/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk of a closed pushforward of the structure module at the generic point
is isomorphic to any compatible residue-field line.
Source: Stacks Project, Tag 01YH, rank calculation following Tag 01YE.
(blueprint: new-rank-one-generic-ideal-inclusion-aux)

Proof: closed-pushforward stalk comparison identifies the source with the regular
module over the generic local ring of W. Integrality makes that ring a field.
The closed-immersion stalk homomorphism is a surjective local homomorphism onto
this field, so its kernel is the ambient maximal ideal. Factoring through that
ideal identifies the field with the ambient residue field. These identifications
respect the ambient stalk-ring action. A vector space of finrank one is finite
and has a one-element basis, hence is linearly isomorphic to its scalar field.
Use the scalar compatibility in hGrank to regard this equivalence as linear over
the ambient stalk ring, and compose with the source identifications. No ideal
lattice or global sheaf morphism is constructed by this statement. -/
theorem rank_one_generic_structure_stalk_iso {X W : Scheme.{u}}
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules)
    (hGrank : ∃ _inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G) = 1) :
    Nonempty ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).obj ((pushforward i).obj
        (SheafOfModules.unit W.ringCatSheaf)) ≅
      (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G) := by
  classical
  obtain ⟨inst, hcompat, hrank⟩ := hGrank
  let : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G) := inst
  obtain ⟨v⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrank
  let R := X.presheaf.stalk (i.base (genericPoint W))
  let K := W.presheaf.stalk (genericPoint W)
  let q : X.residueField (i.base (genericPoint W)) →+* K :=
    IsLocalRing.ResidueField.lift (i.stalkMap (genericPoint W)).hom
  have hq : Function.Bijective q := by
    refine ⟨q.injective, ?_⟩
    intro k
    obtain ⟨r, hr⟩ := i.stalkMap_surjective (genericPoint W) k
    exact ⟨(X.residue (i.base (genericPoint W))).hom r, hr⟩
  let t := RingEquiv.ofBijective q hq
  obtain ⟨eW, heW, _⟩ := AlgebraicGeometry.Scheme.ideal_module_product_stalk
    (𝟙 (SheafOfModules.unit W.ringCatSheaf))
    (SheafOfModules.unit W.ringCatSheaf) (genericPoint W)
  let c := TopCat.Presheaf.stalkPushforward Ab i.base
    (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W)
  have hc := (closedImmersion_pushforward_stalks i i.isClosedEmbedding
    (SheafOfModules.unit W.ringCatSheaf)).2.1 (genericPoint W)
  let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint W))).obj ((pushforward i).obj
        (SheafOfModules.unit W.ringCatSheaf)) →ₗ[R]
      (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G :=
    { toFun := fun m ↦ v (t.symm (eW.hom (c m)))
      map_add' := by intro a b; simp
      map_smul' := by
        intro r m
        change v (t.symm (eW.hom (c (r • m)))) = r • v (t.symm (eW.hom (c m)))
        rw [hc.2.2, eW.hom.hom.map_smul]
        change v (t.symm ((i.stalkMap (genericPoint W)).hom r * eW.hom (c m))) = _
        rw [map_mul]
        have ht : t.symm ((i.stalkMap (genericPoint W)).hom r) =
            (X.residue (i.base (genericPoint W))).hom r := by
          apply t.injective
          simp only [RingEquiv.apply_symm_apply]
          rfl
        rw [ht]
        change v ((X.residue (i.base (genericPoint W))).hom r •
          t.symm (eW.hom (c m))) = _
        rw [v.map_smul, hcompat] }
  have hf : Function.Bijective f := v.bijective.comp
    (t.symm.bijective.comp ((ConcreteCategory.bijective_of_isIso eW.hom).comp hc.1))
  exact ⟨(LinearEquiv.ofBijective f hf).toModuleIso⟩

end AlgebraicGeometry.Scheme.Modules
