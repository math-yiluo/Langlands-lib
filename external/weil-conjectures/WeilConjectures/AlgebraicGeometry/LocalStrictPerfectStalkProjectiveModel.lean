/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Module.Projective
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Bounded finite-projective models of locally strictly perfect stalks

Source: Stacks Project, Tags 08C4, 08CM, 01AG and 00A0.
(blueprint: lem-sc-local-strict-perfect-stalk-projective-model).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Finite free sheaves have finitely generated open stalks.
Source: Stacks Project, Tags 08C4 and 01AG.
Proof: identify the unit stalk with the regular module, preserve its finite
coproduct, reindex to `Fin m`, and identify the coproduct with a finite product.
Finite products of finite modules are finite, including the empty product. -/
private theorem openStalk_free_finite
    (X : Scheme.{u}) (V : X.Opens) (y : V.toScheme) (m : ℕ) :
    Module.Finite (X.presheaf.stalk (V.ι y))
      ((openModuleStalkFunctor X V y).obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))) := by
  let S := openModuleStalkFunctor X V y
  let R := ModuleCat.restrictScalars (V.ι.stalkMap y).hom
  let T := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace y ⋙ R
  obtain ⟨e, _, _⟩ := Scheme.ideal_module_product_stalk
    (𝟙 (SheafOfModules.unit V.toScheme.ringCatSheaf))
    (SheafOfModules.unit V.toScheme.ringCatSheaf) y
  let er := (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
  let eu : S.obj (SheafOfModules.unit ((moduleRings X.toRingedSpace).over V)) ≅
      ModuleCat.of (X.presheaf.stalk (V.ι y)) (X.presheaf.stalk (V.ι y)) :=
    T.mapIso (Scheme.Modules.overEquivFunctorObjUnitIso V).symm ≪≫
      R.mapIso e ≪≫ ModuleCat.restrictScalarsIsoOfEquiv er
  let f := fun _ : ULift.{u} (Fin m) ↦
    S.obj (SheafOfModules.unit ((moduleRings X.toRingedSpace).over V))
  let c := PreservesCoproduct.iso S (fun _ : ULift.{u} (Fin m) ↦
    SheafOfModules.unit ((moduleRings X.toRingedSpace).over V))
  let d := (Sigma.reindex Equiv.ulift.symm f).symm ≪≫
    (biproduct.isoCoproduct (f ∘ Equiv.ulift.symm)).symm ≪≫
      ModuleCat.biproductIsoPi (f ∘ Equiv.ulift.symm)
  have : Module.Finite (X.presheaf.stalk (V.ι y))
      (S.obj (SheafOfModules.unit ((moduleRings X.toRingedSpace).over V))) :=
    Module.Finite.equiv eu.symm.toLinearEquiv
  have : ∀ i : Fin m, Module.Finite (X.presheaf.stalk (V.ι y))
      ((f ∘ Equiv.ulift.symm) i) := fun _ ↦ by
        dsimp only [f, Function.comp_apply]
        infer_instance
  exact Module.Finite.equiv (c ≪≫ d).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- A local strictly perfect representative supplies a bounded finite-projective
representative of the termwise stalk of any complex representing the same derived object.

Source: Stacks Project, Cohomology of Sheaves, Tags 08C4 and 08CM;
Modules, Tag 01AG; Sheaves, Tag 00A0 (restriction to an open neighbourhood).
(blueprint: lem-sc-local-strict-perfect-stalk-projective-model).

Proof:
1. Choose V, P and its derived comparison from hlocal. The category of opens over V
   is equivalent to the open-subspace site of V. At x, neighbourhoods contained in V
   are cofinal among all neighbourhoods. Germ restriction therefore identifies both
   the stalk ring and the stalk modules of a restricted sheaf with their stalks on X.
   This identification commutes with all sheaf morphisms, hence with differentials.
2. Apply the stalk functor termwise to P to obtain L over O_X,x. Stalks preserve zero
   objects, so the lower and upper bounds of P give the same bounds for L. Stalks
   commute with finite coproducts, and the germ of the unit module is the stalk ring.
   Consequently the stalk of the finite free sheaf on Fin m is the free module of
   rank m. Apply stalks to each retraction in IsStrictlyPerfect. Its composite is
   the identity by functoriality. Thus every L.X j is a retract of a finite free
   module: it is finite and projective, without using local-ring freeness yet.
3. Stalks are exact by Tag 01AG, so preserve quasi-isomorphisms. Their termwise
   functor descends to the derived localization. Apply it to the local comparison,
   and compose with the cofinal germ comparison and eG. This gives Q(L) isomorphic
   to Q(G_x). This last argument uses the universal property of localization; the
   morphism universes v and w can differ, since it only transports an isomorphism
   between the represented objects, not an equivalence of the entire categories.
No residue fibre, finiteness of its cohomology, or minimal model is asserted here.
For a zero representative all terms and their retracts are zero. -/
theorem exists_localStrictPerfect_stalk_projective_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    : ∃ (L : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
      (a b : ℤ),
      (∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j)) ∧
      (∀ j : ℤ, Module.Finite (X.presheaf.stalk x) (L.X j) ∧
        Module.Projective (X.presheaf.stalk x) (L.X j)) ∧
      Nonempty (DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) := by
  obtain ⟨V, hx, P, hP, ⟨eP⟩⟩ := hlocal
  let : HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk (V.ι ⟨x, hx⟩))) :=
    inferInstanceAs (HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x)))
  let S := openModuleStalkFunctor X V ⟨x, hx⟩
  let L := (S.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨a, b, hab⟩ := hP.1
  refine ⟨L, a, b, (fun j hj ↦ S.map_isZero (hab j hj)), ?_, ?_⟩
  · intro j
    obtain ⟨m, ι, π, hιπ⟩ := hP.2 j
    let F := S.obj (SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))
    have hret : Retract (L.X j) F :=
      ⟨S.map ι, S.map π, by
        change S.map ι ≫ S.map π = 𝟙 (S.obj (P.X j))
        rw [← S.map_comp, hιπ, S.map_id]⟩
    have : Projective F := openModuleStalk_free_projective X V ⟨x, hx⟩ m
    have : Projective (L.X j) := hret.projective
    have : Module.Finite (X.presheaf.stalk (V.ι ⟨x, hx⟩)) F := openStalk_free_finite X V ⟨x, hx⟩ m
    refine ⟨Module.Finite.of_surjective (S.map π).hom ?_, inferInstance⟩
    intro z
    refine ⟨(S.map ι) z, ?_⟩
    have he : S.map ι ≫ S.map π = 𝟙 (S.obj (P.X j)) := by
      rw [← S.map_comp, hιπ, S.map_id]
    exact ConcreteCategory.congr_hom he z
  · let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
    let Gv := (R.mapHomologicalComplex (.up ℤ)).obj G
    let d : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj
        ((S.mapHomologicalComplex (.up ℤ)).obj Gv) :=
      (S.mapDerivedCategoryFactors.app P).symm ≪≫
        (S.mapDerivedCategory.mapIso eP).symm ≪≫
        (S.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso eG)).symm ≪≫
        S.mapDerivedCategory.mapIso (R.mapDerivedCategoryFactors.app G) ≪≫
        S.mapDerivedCategoryFactors.app Gv
    let ρ := (V.ι.stalkMap ⟨x, hx⟩).hom
    let A := ModuleCat.restrictScalars ρ
    let H := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace ⟨x, hx⟩
    let C := ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
      (.up ℤ)).obj G
    have : (Scheme.Modules.restrictFunctor V.ι).Additive :=
      Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
    obtain ⟨c⟩ := nonempty_restriction_stalk_extension_iso V.ι ⟨x, hx⟩ G
    let eρ := RingEquiv.ofBijective ρ
      (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap ⟨x, hx⟩))
    have : A.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
    let ev := (NatIso.mapHomologicalComplex (Scheme.Modules.overFunctorEquiv V)
      (.up ℤ)).app G
    let q : (S.mapHomologicalComplex (.up ℤ)).obj Gv ≅ C :=
      (A.mapHomologicalComplex (.up ℤ)).mapIso
        ((H.mapHomologicalComplex (.up ℤ)).mapIso ev) ≪≫
      ((A.mapHomologicalComplex (.up ℤ)).mapIso c).symm ≪≫
      ((NatIso.mapHomologicalComplex
        (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) (.up ℤ)).app C).symm
    exact ⟨d ≪≫ DerivedCategory.Q.mapIso q⟩

end AlgebraicGeometry.Scheme
