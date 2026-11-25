/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ResiduePullbackGlobalSections
import WeilConjectures.Topology.PointModuleEvaluationEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Residue cohomology of a K-flat sheaf representative

Source: Stacks Project, Cohomology, Tags 06YI and 06YJ; Sheaves, Tag 0098.
(blueprint: lem-sc-kflat-stalk-residue-cohomology).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

/-- A K-flat sheaf complex computes residue-fibre cohomology by its stalk tensor.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ; Sheaves, Tag 0098.
(blueprint: lem-sc-kflat-stalk-residue-cohomology).

Proof: The counit in `exists_derivedPullback` is invertible on P since P is K-flat.
It identifies the derived residue pullback of Q(P) with Q of the termwise tensor
pullback of P. Apply derived pullback to eP to replace Q(P) with E. On the spectrum
of the residue field the only opens are the empty open and the whole space.
The sheaf axiom makes sections on the empty open zero, so evaluation on the whole
space preserves kernels and cokernels, hence homology. Its scalar transport along
GammaSpecIso identifies the resulting complex with termwise extension of the stalk
of P along the residue map. To construct this identification, restrict scalar and
module germs to the residue point, send a pure tensor a tensor m to a times the
restricted germ, and use the balanced tensor universal property. The inverse is
provided by the stalk tensor pullback isomorphism of Tag 0098 and the equality of
sections with the stalk on a one-point space. Those maps commute with every module
map, hence with differentials. Apply degree-i homology and compose the resulting
linear equivalences. No boundedness, finite rank or flatness of the residue map is
used. The zero representative gives the zero equivalence, and negative degrees
are handled by the same homology functor. -/
theorem nonempty_kFlat_stalk_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eP : DerivedCategory.Q.obj P ≅ E) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)).homology i)) := by
  classical
  let Y := Spec (X.residueField x)
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let f := X.fromSpecResidueField x
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, _, _, hcompute⟩ :=
    (derivedPullback_spec f)
  have hF' : F = Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  let F := Modules.tensorPullback f
  have : F.Additive := hAdd
  let Fc := F.mapHomologicalComplex (.up ℤ)
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := hcompute P hP
  let c : (derivedPullback f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (Fc.obj P) :=
    (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso A).symm.app P) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso B).app (Fc.obj P)
  let Γ : B ⥤ ModuleCat.{u} (X.residueField x) :=
    SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤) ⋙
    ModuleCat.restrictScalars.{u, u, u} (ΓSpecIso (X.residueField x)).inv.hom
  have : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).IsEquivalence :=
    RingedSpace.globalSectionsFunctor_isEquivalence_of_unique Y.toRingedSpace
  have : PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)) :=
    inferInstanceAs (PreservesFiniteLimits (RingedSpace.globalSectionsFunctor Y.toRingedSpace))
  have : PreservesFiniteColimits
      (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)) :=
    inferInstanceAs (PreservesFiniteColimits (RingedSpace.globalSectionsFunctor Y.toRingedSpace))
  have : PreservesFiniteLimits Γ :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits Γ :=
    comp_preservesFiniteColimits _ _
  have : Γ.PreservesHomology := inferInstance
  let h : derivedFiberCohomology X E i x ≅ Γ.obj ((Fc.obj P).homology i) :=
    Γ.mapIso ((DerivedCategory.homologyFunctor B i).mapIso
      ((derivedPullback f).mapIso eP).symm ≪≫
        (DerivedCategory.homologyFunctor B i).mapIso c ≪≫
          (DerivedCategory.homologyFunctorFactors B i).app (Fc.obj P))
  let hΓ : Γ.obj ((Fc.obj P).homology i) ≅
      ((Γ.mapHomologicalComplex (.up ℤ)).obj (Fc.obj P)).homology i :=
    ((Fc.obj P).sc i).mapHomologyIso Γ |>.symm
  have : (ModuleCat.extendScalars.{u, u, u}
      (IsLocalRing.residue (X.presheaf.stalk x))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (IsLocalRing.residue (X.presheaf.stalk x))).left_adjoint_additive
  have : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms X.toRingedSpace x
  obtain ⟨d⟩ := nonempty_residuePullback_globalSections_iso X x
  let t := (NatIso.mapHomologicalComplex d (.up ℤ)).app P
  let ht := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (X.residueField x))
    (.up ℤ) i).mapIso t
  exact ⟨(h ≪≫ hΓ ≪≫ ht).toLinearEquiv⟩

end AlgebraicGeometry.Scheme
