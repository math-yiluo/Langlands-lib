/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PrimeCurveGeometricStalkFinite
import WeilConjectures.AlgebraicGeometry.Module.ModuleSpecializationAbelianIso
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteStalkSpecializationCriterion
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothProperPrimeSpecialization
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-!
# Prime coefficients in proper smooth curve families

## References

* Stacks Project, Tag 0GKV, the Noetherian case
* Stacks Project, Tag 0GKV, for a prime invertible on the base, the case Tag 0GL0 uses

## Implementation details

`GeometricallyConnected f` includes nonemptiness of the fibres. Dimension is measured on
residue-field fibres, which is the geometric fibre condition since field extension preserves
dimension. The coefficients `ULift (ZMod ell)` place the prime field in the coefficient universe.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def higherDirectImage_forget_iso
    (R : Type (u + 1)) [CommRing R] {X S : Scheme.{u}}
    (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ) :
    (moduleAbelianForget R S).obj (higherDirectImage R f q F) ≅
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((moduleAbelianForget R X).obj F))) := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  exact ((moduleAbelianForget R S).mapDerivedCategoryPlusHomologyFunctorIso
      (q : ℤ)).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((moduleAbelianDerivedLowerStarIso R f).app K ≪≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
          (((moduleAbelianForget R X).mapDerivedCategoryPlusSingleFunctor 0).app F))

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem prime_invertible_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime]
    (hunit : ∀ s : S, IsUnit (p : S.presheaf.stalk s)) (q : ℕ) :
    Scheme.IsConstructibleSheaf (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
      ((constantSheaf C.smallEtaleTopology _).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) := by
  have : IsNoetherian S := ⟨⟩
  let R := ULift.{u + 1} (ZMod p)
  let M := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R R)
  let G := higherDirectImage R f q M
  have : Scheme.IsLocallyConstantSheaf M :=
    (Sheaf.isConstant_of_iso _ (Iso.refl M)).isLocallyConstantSheaf
  obtain ⟨𝒰, h𝒰⟩ :=
    Scheme.finiteLocallyConstant_of_finite_stalks_of_bijective_specialization G
      (fun Ω _ _ s ↦ prime_constant_stalk_finite f hdim p q Ω s) (by
        intro Ω Ξ _ _ _ _ s t
        exact bijective_moduleSpecialization_of_abelianIso G _
          (higherDirectImage_forget_iso R f M q) s t
          (isIso_strictLocalSpecialization_smooth_proper_prime f p hunit M q s t))
  let d : Scheme.LocallyConstantDatum G :=
    ⟨𝒰, fun i ↦ by
      obtain ⟨E, -, ⟨e⟩⟩ := h𝒰 i
      exact Sheaf.isConstant_of_iso _ e⟩
  have : Scheme.IsFiniteLocallyConstantSheaf G :=
    (Scheme.finite_locally_constant_module_values_iff G).1.mp ⟨d, h𝒰⟩
  exact ⟨Scheme.Stratification.trivial S, fun _ ↦
    Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 S) G⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In a proper smooth family with nonempty geometrically connected one-dimensional
fibres over a Noetherian base on which the prime `ell` is invertible, every nonnegative
higher direct image of the constant prime-field module sheaf is constructible. -/
theorem properSmoothCurves_prime_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (ell : ℕ) [Fact ell.Prime] (hunit : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (q : ℕ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ell)) (ULift.{u + 1} (ZMod ell))))))) := by
  let R := ULift.{u + 1} (ZMod ell)
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R R)
  change Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage R f q F)
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (prime_invertible_constructible f h_dim ell hunit q)

end AlgebraicGeometry.Etale
