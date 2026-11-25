/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport

/-!
# Direct-image amplitude for bounded complexes of etale origin

The comparison is the termwise inverse image with canonical constant-ring
realization. Direct images are ordinary uncompleted unbounded right derived functors.

## References

* Stacks Project, Tags 08J5 and 05TC
* Tags 099T and 09A6
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A bound on all etale heart objects controls the direct image of a bounded etale-origin
complex, including the zero-image conclusion when the bound is negative. -/
theorem etaleOrigin_pushforward_amplitude
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (B : Type u) [CommRing B] [Finite B] (N : ℤ)
    (_hN : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
      (q : ℤ), 0 ≤ q → N < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b)
    (L : FiniteCoefficientEtaleDerivedCategory X (ULift.{u + 1, u} B))
    (_hL : ∃ c d : ℤ, c ≤ d ∧ ∀ r : ℤ, r < c ∨ d < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj L))
    (_hC : ∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((finiteCoefficientIntrinsicDerivedComparison X B).obj L))) :
    (∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj L)) ∧
    (∀ i : ℤ, i < a ∨ b + N < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((Scheme.proEtaleConstantDerivedDirectImage f B).obj
          ((finiteCoefficientIntrinsicDerivedComparison X B).obj L)))) ∧
    (N < 0 →
      IsZero
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctor.obj L) ∧
      IsZero ((Scheme.proEtaleConstantDerivedDirectImage f B).obj
        ((finiteCoefficientIntrinsicDerivedComparison X B).obj L))) := by
  let A := ULift.{u + 1, u} B
  let ν := fun T : Scheme.{u} ↦ comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicRealization T B
  let Cp := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicDerivedComparison T B
  let re := Etale.lowerStar (ModuleCat.{u + 1} A) f
  let rp := lowerStar (ModuleCat.{u + 1} A) f
  let F := re.rightDerivedFunctor
  let : (R X).IsEquivalence := (finiteCoefficientIntrinsicRealization_exact X B).1
  have : (finiteCoefficientIntrinsicComparison X B).Faithful :=
    inferInstanceAs ((ν X) ⋙ R X).Faithful
  have hL (r : ℤ) (hr : r < a ∨ b < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj L) :=
    (finiteCoefficientIntrinsicComparison X B)
      |>.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj (_hC r hr)
  have hPlus : DerivedCategory.TStructure.t.plus L :=
    ⟨a, (DerivedCategory.isGE_iff L a).mpr (fun i hi ↦ hL i (Or.inl hi))⟩
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨L, hPlus⟩
  let := isIso_comparisonDirectImagePlus A f
  -- First compare the fixed-scalar direct images through their bounded-below models.
  let efix : (ν Y).mapDerivedCategory.obj (F.obj L) ≅
      rp.rightDerivedFunctor.obj ((ν X).mapDerivedCategory.obj L) :=
    (ν Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app J).symm ≪≫
      ((ν Y).mapDerivedCategoryPlusCompatibility.app
        (re.rightDerivedFunctorPlus.obj J)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).app J) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((ν X).mapDerivedCategoryPlus.obj J)) ≪≫
      rp.rightDerivedFunctor.mapIso ((ν X).mapDerivedCategoryPlusCompatibility.app J)
  let eC (T : Scheme.{u}) (K : FiniteCoefficientEtaleDerivedCategory T A) :
      (Cp T).obj K ≅ (R T).mapDerivedCategory.obj ((ν T).mapDerivedCategory.obj K) :=
    (Functor.mapDerivedCategoryCompIso (ν T) (R T)).symm.app K
  let direct := Scheme.proEtaleConstantDerivedDirectImage f B
  -- Then change to the canonical intrinsic constant-ring presentation.
  let e : (Cp Y).obj (F.obj L) ≅ direct.obj ((Cp X).obj L) :=
    eC Y (F.obj L) ≪≫ (R Y).mapDerivedCategory.mapIso efix ≪≫
      (Scheme.sfIntrinsicDerivedDirectImageComparison f B).symm.app
        ((ν X).mapDerivedCategory.obj L) ≪≫
      direct.mapIso (eC X L).symm
  have hneg (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (i : ℤ) (hi : i < 0) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (F.obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
    have := re.isGE_rightDerivedFunctor_obj_singleFunctor M
    exact (DerivedCategory.isGE_iff _ 0).mp this i hi
  have hamp (c d : ℤ) (hcd : c ≤ d)
      (hh : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (i : ℤ),
        i < c ∨ d < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)))) :
      ∀ i : ℤ, i < a + c ∨ b + d < i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (F.obj L)) :=
    DerivedCategory.bounded_heart_amplitude _ _ F (fun _ ↦ True)
      (fun _ _ _ _ ↦ trivial) trivial c d hcd
      (fun M _ i hi ↦ hh M i hi) a b _hab L hL (fun _ ↦ trivial)
  have hzero (hN : N < 0) : IsZero (F.obj L) := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    -- Every heart image is zero, so any singleton heart interval is available.
    exact hamp (i - a + 1) (i - a + 1) le_rfl (fun M q _ ↦ by
      by_cases hq : q < 0
      · exact hneg M q hq
      · exact _hN M q (by omega) (by omega)) i (Or.inl (by omega))
  refine ⟨hL, ?_, ?_⟩
  · intro i hi
    by_cases hN : N < 0
    · exact (DerivedCategory.homologyFunctor _ i).map_isZero
        (((finiteCoefficientIntrinsicComparison Y B).mapDerivedCategory.map_isZero
          (hzero hN)).of_iso e.symm)
    · have hi' : i < a + 0 ∨ b + N < i := by simpa using hi
      have hv := hamp 0 N (by omega) (fun M q hq ↦ by
        rcases hq with hq | hq
        · exact hneg M q hq
        · exact _hN M q (by omega) hq) i hi'
      exact ((finiteCoefficientIntrinsicComparison Y B)
        |>.isZero_homologyFunctor_mapDerivedCategory_obj hv).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro hN
    exact ⟨hzero hN,
      ((finiteCoefficientIntrinsicComparison Y B).mapDerivedCategory.map_isZero
        (hzero hN)).of_iso e.symm⟩

end AlgebraicGeometry.ProEtale
