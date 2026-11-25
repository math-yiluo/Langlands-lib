/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The specified integral comparison at an arbitrary derived object

This is the recorded comparison transported through a representative of a derived
object and a flat-term K-flat resolution. No new naturality assertion is imposed.
The finite comparisons and all coefficient maps are publicly retained.

## References

* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

/-- Evaluate part (b) on the chosen representative and its chosen K-flat resolution,
then transport its two endpoints by the representative isomorphism. The resolution
is used only through the localized specified comparison. -/
def inverseImagePullbackComparisonDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y)) :
    (inverseImageIntegralDerived l E g).obj K ⟶
      (integralDerivedPullback l E g).obj K := by
  let M := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E Y) M
  let P := h.choose
  let q := h.choose_spec.choose
  let hq := h.choose_spec.choose_spec
  letI : QuasiIso q := hq.2.2.1
  exact (inverseImageIntegralDerived l E g).map e.inv ≫
    inverseImagePullbackComparison l E g hX hY M
      ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hq.2.1 i)⟩ q ≫
      (integralDerivedPullback l E g).map e.hom

end AlgebraicGeometry.ProEtale
