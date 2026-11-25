/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.NagataAffineProjScalarExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
/-! # Normalized scalar-extension twist sections

The two original definitions of the scalar-extension twist comparison, separated from
its existence proof so that the chart construction and fraction calculus can be imported
independently.

## References

* Stacks Project, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- Apply a twist comparison to the actual pullback section `1 ⊗ s`. -/
noncomputable def scalarExtensionTwistSection
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U)) :
    Γ(twist ℬ j, r ⁻¹ᵁ U) :=
  (θ j).hom.app (r ⁻¹ᵁ U) (tensorPullbackSection r (twist 𝒜 j) U s)

/-- The normalized fraction rule for the scalar-extension comparison. A section `s=a/b`
is specified by `b*s=a` where `b` is invertible. For `b=f^m`, this is exactly
`(a/f^m) ⊗ c ↦ c*ψ(a)/ψ(f)^m`. All opens are allowed, so the rule includes further
standard-open restrictions. -/
def IsScalarExtensionTwistComparison
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j) : Prop :=
  ∀ (j : ℤ) (i k : ℕ) (a : A) (b : A), a ∈ 𝒜 i → b ∈ 𝒜 k →
    (i : ℤ) = (k : ℤ) + j →
    ∀ (U : (Proj 𝒜).Opens), U ≤ basicOpen 𝒜 b →
    ∀ (s : Γ(twist 𝒜 j, U)),
      (∀ y : U, (s.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk b 1 = Localization.mk a 1) →
    ∀ (c : Γ(Proj ℬ, r ⁻¹ᵁ U)) (x : r ⁻¹ᵁ U),
      ((c • scalarExtensionTwistSection r θ j U s).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk (ψ b) 1 =
        (c.1 x).val * Localization.mk (ψ a) 1

end AlgebraicGeometry.Proj
