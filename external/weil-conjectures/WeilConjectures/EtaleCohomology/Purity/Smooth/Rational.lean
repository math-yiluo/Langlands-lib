/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Adic

/-!
# Smooth purity with coefficients in `E`

At the stage `Λ = E`, a finite extension of `ℚ_ℓ`, an object is presented by a lattice: an
object of the integral stage `D_comp(X, 𝒪_E)` (`DerivedCategoryDerivedCompleteIntegral`),
viewed in its rationalization `D_comp(X, E)` (`DerivedCategoryDerivedCompleteRational`) through
the localization functor `fromIntegral`, the exact functor `- ⊗ᴸ_{𝒪_E} E`. The `E`-purity
isomorphism is the image of the adic purity isomorphism of
`AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel` under this functor.

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_fromIntegral_realization_twistShiftPullbackLevel`
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_rational
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]
  [∀ n : ℕ, Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
  [∀ n : ℕ, HasTateTwist (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
  {X Y : Scheme.{u}} (d : ℤ) (f : X ⟶ Y) [HasCompactification f]

/-- Rational and `ℚ̄_ℓ` purity (`E`-stage packaging only)

Let `K = (K_n)_n` be a normalized system over `𝒪_E` on `Y`, `S`, `T` normalized systems on `X`
with levels identified with `Lf^* K_n(d)[2d]` and `Rf^! K_n`, and `γ_n` isomorphisms between
these levels forming a morphism of normalized systems (`hγ`). Then any homotopy limits of `S`
and `T` are derived complete, so they are objects of `D_comp(X, 𝒪_E)`; the isomorphism `e`
between them of `AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel`
reduces to `γ_n` at every level, and its image under the exact functor `- ⊗ᴸ_{𝒪_E} E`
(`DerivedCategoryDerivedCompleteRational.fromIntegral`) is an isomorphism in `D_comp(X, E)`.

This is the `E`-stage packaging of the realized isomorphism, not the `E`-part of the
blueprint statement: `hγ` is assumed, the objects are arbitrary homotopy limits rather than
`Lf^* K_E(d)[2d]` and `Rf^! K_E`, and the `IsIso` conclusion follows formally from `e` being an
isomorphism. -/
theorem exists_iso_fromIntegral_realization_twistShiftPullbackLevel
    (K : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) Y)
    (S T : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) X)
    (eS : ∀ n : ℕ, S.obj n ≅ twistShiftPullbackLevel d f K n)
    (eT : ∀ n : ℕ, T.obj n ≅ upperShriekLevel f K n)
    (γ : ∀ n : ℕ, twistShiftPullbackLevel d f K n ≅ upperShriekLevel f K n)
    (hγ : ∀ n : ℕ, S.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor _ n) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom =
      (eS (n + 1) ≪≫ γ (n + 1) ≪≫ (eT (n + 1)).symm).hom ≫ T.map n)
    {cS : Cone S.restrict} (hcS : Pretriangulated.IsHomotopyLimit cS)
    {cT : Cone T.restrict} (hcT : Pretriangulated.IsHomotopyLimit cT) :
    ∃ (hS : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cS.pt)
      (hT : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cT.pt)
      (e : cS.pt ≅ cT.pt),
      (∀ n : ℕ, e.hom ≫ cT.π.app (Opposite.op n) =
        cS.π.app (Opposite.op n) ≫
          (derivedRestrictScalars (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ (n + 1)))
            X).map (eS n ≪≫ γ n ≪≫ (eT n).symm).hom) ∧
      IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).map
        (X := ⟨cS.pt, hS⟩) (Y := ⟨cT.pt, hT⟩) (ObjectProperty.homMk e.hom)) := by
  obtain ⟨ϖ, hϖ, hI⟩ := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨e, he⟩ := exists_iso_realization_twistShiftPullbackLevel d f K S T eS eT γ hγ hcS hcT
  refine ⟨S.derivedComplete_of_isHomotopyLimit hϖ hI hcS,
    T.derivedComplete_of_isHomotopyLimit hϖ hI hcT, e, he, ?_⟩
  have : IsIso (ObjectProperty.homMk (P := DerivedCategory.derivedCompleteIntegral
      X.smallEtaleTopology l E) (X := ⟨cS.pt, S.derivedComplete_of_isHomotopyLimit hϖ hI hcS⟩)
      (Y := ⟨cT.pt, T.derivedComplete_of_isHomotopyLimit hϖ hI hcT⟩) e.hom) :=
    ⟨ObjectProperty.homMk e.inv, by ext; exact e.hom_inv_id, by ext; exact e.inv_hom_id⟩
  exact Functor.map_isIso _ _

end Etale

end AlgebraicGeometry
