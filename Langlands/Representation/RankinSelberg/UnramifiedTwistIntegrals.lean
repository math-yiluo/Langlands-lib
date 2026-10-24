import Langlands.Representation.RankinSelberg.TwistInvariance

/-!
# Spectral shifts of JPSS integrands and their value sets

The pointwise identities transport actual convergence and integrals. The value-set
lemmas isolate the rational-continuation substitution law as an explicit input.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory Polynomial

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

omit [TopologicalSpace F] in
/-- Complex powers of the nonzero determinant norm multiply under addition. -/
theorem determinantWeight_add {n : ℕ} (g : Langlands.GeneralLinear n F) (s u : ℂ) :
    determinantWeight abv g (s + u) =
      determinantWeight abv g s * determinantWeight abv g u := by
  apply Complex.cpow_add
  exact_mod_cast (abv.ne_zero (determinant g).ne_zero)

/-- Multiplying the Whittaker product by the spectral weight shifts the equal-rank
integrand, on the actual quotient. -/
theorem equalRankIntegrand_shift_of_product {n : ℕ}
    {W₁ W₂ : WhittakerFunctions ψ n} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (u : ℂ)
    (h : ∀ g, W₁.val g * W₁'.val g =
      determinantWeight abv g u * (W₂.val g * W₂'.val g))
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegrand ψ abv W₁ W₁' Φ s =
      equalRankIntegrand ψ abv W₂ W₂' Φ (s + u) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk, h g, determinantWeight_add]
    ring

/-- The same pointwise transport holds for every unequal-rank block. -/
theorem unequalRankIntegrand_shift_of_product {n : ℕ} (j k : ℕ)
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))}
    {W₁' W₂' : InverseWhittakerFunctions ψ n} (u : ℂ)
    (h : ∀ g x, W₁.val (unequalRankMatrix j k g x) * W₁'.val g =
      determinantWeight abv g u * (W₂.val (unequalRankMatrix j k g x) * W₂'.val g))
    (s : ℂ) :
    unequalRankIntegrand ψ abv j k W₁ W₁' s =
      unequalRankIntegrand ψ abv j k W₂ W₂' (s + u) := by
  funext x q
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, h g x]
    rw [show s + u - ((j + k + 1 : ℕ) : ℂ) / 2 =
      (s - ((j + k + 1 : ℕ) : ℂ) / 2) + u by ring, determinantWeight_add]
    ring

omit [TopologicalSpace F] in
/-- A character with the prescribed absolute-value formula is the determinant
weight on each general linear group. -/
theorem unramifiedCharacter_determinant (χ : Fˣ →* ℂˣ) (u : ℂ)
    (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u)
    {n : ℕ} (g : Langlands.GeneralLinear n F) :
    (χ (determinant g) : ℂ) = determinantWeight abv g u :=
  hχ (determinant g)

section WhittakerImages

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (χ : Fˣ →* ℂˣ) {n : ℕ}

/-- Character multiplication on the actual Whittaker function space. -/
def whittakerDeterminantTwist (m : ℕ) :
    WhittakerFunctions ψ m ≃ₗ[ℂ] WhittakerFunctions ψ m :=
  twistFunctionEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ)

/-- Character multiplication on the inverse-character Whittaker space. -/
def inverseWhittakerDeterminantTwist (m : ℕ) :
    InverseWhittakerFunctions ψ m ≃ₗ[ℂ] InverseWhittakerFunctions ψ m :=
  twistFunctionEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ)

/-- The actual Whittaker set of a twist is the image under character multiplication. -/
theorem whittakerSet_twist_image
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    whittakerSet ψ n (Langlands.twist (χ.comp determinant) π) =
      (whittakerDeterminantTwist ψ χ n) '' whittakerSet ψ n π := by
  ext W
  rw [mem_whittakerSet_twist_iff]
  constructor
  · rintro ⟨W₀, hW₀, h⟩
    exact ⟨W₀, hW₀, Subtype.ext (funext fun g => (h g).symm)⟩
  · rintro ⟨W₀, hW₀, rfl⟩
    exact ⟨W₀, hW₀, fun _ => rfl⟩

/-- The inverse-character Whittaker set has the same image description. -/
theorem inverseWhittakerSet_twist_image
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    inverseWhittakerSet ψ n (Langlands.twist (χ.comp determinant) π) =
      (inverseWhittakerDeterminantTwist ψ χ n) '' inverseWhittakerSet ψ n π := by
  ext W
  rw [mem_inverseWhittakerSet_twist_iff]
  constructor
  · rintro ⟨W₀, hW₀, h⟩
    exact ⟨W₀, hW₀, Subtype.ext (funext fun g => (h g).symm)⟩
  · rintro ⟨W₀, hW₀, rfl⟩
    exact ⟨W₀, hW₀, fun _ => rfl⟩

end WhittakerImages

section ValueTransport

variable (q : ℕ) (u : ℂ) (e : RationalFunctions ≃ RationalFunctions)
variable (hshift : ∀ (f : ℂ → ℂ) (R : RationalFunctions),
  HasRationalContinuation q (fun s => f (s + u)) (e R) ↔ HasRationalContinuation q f R)

include hshift

/-- Integrand shifts transport equal-rank value sets through any rational
substitution satisfying the stated continuation law. -/
theorem equalRankValuesOf_image_of_shift {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (T : WhittakerFunctions ψ n → WhittakerFunctions ψ n)
    (T' : InverseWhittakerFunctions ψ n → InverseWhittakerFunctions ψ n)
    (hI : ∀ W W' Φ s, equalRankIntegrand ψ abv (T W) (T' W') Φ s =
      equalRankIntegrand ψ abv W W' Φ (s + u))
    (S : Set (WhittakerFunctions ψ n)) (S' : Set (InverseWhittakerFunctions ψ n)) :
    equalRankValuesOf q ψ abv μ (T '' S) (T' '' S') =
      e '' equalRankValuesOf q ψ abv μ S S' := by
  have hfun : ∀ W W' Φ, equalRankIntegral ψ abv μ (T W) (T' W') Φ =
      fun s => equalRankIntegral ψ abv μ W W' Φ (s + u) := by
    intro W W' Φ
    funext s
    simp only [equalRankIntegral, hI]
  ext R
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, _, ⟨W', hW', rfl⟩, Φ, ⟨a, ha⟩, hR⟩
    refine ⟨e.symm R, ⟨W, hW, W', hW', Φ, ⟨a + u.re, ?_⟩, ?_⟩,
      e.apply_symm_apply R⟩
    · intro s hs
      have ht := ha (s - u) (by simp only [Complex.sub_re]; linarith)
      simpa only [EqualRankConverges, hI, sub_add_cancel] using ht
    · apply (hshift _ _).mp
      simpa only [e.apply_symm_apply, hfun] using hR
  · rintro ⟨R, ⟨W, hW, W', hW', Φ, ⟨a, ha⟩, hR⟩, rfl⟩
    refine ⟨T W, ⟨W, hW, rfl⟩, T' W', ⟨W', hW', rfl⟩, Φ,
      ⟨a - u.re, ?_⟩, ?_⟩
    · intro s hs
      have ht := ha (s + u) (by simp only [Complex.add_re]; linarith)
      simpa only [EqualRankConverges, hI] using ht
    · rw [hfun]
      exact (hshift _ _).mpr hR

/-- The same transport treats every rectangular block, both product-measure
absolute convergence and the iterated scalar integral. -/
theorem unequalRankValuesOf_image_of_shift {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (T : WhittakerFunctions ψ (n + (j + k + 1)) →
      WhittakerFunctions ψ (n + (j + k + 1)))
    (T' : InverseWhittakerFunctions ψ n → InverseWhittakerFunctions ψ n)
    (hI : ∀ W W' s, unequalRankIntegrand ψ abv j k (T W) (T' W') s =
      unequalRankIntegrand ψ abv j k W W' (s + u))
    (S : Set (WhittakerFunctions ψ (n + (j + k + 1))))
    (S' : Set (InverseWhittakerFunctions ψ n)) :
    unequalRankValuesOf q ψ abv j k μ ν (T '' S) (T' '' S') =
      e '' unequalRankValuesOf q ψ abv j k μ ν S S' := by
  have hfun : ∀ W W', unequalRankIntegral ψ abv j k μ ν (T W) (T' W') =
      fun s => unequalRankIntegral ψ abv j k μ ν W W' (s + u) := by
    intro W W'
    funext s
    simp only [unequalRankIntegral, hI]
  ext R
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, _, ⟨W', hW', rfl⟩, ⟨a, ha⟩, hR⟩
    refine ⟨e.symm R, ⟨W, hW, W', hW', ⟨a + u.re, ?_⟩, ?_⟩,
      e.apply_symm_apply R⟩
    · intro s hs
      have ht := ha (s - u) (by simp only [Complex.sub_re]; linarith)
      simpa only [UnequalRankConverges, hI, sub_add_cancel] using ht
    · apply (hshift _ _).mp
      simpa only [e.apply_symm_apply, hfun] using hR
  · rintro ⟨R, ⟨W, hW, W', hW', ⟨a, ha⟩, hR⟩, rfl⟩
    refine ⟨T W, ⟨W, hW, rfl⟩, T' W', ⟨W', hW', rfl⟩,
      ⟨a - u.re, ?_⟩, ?_⟩
    · intro s hs
      have ht := ha (s + u) (by simp only [Complex.add_re]; linarith)
      simpa only [UnequalRankConverges, hI] using ht
    · rw [hfun]
      exact (hshift _ _).mpr hR

section RepresentationValues

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (χ : Fˣ →* ℂˣ)
variable (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u)
include hχ

/-- Twisting the first representation shifts the equal-rank zeta values. -/
theorem equalRankZetaValues_unramified_left {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    equalRankZetaValues q ψ abv μ (Langlands.twist (χ.comp determinant) π) σ =
      e '' equalRankZetaValues q ψ abv μ π σ := by
  unfold equalRankZetaValues
  rw [whittakerSet_twist_image]
  conv_lhs => rw [← Set.image_id (inverseWhittakerSet ψ n σ)]
  apply equalRankValuesOf_image_of_shift ψ abv q u e hshift
  intro W W' Φ s
  apply equalRankIntegrand_shift_of_product ψ abv u
  intro g
  change ((χ (determinant g) : ℂ) * W.val g) * W'.val g = _
  rw [unramifiedCharacter_determinant abv χ u hχ, mul_assoc]

/-- Twisting the second representation shifts the equal-rank zeta values. -/
theorem equalRankZetaValues_unramified_right {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    equalRankZetaValues q ψ abv μ π (Langlands.twist (χ.comp determinant) σ) =
      e '' equalRankZetaValues q ψ abv μ π σ := by
  unfold equalRankZetaValues
  rw [inverseWhittakerSet_twist_image]
  conv_lhs => rw [← Set.image_id (whittakerSet ψ n π)]
  apply equalRankValuesOf_image_of_shift ψ abv q u e hshift
  intro W W' Φ s
  apply equalRankIntegrand_shift_of_product ψ abv u
  intro g
  change W.val g * ((χ (determinant g) : ℂ) * W'.val g) = _
  rw [unramifiedCharacter_determinant abv χ u hχ, mul_left_comm]

/-- Twisting the larger representation shifts every unequal-rank block. -/
theorem unequalRankZetaValues_unramified_left {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    unequalRankZetaValues q ψ abv j k μ ν (Langlands.twist (χ.comp determinant) π) σ =
      e '' unequalRankZetaValues q ψ abv j k μ ν π σ := by
  unfold unequalRankZetaValues
  rw [whittakerSet_twist_image]
  conv_lhs => rw [← Set.image_id (inverseWhittakerSet ψ n σ)]
  apply unequalRankValuesOf_image_of_shift ψ abv q u e hshift
  intro W W' s
  apply unequalRankIntegrand_shift_of_product ψ abv j k u
  intro g x
  change ((χ (determinant (unequalRankMatrix j k g x)) : ℂ) *
    W.val (unequalRankMatrix j k g x)) * W'.val g = _
  rw [determinant_unequalRankMatrix, unramifiedCharacter_determinant abv χ u hχ, mul_assoc]

/-- Twisting the smaller representation shifts every unequal-rank block. -/
theorem unequalRankZetaValues_unramified_right {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    unequalRankZetaValues q ψ abv j k μ ν π (Langlands.twist (χ.comp determinant) σ) =
      e '' unequalRankZetaValues q ψ abv j k μ ν π σ := by
  unfold unequalRankZetaValues
  rw [inverseWhittakerSet_twist_image]
  conv_lhs => rw [← Set.image_id (whittakerSet ψ (n + (j + k + 1)) π)]
  apply unequalRankValuesOf_image_of_shift ψ abv q u e hshift
  intro W W' s
  apply unequalRankIntegrand_shift_of_product ψ abv j k u
  intro g x
  change W.val (unequalRankMatrix j k g x) * ((χ (determinant g) : ℂ) * W'.val g) = _
  rw [unramifiedCharacter_determinant abv χ u hχ, mul_left_comm]

end RepresentationValues

end ValueTransport

end Langlands.RankinSelberg
