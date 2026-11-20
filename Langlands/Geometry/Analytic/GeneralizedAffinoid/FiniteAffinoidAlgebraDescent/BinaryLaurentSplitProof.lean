import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.BinaryLaurentSplitStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximation
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentIdealDescent

/-! # Proof that real-radius binary Laurent splits of full domains are split squares -/

noncomputable section

universe u

open Filter Topology

namespace Langlands.Analytic.PresentedAffinoidAlgebra

namespace BinaryLaurentSplit

/-- An additive continuous map from a complete normed group that admits
approximate solutions with norm control and halving residuals is surjective,
with norm-controlled exact solutions. -/
theorem exists_eq_of_approx {V W : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    [NormedAddCommGroup W] (T : V →+ W) (hT : Continuous T) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w, ∃ v, ‖v‖ ≤ C * ‖w‖ ∧ ‖w - T v‖ ≤ ‖w‖ / 2) (w : W) :
    ∃ v, T v = w ∧ ‖v‖ ≤ C * ‖w‖ * 2 := by
  choose f hf₁ hf₂ using h
  let res : ℕ → W := fun k => (fun z => z - T (f z))^[k] w
  have res_succ : ∀ k, res (k + 1) = res k - T (f (res k)) := fun k =>
    Function.iterate_succ_apply' _ k w
  have hres : ∀ k, ‖res k‖ ≤ ‖w‖ * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp [res]
    | succ k ih =>
      rw [res_succ, pow_succ]
      calc ‖res k - T (f (res k))‖ ≤ ‖res k‖ / 2 := hf₂ _
        _ ≤ ‖w‖ * (1 / 2) ^ k / 2 := by gcongr
        _ = ‖w‖ * ((1 / 2) ^ k * (1 / 2)) := by ring
  have hbound : ∀ k, ‖f (res k)‖ ≤ C * ‖w‖ * (1 / 2) ^ k := fun k =>
    (hf₁ _).trans (by
      calc C * ‖res k‖ ≤ C * (‖w‖ * (1 / 2) ^ k) := by gcongr; exact hres k
        _ = C * ‖w‖ * (1 / 2) ^ k := by ring)
  have hgeom : HasSum (fun k : ℕ => C * ‖w‖ * (1 / 2) ^ k) (C * ‖w‖ * 2) :=
    hasSum_geometric_two.mul_left _
  have hsum : Summable fun k => f (res k) := Summable.of_norm_bounded hgeom.summable hbound
  refine ⟨∑' k, f (res k), ?_, tsum_of_norm_bounded hgeom hbound⟩
  have hpartial : ∀ N, T (∑ k ∈ Finset.range N, f (res k)) = w - res N := by
    intro N
    rw [map_sum]
    have : ∀ k, T (f (res k)) = res k - res (k + 1) := fun k => by rw [res_succ]; abel
    simp_rw [this]
    rw [Finset.sum_range_sub']
    rfl
  have hlim₁ : Tendsto (fun N => T (∑ k ∈ Finset.range N, f (res k))) atTop
      (𝓝 (T (∑' k, f (res k)))) :=
    (hT.tendsto _).comp hsum.hasSum.tendsto_sum_nat
  have hres0 : Tendsto res atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hres ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul ‖w‖
  have hlim₂ : Tendsto (fun N => T (∑ k ∈ Finset.range N, f (res k))) atTop (𝓝 w) := by
    simp_rw [hpartial]
    simpa using (tendsto_const_nhds (x := w)).sub hres0
  exact tendsto_nhds_unique hlim₁ hlim₂

/-- `‖x yⁿ‖ ≤ ‖x‖ ‖y‖ⁿ` in any normed ring, without assuming `‖1‖ ≤ 1`. -/
theorem norm_mul_pow_le {B : Type*} [NormedRing B] (x y : B) (n : ℕ) :
    ‖x * y ^ n‖ ≤ ‖x‖ * ‖y‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, pow_succ, ← mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

section Relative

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (a : A) {ρ : ℝ}

/-- The image of a relative monomial in a two-variable relative rational quotient. -/
theorem quotientMap_monomial (s : PositivePolyradius (Fin 2)) (g : A) (f : Fin 2 → A)
    (d : Fin 2 →₀ ℕ) (c : A) :
    RelativeRationalPresentation.quotientMap K A s g f (monomial s A d c) =
      RelativeRationalPresentation.baseMap K A s g f c *
        (RelativeRationalPresentation.fraction K A s g f 0 ^ d 0 *
          RelativeRationalPresentation.fraction K A s g f 1 ^ d 1) := by
  rw [relative_monomial_eq (K := K), map_mul]
  congr 1
  rw [StrictTateAlgebra.monomialValue, map_finsuppProd,
    Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
  simp only [map_pow]
  rfl

/-- The weight of an exponent for the radii `(ρ⁻¹, ρ)`. -/
theorem weight_eq (s : PositivePolyradius (Fin 2)) (hs₀ : s 0 = ρ⁻¹) (hs₁ : s 1 = ρ)
    (d : Fin 2 →₀ ℕ) : s.weight d = ρ⁻¹ ^ d 0 * ρ ^ d 1 := by
  rw [PositivePolyradius.weight, Finsupp.prod_fintype _ _ (fun i => by simp),
    Fin.prod_univ_two, hs₀, hs₁]

theorem weight_eq_of_le (hρ : 0 < ρ) (s : PositivePolyradius (Fin 2)) (hs₀ : s 0 = ρ⁻¹)
    (hs₁ : s 1 = ρ) (d : Fin 2 →₀ ℕ) (hd : d 0 ≤ d 1) :
    s.weight d = ρ ^ (d 1 - d 0) := by
  rw [weight_eq s hs₀ hs₁, ← Nat.add_sub_cancel' hd, pow_add, ← mul_assoc, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'), one_mul, Nat.add_sub_cancel_left]

theorem weight_eq_of_lt (hρ : 0 < ρ) (s : PositivePolyradius (Fin 2)) (hs₀ : s 0 = ρ⁻¹)
    (hs₁ : s 1 = ρ) (d : Fin 2 →₀ ℕ) (hd : d 1 < d 0) :
    s.weight d = ρ⁻¹ ^ (d 0 - d 1) := by
  obtain ⟨k, hk⟩ : ∃ k, d 0 = d 1 + k := ⟨d 0 - d 1, by omega⟩
  rw [weight_eq s hs₀ hs₁, hk, Nat.add_sub_cancel_left, pow_add, mul_comm, ← mul_assoc,
    ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, one_mul]

end Relative

section Core

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (a : A) {ρ : ℝ}

/-- In the weighted quotient with denominator `1` and numerator `a`, the fraction is `a`. -/
theorem fraction_eq_of_one {s₁ : PositivePolyradius (Fin 1)} {g₁ : A} {f₁ : Fin 1 → A}
    (hg₁ : g₁ = 1) (hf₁ : f₁ 0 = a) :
    RelativeRationalPresentation.fraction K A s₁ g₁ f₁ 0 =
      RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ a := by
  subst g₁
  have h := RelativeRationalPresentation.fraction_equation K A s₁ 1 f₁ 0
  rwa [map_one, one_mul, hf₁] at h

/-- In the weighted quotient with denominator `a` and numerator `1`, the fraction
inverts `a`. -/
theorem baseMap_mul_fraction_of_one {s₂ : PositivePolyradius (Fin 1)} {g₂ : A}
    {f₂ : Fin 1 → A} (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1) :
    RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ a *
      RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0 = 1 := by
  subst g₂
  have h := RelativeRationalPresentation.fraction_equation K A s₂ a f₂ 0
  rwa [hf₂, map_one] at h

/-- In the overlap quotient with denominator `a` and numerators `1, a²`, the
first fraction inverts `a`. -/
theorem overlap_mul_fraction_zero {s : PositivePolyradius (Fin 2)} {g : A} {f : Fin 2 → A}
    (hg : g = a) (hf₀ : f 0 = 1) :
    RelativeRationalPresentation.baseMap K A s g f a *
      RelativeRationalPresentation.fraction K A s g f 0 = 1 := by
  subst g
  have h := RelativeRationalPresentation.fraction_equation K A s a f 0
  rwa [hf₀, map_one] at h

/-- In the overlap quotient the second fraction is `a` itself. -/
theorem overlap_fraction_one {s : PositivePolyradius (Fin 2)} {g : A} {f : Fin 2 → A}
    (hg : g = a) (hf₀ : f 0 = 1) (hf₁ : f 1 = a ^ 2) :
    RelativeRationalPresentation.fraction K A s g f 1 =
      RelativeRationalPresentation.baseMap K A s g f a := by
  subst g
  have h0 := overlap_mul_fraction_zero A a (s := s) (f := f) rfl hf₀
  have h1 := RelativeRationalPresentation.fraction_equation K A s a f 1
  rw [hf₁, map_pow, sq] at h1
  set B := RelativeRationalPresentation.baseMap K A s a f a
  set F₀ := RelativeRationalPresentation.fraction K A s a f 0
  set F₁ := RelativeRationalPresentation.fraction K A s a f 1
  calc F₁ = (B * F₀) * F₁ := by rw [h0, one_mul]
    _ = F₀ * (B * F₁) := by ring
    _ = F₀ * (B * B) := by rw [h1]
    _ = (B * F₀) * B := by ring
    _ = B := by rw [h0, one_mul]

end Core

section Pieces

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- The part of the monomial with exponent `d` and coefficient `c` that lies in
the first side, nonzero only when `d 0 ≤ d 1`. -/
def firstPiece (s₁ : PositivePolyradius (Fin 1)) (g₁ : A) (f₁ : Fin 1 → A)
    (d : Fin 2 →₀ ℕ) (c : A) : RelativeRationalPresentation.Algebra K A s₁ g₁ f₁ :=
  if d 0 ≤ d 1 then
    RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c *
      RelativeRationalPresentation.fraction K A s₁ g₁ f₁ 0 ^ (d 1 - d 0)
  else 0

/-- The part of the monomial with exponent `d` and coefficient `c` that lies in
the second side, nonzero only when `d 1 < d 0`. -/
def secondPiece (s₂ : PositivePolyradius (Fin 1)) (g₂ : A) (f₂ : Fin 1 → A)
    (d : Fin 2 →₀ ℕ) (c : A) : RelativeRationalPresentation.Algebra K A s₂ g₂ f₂ :=
  if d 0 ≤ d 1 then 0
  else
    RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c *
      RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0 ^ (d 0 - d 1)

end Pieces

section Split

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (a : A) {ρ : ℝ}
  {s₁ s₂ : PositivePolyradius (Fin 1)} {g₁ g₂ : A} {f₁ f₂ : Fin 1 → A}
  {s : PositivePolyradius (Fin 2)} {g : A} {f : Fin 2 → A}

/-- A map from the first side over the coefficients sends `c F₁ᵏ` to `c aᵏ`. -/
theorem first_apply (hg₁ : g₁ = 1) (hf₁ : f₁ 0 = a)
    (t₁ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₁ g₁ f₁)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₁ : ∀ c, t₁ (RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c) =
      RelativeRationalPresentation.baseMap K A s g f c) (c : A) (k : ℕ) :
    t₁ (RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c *
        RelativeRationalPresentation.fraction K A s₁ g₁ f₁ 0 ^ k) =
      RelativeRationalPresentation.baseMap K A s g f c *
        RelativeRationalPresentation.baseMap K A s g f a ^ k := by
  rw [fraction_eq_of_one A a hg₁ hf₁]
  simp only [map_mul, map_pow, ht₁]

/-- A map from the second side over the coefficients sends the inverse of `a`
to the inverse of `a`. -/
theorem second_fraction (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1) (hg : g = a) (hf₀ : f 0 = 1)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c) :
    t₂ (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0) =
      RelativeRationalPresentation.fraction K A s g f 0 := by
  have h₁ := baseMap_mul_fraction_of_one A a (s₂ := s₂) hg₂ hf₂
  have h₂ := overlap_mul_fraction_zero A a (s := s) hg hf₀
  have h₃ : RelativeRationalPresentation.baseMap K A s g f a *
      t₂ (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0) = 1 := by
    rw [← ht₂, ← map_mul, h₁, map_one]
  calc t₂ (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0)
      = (RelativeRationalPresentation.baseMap K A s g f a *
          RelativeRationalPresentation.fraction K A s g f 0) *
          t₂ (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0) := by rw [h₂, one_mul]
    _ = RelativeRationalPresentation.fraction K A s g f 0 *
          (RelativeRationalPresentation.baseMap K A s g f a *
            t₂ (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0)) := by ring
    _ = _ := by rw [h₃, mul_one]

/-- A map from the second side over the coefficients sends `c F₂ᵏ` to `c F₀ᵏ`. -/
theorem second_apply (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1) (hg : g = a) (hf₀ : f 0 = 1)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c) (c : A) (k : ℕ) :
    t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c *
        RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0 ^ k) =
      RelativeRationalPresentation.baseMap K A s g f c *
        RelativeRationalPresentation.fraction K A s g f 0 ^ k := by
  simp only [map_mul, map_pow, ht₂, second_fraction A a hg₂ hf₂ hg hf₀ t₂ ht₂]

/-- The two pieces of a monomial map to the image of the monomial in the overlap. -/
theorem piece_sum (hg₁ : g₁ = 1) (hf₁ : f₁ 0 = a) (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1)
    (hg : g = a) (hf₀ : f 0 = 1) (hf₁' : f 1 = a ^ 2)
    (t₁ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₁ g₁ f₁)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₁ : ∀ c, t₁ (RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c) =
      RelativeRationalPresentation.baseMap K A s g f c)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c) (d : Fin 2 →₀ ℕ) (c : A) :
    t₁ (firstPiece A s₁ g₁ f₁ d c) + t₂ (secondPiece A s₂ g₂ f₂ d c) =
      RelativeRationalPresentation.quotientMap K A s g f (monomial s A d c) := by
  have h0 := overlap_mul_fraction_zero A a (s := s) hg hf₀
  have e : ∀ (B F : RelativeRationalPresentation.Algebra K A s g f) (m k : ℕ),
      B * F = 1 → F ^ m * B ^ (m + k) = B ^ k := by
    intro B F m k h
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_comm F, h, one_pow, one_mul]
  have e' : ∀ (B F : RelativeRationalPresentation.Algebra K A s g f) (m k : ℕ),
      B * F = 1 → F ^ (m + k) * B ^ m = F ^ k := by
    intro B F m k h
    rw [pow_add, mul_comm (F ^ m), mul_assoc, ← mul_pow, mul_comm F, h, one_pow, mul_one]
  rw [quotientMap_monomial A s g f d c, overlap_fraction_one A a hg hf₀ hf₁']
  unfold firstPiece secondPiece
  split_ifs with hd
  · rw [map_zero t₂.toAlgHom, add_zero, first_apply A a hg₁ hf₁ t₁ ht₁]
    obtain ⟨k, hk⟩ : ∃ k, d 1 = d 0 + k := ⟨d 1 - d 0, by omega⟩
    rw [hk, Nat.add_sub_cancel_left, e _ _ _ _ h0]
  · rw [map_zero t₁.toAlgHom, zero_add, second_apply A a hg₂ hf₂ hg hf₀ t₂ ht₂]
    obtain ⟨k, hk⟩ : ∃ k, d 0 = d 1 + k := ⟨d 0 - d 1, by omega⟩
    rw [hk, Nat.add_sub_cancel_left, e' _ _ _ _ h0]

theorem norm_firstPiece_le (hρ : 0 < ρ) (hs₁ : s₁ 0 = ρ) (hs₀ : s 0 = ρ⁻¹) (hs₁' : s 1 = ρ)
    (d : Fin 2 →₀ ℕ) (c : A) :
    ‖firstPiece A s₁ g₁ f₁ d c‖ ≤ ‖c‖ * s.weight d := by
  unfold firstPiece
  split_ifs with hd
  · rw [weight_eq_of_le hρ s hs₀ hs₁' d hd]
    refine (norm_mul_pow_le _ _ _).trans ?_
    gcongr
    · exact RelativeRationalPresentation.norm_baseMap_le K A s₁ g₁ f₁ c
    · exact (RelativeRationalPresentation.norm_fraction_le K A s₁ g₁ f₁ 0).trans hs₁.le
  · rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (s.weight_pos d).le

theorem norm_secondPiece_le (hρ : 0 < ρ) (hs₂ : s₂ 0 = ρ⁻¹) (hs₀ : s 0 = ρ⁻¹)
    (hs₁' : s 1 = ρ) (d : Fin 2 →₀ ℕ) (c : A) :
    ‖secondPiece A s₂ g₂ f₂ d c‖ ≤ ‖c‖ * s.weight d := by
  unfold secondPiece
  split_ifs with hd
  · rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (s.weight_pos d).le
  · rw [weight_eq_of_lt hρ s hs₀ hs₁' d (not_le.mp hd)]
    refine (norm_mul_pow_le _ _ _).trans ?_
    gcongr
    · exact RelativeRationalPresentation.norm_baseMap_le K A s₂ g₂ f₂ c
    · exact (RelativeRationalPresentation.norm_fraction_le K A s₂ g₂ f₂ 0).trans hs₂.le

/-- One approximation step: every overlap element is approximated, up to half
its norm, by a sum of images from the two sides with norms at most twice its norm. -/
theorem exists_approx (hρ : 0 < ρ) (hs₁ : s₁ 0 = ρ) (hs₂ : s₂ 0 = ρ⁻¹)
    (hs₀ : s 0 = ρ⁻¹) (hs₁' : s 1 = ρ)
    (hg₁ : g₁ = 1) (hf₁ : f₁ 0 = a) (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1)
    (hg : g = a) (hf₀ : f 0 = 1) (hf₁' : f 1 = a ^ 2)
    (t₁ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₁ g₁ f₁)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₁ : ∀ c, t₁ (RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c) =
      RelativeRationalPresentation.baseMap K A s g f c)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c)
    (h : RelativeRationalPresentation.Algebra K A s g f) :
    ∃ v : RelativeRationalPresentation.Algebra K A s₁ g₁ f₁ ×
        RelativeRationalPresentation.Algebra K A s₂ g₂ f₂,
      ‖v‖ ≤ 2 * ‖h‖ ∧ ‖h - (t₁ v.1 + t₂ v.2)‖ ≤ ‖h‖ / 2 := by
  rcases eq_or_ne h 0 with rfl | h0
  · exact ⟨0, by simp, by simp⟩
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
  obtain ⟨H, rfl, hH⟩ :=
    RelativeRationalPresentation.exists_representative_norm_lt K A s g f h hpos
  have hsum : Tendsto (fun S : Finset (Fin 2 →₀ ℕ) =>
      ∑ d ∈ S, monomial s A d (MvPowerSeries.coeff d (series s A H))) atTop (𝓝 H) :=
    hasSum_monomials s A H
  obtain ⟨S, hS⟩ := (hsum.eventually (Metric.ball_mem_nhds H (half_pos hpos))).exists
  refine ⟨(∑ d ∈ S, firstPiece A s₁ g₁ f₁ d (MvPowerSeries.coeff d (series s A H)),
    ∑ d ∈ S, secondPiece A s₂ g₂ f₂ d (MvPowerSeries.coeff d (series s A H))), ?_, ?_⟩
  · have hHle : ‖H‖ ≤ 2 * ‖RelativeRationalPresentation.quotientMap K A s g f H‖ := by
      linarith
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg H)
        fun d _ => ?_).trans hHle
      exact (norm_firstPiece_le A hρ hs₁ hs₀ hs₁' d _).trans (weighted_norm_coeff_le s A H d)
    · refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg H)
        fun d _ => ?_).trans hHle
      exact (norm_secondPiece_le A hρ hs₂ hs₀ hs₁' d _).trans (weighted_norm_coeff_le s A H d)
  · have hT : t₁ (∑ d ∈ S, firstPiece A s₁ g₁ f₁ d (MvPowerSeries.coeff d (series s A H))) +
        t₂ (∑ d ∈ S, secondPiece A s₂ g₂ f₂ d (MvPowerSeries.coeff d (series s A H))) =
        RelativeRationalPresentation.quotientMap K A s g f
          (∑ d ∈ S, monomial s A d (MvPowerSeries.coeff d (series s A H))) := by
      rw [map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ =>
        piece_sum A a hg₁ hf₁ hg₂ hf₂ hg hf₀ hf₁' t₁ ht₁ t₂ ht₂ d _
    change ‖RelativeRationalPresentation.quotientMap K A s g f H -
      (t₁ (∑ d ∈ S, firstPiece A s₁ g₁ f₁ d (MvPowerSeries.coeff d (series s A H))) +
        t₂ (∑ d ∈ S, secondPiece A s₂ g₂ f₂ d (MvPowerSeries.coeff d (series s A H))))‖ ≤ _
    rw [hT, ← map_sub]
    refine (RelativeRationalPresentation.norm_quotientMap_le K A s g f _).trans ?_
    rw [← dist_eq_norm, dist_comm]
    exact (Metric.mem_ball.mp hS).le

/-- The model overlap splitting with constant `4`. -/
theorem exists_split [CompleteSpace K] (hρ : 0 < ρ) (hs₁ : s₁ 0 = ρ) (hs₂ : s₂ 0 = ρ⁻¹)
    (hs₀ : s 0 = ρ⁻¹) (hs₁' : s 1 = ρ)
    (hg₁ : g₁ = 1) (hf₁ : f₁ 0 = a) (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1)
    (hg : g = a) (hf₀ : f 0 = 1) (hf₁' : f 1 = a ^ 2)
    (t₁ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₁ g₁ f₁)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₁ : ∀ c, t₁ (RelativeRationalPresentation.baseMap K A s₁ g₁ f₁ c) =
      RelativeRationalPresentation.baseMap K A s g f c)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c)
    (h : RelativeRationalPresentation.Algebra K A s g f) :
    ∃ v₁ v₂, h = t₁ v₁ + t₂ v₂ ∧ ‖v₁‖ ≤ 4 * ‖h‖ ∧ ‖v₂‖ ≤ 4 * ‖h‖ := by
  let T : RelativeRationalPresentation.Algebra K A s₁ g₁ f₁ ×
      RelativeRationalPresentation.Algebra K A s₂ g₂ f₂ →+
        RelativeRationalPresentation.Algebra K A s g f :=
    { toFun := fun v => t₁ v.1 + t₂ v.2
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel }
  have hT : Continuous T :=
    (t₁.continuous.comp continuous_fst).add (t₂.continuous.comp continuous_snd)
  obtain ⟨v, hv, hvn⟩ := exists_eq_of_approx T hT (by norm_num : (0 : ℝ) ≤ 2)
    (fun w => exists_approx A a hρ hs₁ hs₂ hs₀ hs₁' hg₁ hf₁ hg₂ hf₂ hg hf₀ hf₁' t₁ ht₁ t₂ ht₂ w) h
  refine ⟨v.1, v.2, hv.symm, ?_, ?_⟩
  · exact (norm_fst_le v).trans (by linarith)
  · exact (norm_snd_le v).trans (by linarith)

/-- The second model restriction has dense range. -/
theorem denseRange_second (hg₂ : g₂ = a) (hf₂ : f₂ 0 = 1)
    (hg : g = a) (hf₀ : f 0 = 1) (hf₁' : f 1 = a ^ 2)
    (t₂ : BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s₂ g₂ f₂)
      (RelativeRationalPresentation.Algebra K A s g f))
    (ht₂ : ∀ c, t₂ (RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c) =
      RelativeRationalPresentation.baseMap K A s g f c) :
    DenseRange t₂ := by
  intro h
  obtain ⟨H, rfl⟩ := RelativeRationalPresentation.quotientMap_surjective K A s g f h
  have hsum : Tendsto (fun S : Finset (Fin 2 →₀ ℕ) =>
      ∑ d ∈ S, monomial s A d (MvPowerSeries.coeff d (series s A H))) atTop (𝓝 H) :=
    hasSum_monomials s A H
  have hmem : ∀ d c, RelativeRationalPresentation.quotientMap K A s g f (monomial s A d c) ∈
      t₂.toAlgHom.range := by
    intro d c
    refine ⟨RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ c *
      (RelativeRationalPresentation.fraction K A s₂ g₂ f₂ 0 ^ d 0 *
        RelativeRationalPresentation.baseMap K A s₂ g₂ f₂ a ^ d 1), ?_⟩
    rw [quotientMap_monomial A s g f d c, overlap_fraction_one A a hg hf₀ hf₁']
    change t₂ _ = _
    simp only [map_mul, map_pow, ht₂, second_fraction A a hg₂ hf₂ hg hf₀ t₂ ht₂]
  refine mem_closure_of_tendsto
    (((RelativeRationalPresentation.quotientMap K A s g f).continuous.tendsto H).comp hsum)
    (Eventually.of_forall fun S => ?_)
  change RelativeRationalPresentation.quotientMap K A s g f
      (∑ d ∈ S, monomial s A d (MvPowerSeries.coeff d (series s A H))) ∈ Set.range t₂
  rw [map_sum, ← AlgHom.coe_range]
  exact Subalgebra.sum_mem t₂.toAlgHom.range fun d _ => hmem d _

end Split

section Domain

open GeneralizedTateAlgebra FiniteAffinoidAlgebraDescent CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}

/-- A domain whose locus is that of the extension of a rational chart over
`U.algebra` is boundedly equivalent to the relative rational quotient of the chart. -/
def chartEquiv (U : Domain K R) (c : RationalChart K U.algebra) (V : Domain K R)
    (h : V.locus = (U.extend c.toDomain).locus) :
    BoundedAlgEquiv K V.algebra
      (RelativeRationalPresentation.Algebra K U.algebra c.radii
        (presentationMap K U.algebra c.denominator)
        (fun j => presentationMap K U.algebra (c.numerators j))) :=
  (Domain.boundedEquivOfLocusEq V (U.extend c.toDomain) h).trans
    (RationalPresentation.relativeEquiv K U.algebra c.radii c.denominator c.numerators)

/-- The chart comparison sends original restrictions from `U` to coefficients. -/
theorem chartEquiv_restriction (U : Domain K R) (c : RationalChart K U.algebra)
    (V : Domain K R) (h : V.locus = (U.extend c.toDomain).locus)
    (hV : V.locus ⊆ U.locus) (x : U.algebra) :
    chartEquiv U c V h (restriction hV x) =
      RelativeRationalPresentation.baseMap K U.algebra c.radii
        (presentationMap K U.algebra c.denominator)
        (fun j => presentationMap K U.algebra (c.numerators j)) x := by
  have hEV : (U.extend c.toDomain).locus ⊆ V.locus := fun _ hx => h.symm ▸ hx
  have h1 : Domain.boundedEquivOfLocusEq V (U.extend c.toDomain) h (restriction hV x) =
      restriction hEV (restriction hV x) := rfl
  have h2 : restriction hEV (restriction hV x) =
      RationalPresentation.baseMap K U.algebra c.radii c.denominator c.numerators x :=
    congrArg (fun φ : BoundedAlgHom K U.algebra (U.extend c.toDomain).algebra => φ x)
      ((restriction_comp hEV hV).trans (restriction_eq (U.extendInclusion c.toDomain) _))
  calc chartEquiv U c V h (restriction hV x)
      = RationalPresentation.relativeEquiv K U.algebra c.radii c.denominator c.numerators
          (Domain.boundedEquivOfLocusEq V (U.extend c.toDomain) h (restriction hV x)) := rfl
    _ = RationalPresentation.relativeEquiv K U.algebra c.radii c.denominator c.numerators
          (RationalPresentation.baseMap K U.algebra c.radii c.denominator c.numerators x) := by
        rw [h1, h2]
    _ = _ := RationalPresentation.relativeEquiv_baseMap K U.algebra c.radii c.denominator
          c.numerators x

/-- Gluing along a cover of `U` by two domains whose overlap lies in `W`. -/
theorem exists_glue {U U₁ U₂ W : Domain K R} (h₁ : U₁.locus ⊆ U.locus)
    (h₂ : U₂.locus ⊆ U.locus) (hW₁ : W.locus ⊆ U₁.locus) (hW₂ : W.locus ⊆ U₂.locus)
    (hcov : U.locus ⊆ U₁.locus ∪ U₂.locus) (hW : U₁.locus ∩ U₂.locus ⊆ W.locus)
    (a₁ : U₁.algebra) (a₂ : U₂.algebra) (h : restriction hW₁ a₁ = restriction hW₂ a₂) :
    ∃ x, restriction h₁ x = a₁ ∧ restriction h₂ x = a₂ := by
  have key : ∀ (V : Domain K R) (f : V ⟶ U₁) (g : V ⟶ U₂),
      f.restriction a₁ = g.restriction a₂ := by
    intro V f g
    have hV : V.locus ⊆ W.locus := fun x hx => hW ⟨f.subset hx, g.subset hx⟩
    have ef : f.restriction = (restriction hV).comp (restriction hW₁) :=
      (restriction_eq f f.subset).symm.trans (restriction_comp hV hW₁).symm
    have eg : g.restriction = (restriction hV).comp (restriction hW₂) :=
      (restriction_eq g g.subset).symm.trans (restriction_comp hV hW₂).symm
    rw [ef, eg]
    exact congrArg (fun z => restriction hV z) h
  let c : Domain.FiniteCover U :=
    { size := 2
      obj := ![U₁, U₂]
      map := fun i => Domain.inclusionOfSubset _ U (by fin_cases i; exacts [h₁, h₂])
      covers := fun x hx => by
        rcases hcov hx with hx | hx
        exacts [⟨0, hx⟩, ⟨1, hx⟩] }
  let s : ∀ i : Fin 2, (![U₁, U₂] i).algebra :=
    Fin.cons (α := fun i : Fin 2 => (![U₁, U₂] i).algebra) a₁
      (Fin.cons (α := fun i : Fin 1 => (![U₁, U₂] i.succ).algebra) a₂ finZeroElim)
  have hs : c.AlgebraCompatible s := by
    intro i j V f g
    fin_cases i <;> fin_cases j
    · exact congrArg (fun r : V ⟶ U₁ => r.restriction a₁)
        (@Subsingleton.elim (Domain.Inclusion V U₁) inferInstance f g)
    · exact key V f g
    · exact (key V g f).symm
    · exact congrArg (fun r : V ⟶ U₂ => r.restriction a₂)
        (@Subsingleton.elim (Domain.Inclusion V U₂) inferInstance f g)
  obtain ⟨x, hx, -⟩ := c.algebra_existsUnique s hs
  refine ⟨x, ?_, ?_⟩
  · exact (congrArg (fun φ => φ x) (restriction_eq (c.map 0) h₁)).trans (congrFun hx 0)
  · exact (congrArg (fun φ => φ x) (restriction_eq (c.map 1) h₂)).trans (congrFun hx 1)

variable (U : Domain K R) (a₀ : GeneralizedTateAlgebra U.algebra.polyradius K) {ρ : ℝ}
  (hρ : 0 < ρ)

/-- The chart `{|a₀| ≤ ρ}`, with denominator `1` and numerator `a₀`. -/
def chart₁ : RationalChart K U.algebra where
  arity := 1
  radii := ⟨fun _ => ρ, fun _ => hρ⟩
  denominator := 1
  numerators := fun _ => a₀
  generates := by
    unfold RationalPresentation.GeneratesUnitIdeal
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _))
      (by rw [map_one]; exact isUnit_one)

/-- The chart `{|a₀| ≥ ρ}`, with denominator `a₀`, numerator `1` and radius `ρ⁻¹`. -/
def chart₂ : RationalChart K U.algebra where
  arity := 1
  radii := ⟨fun _ => ρ⁻¹, fun _ => inv_pos.mpr hρ⟩
  denominator := a₀
  numerators := fun _ => 1
  generates := by
    unfold RationalPresentation.GeneratesUnitIdeal
    exact Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
      (by simp)

/-- The chart `{|a₀| = ρ}`, with denominator `a₀`, numerators `1, a₀²` and
radii `ρ⁻¹, ρ`. -/
def chart₁₂ : RationalChart K U.algebra where
  arity := 2
  radii := ⟨![ρ⁻¹, ρ], by intro i; fin_cases i <;> simp [hρ]⟩
  denominator := a₀
  numerators := ![1, a₀ ^ 2]
  generates := by
    unfold RationalPresentation.GeneratesUnitIdeal
    exact Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
      (by simp)

theorem chart₁_locus :
    (chart₁ U a₀ hρ).locus = {y | y (presentationMap K U.algebra a₀) ≤ ρ} := by
  ext y
  change (∀ _ : Fin 1, y (presentationMap K U.algebra a₀) ≤
    ρ * y (presentationMap K U.algebra 1)) ↔ _
  rw [map_one, show y 1 = 1 from map_one y.toMulRingSeminorm, mul_one]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem chart₂_locus :
    (chart₂ U a₀ hρ).locus = {y | ρ ≤ y (presentationMap K U.algebra a₀)} := by
  ext y
  change (∀ _ : Fin 1, y (presentationMap K U.algebra 1) ≤
    ρ⁻¹ * y (presentationMap K U.algebra a₀)) ↔ _
  rw [map_one, show y 1 = 1 from map_one y.toMulRingSeminorm, one_le_inv_mul₀ hρ]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem chart₁₂_locus :
    (chart₁₂ U a₀ hρ).locus = {y | y (presentationMap K U.algebra a₀) ≤ ρ} ∩
      {y | ρ ≤ y (presentationMap K U.algebra a₀)} := by
  ext y
  change (∀ j : Fin 2, y (presentationMap K U.algebra (![1, a₀ ^ 2] j)) ≤
    ![ρ⁻¹, ρ] j * y (presentationMap K U.algebra a₀)) ↔ _
  rw [Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_pow,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [one_le_inv_mul₀ hρ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h1⟩
  · rintro ⟨h1, h2⟩
    have : y (presentationMap K U.algebra a₀) = ρ := le_antisymm h1 h2
    refine ⟨h2, ?_⟩
    rw [this, sq]

theorem extend_chart₁_locus :
    (U.extend (chart₁ U a₀ hρ).toDomain).locus =
      U.spectrumMap '' {y | y (presentationMap K U.algebra a₀) ≤ ρ} := by
  rw [Domain.extend_locus, RationalChart.toDomain_locus, chart₁_locus]

theorem extend_chart₂_locus :
    (U.extend (chart₂ U a₀ hρ).toDomain).locus =
      U.spectrumMap '' {y | ρ ≤ y (presentationMap K U.algebra a₀)} := by
  rw [Domain.extend_locus, RationalChart.toDomain_locus, chart₂_locus]

theorem extend_chart₁₂_locus :
    (U.extend (chart₁₂ U a₀ hρ).toDomain).locus =
      U.spectrumMap '' {y | y (presentationMap K U.algebra a₀) ≤ ρ} ∩
        U.spectrumMap '' {y | ρ ≤ y (presentationMap K U.algebra a₀)} := by
  rw [Domain.extend_locus, RationalChart.toDomain_locus, chart₁₂_locus,
    Set.image_inter U.spectrumMap_injective]

variable {U a₀} in
/-- The split square of the original restrictions of a binary Laurent split,
transported from the model computation through the chart comparisons. -/
def splitSquare {U₁ U₂ W : Domain K R} (h₁ : U₁.locus ⊆ U.locus) (h₂ : U₂.locus ⊆ U.locus)
    (hW₁ : W.locus ⊆ U₁.locus) (hW₂ : W.locus ⊆ U₂.locus)
    (hU₁ : U₁.locus = U.spectrumMap '' {y | y (presentationMap K U.algebra a₀) ≤ ρ})
    (hU₂ : U₂.locus = U.spectrumMap '' {y | ρ ≤ y (presentationMap K U.algebra a₀)})
    (hW : W.locus = U₁.locus ∩ U₂.locus) :
    BoundedAlgHom.SplitSquare (restriction h₁) (restriction h₂) (restriction hW₁)
      (restriction hW₂) := by
  let e₁ := chartEquiv U (chart₁ U a₀ hρ) U₁ (hU₁.trans (extend_chart₁_locus U a₀ hρ).symm)
  let e₂ := chartEquiv U (chart₂ U a₀ hρ) U₂ (hU₂.trans (extend_chart₂_locus U a₀ hρ).symm)
  let e₁₂ := chartEquiv U (chart₁₂ U a₀ hρ) W
    (by rw [hW, hU₁, hU₂, extend_chart₁₂_locus])
  let t₁ := e₁₂.toBoundedAlgHom.comp ((restriction hW₁).comp e₁.symm.toBoundedAlgHom)
  let t₂ := e₁₂.toBoundedAlgHom.comp ((restriction hW₂).comp e₂.symm.toBoundedAlgHom)
  have hB₁ : ∀ x, e₁ (restriction h₁ x) = _ := chartEquiv_restriction U (chart₁ U a₀ hρ) U₁
    (hU₁.trans (extend_chart₁_locus U a₀ hρ).symm) h₁
  have hB₂ : ∀ x, e₂ (restriction h₂ x) = _ := chartEquiv_restriction U (chart₂ U a₀ hρ) U₂
    (hU₂.trans (extend_chart₂_locus U a₀ hρ).symm) h₂
  have hB : ∀ x, e₁₂ (restriction (hW₁.trans h₁) x) = _ :=
    chartEquiv_restriction U (chart₁₂ U a₀ hρ) W (by rw [hW, hU₁, hU₂, extend_chart₁₂_locus])
      (hW₁.trans h₁)
  have ht₁ : ∀ x, t₁ (RelativeRationalPresentation.baseMap K U.algebra
      (chart₁ U a₀ hρ).radii (presentationMap K U.algebra (chart₁ U a₀ hρ).denominator)
      (fun j => presentationMap K U.algebra ((chart₁ U a₀ hρ).numerators j)) x) =
      RelativeRationalPresentation.baseMap K U.algebra
      (chart₁₂ U a₀ hρ).radii (presentationMap K U.algebra (chart₁₂ U a₀ hρ).denominator)
      (fun j => presentationMap K U.algebra ((chart₁₂ U a₀ hρ).numerators j)) x := by
    intro x
    rw [← hB₁ x, ← hB x]
    change e₁₂ (restriction hW₁ (e₁.symm (e₁ (restriction h₁ x)))) = _
    rw [e₁.symm_apply_apply]
    exact congrArg (fun z => e₁₂ z)
      (congrArg (fun φ : BoundedAlgHom K U.algebra W.algebra => φ x) (restriction_comp hW₁ h₁))
  have ht₂ : ∀ x, t₂ (RelativeRationalPresentation.baseMap K U.algebra
      (chart₂ U a₀ hρ).radii (presentationMap K U.algebra (chart₂ U a₀ hρ).denominator)
      (fun j => presentationMap K U.algebra ((chart₂ U a₀ hρ).numerators j)) x) =
      RelativeRationalPresentation.baseMap K U.algebra
      (chart₁₂ U a₀ hρ).radii (presentationMap K U.algebra (chart₁₂ U a₀ hρ).denominator)
      (fun j => presentationMap K U.algebra ((chart₁₂ U a₀ hρ).numerators j)) x := by
    intro x
    rw [← hB₂ x, ← hB x]
    change e₁₂ (restriction hW₂ (e₂.symm (e₂ (restriction h₂ x)))) = _
    rw [e₂.symm_apply_apply]
    exact congrArg (fun z => e₁₂ z)
      (congrArg (fun φ : BoundedAlgHom K U.algebra W.algebra => φ x)
        (restriction_comp hW₂ h₂))
  have hs₁ : (chart₁ U a₀ hρ).radii (0 : Fin 1) = ρ := rfl
  have hs₂ : (chart₂ U a₀ hρ).radii (0 : Fin 1) = ρ⁻¹ := rfl
  have hs₀ : (chart₁₂ U a₀ hρ).radii (0 : Fin 2) = ρ⁻¹ := rfl
  have hs₁' : (chart₁₂ U a₀ hρ).radii (1 : Fin 2) = ρ := rfl
  have hg₁ : presentationMap K U.algebra (chart₁ U a₀ hρ).denominator = 1 := map_one _
  have hf₁ : (fun j => presentationMap K U.algebra ((chart₁ U a₀ hρ).numerators j)) (0 : Fin 1) =
      presentationMap K U.algebra a₀ := rfl
  have hg₂ : presentationMap K U.algebra (chart₂ U a₀ hρ).denominator =
      presentationMap K U.algebra a₀ := rfl
  have hf₂ : (fun j => presentationMap K U.algebra ((chart₂ U a₀ hρ).numerators j)) (0 : Fin 1) = 1 :=
    map_one _
  have hg : presentationMap K U.algebra (chart₁₂ U a₀ hρ).denominator =
      presentationMap K U.algebra a₀ := rfl
  have hf₀ : (fun j => presentationMap K U.algebra ((chart₁₂ U a₀ hρ).numerators j)) (0 : Fin 2) = 1 :=
    map_one _
  have hf₁' : (fun j => presentationMap K U.algebra ((chart₁₂ U a₀ hρ).numerators j)) (1 : Fin 2) =
      presentationMap K U.algebra a₀ ^ 2 :=
    map_pow _ _ _
  have hcov : U.locus ⊆ U₁.locus ∪ U₂.locus := by
    intro x hx
    obtain ⟨y, hy⟩ := U.spectrumToLocus_surjective ⟨x, hx⟩
    have hyx : U.spectrumMap y = x := congrArg Subtype.val hy
    rcases le_total (y (presentationMap K U.algebra a₀)) ρ with hle | hle
    · left
      rw [hU₁]
      exact ⟨y, hle, hyx⟩
    · right
      rw [hU₂]
      exact ⟨y, hle, hyx⟩
  have hsub : U₁.locus ∩ U₂.locus ⊆ W.locus := fun x hx => by
    rw [hW]
    exact hx
  let S : BoundedAlgHom.SplitSquare (e₁.toBoundedAlgHom.comp (restriction h₁))
      (e₂.toBoundedAlgHom.comp (restriction h₂)) t₁ t₂ :=
    { comm := fun x => by
        change t₁ (e₁ (restriction h₁ x)) = t₂ (e₂ (restriction h₂ x))
        rw [hB₁, hB₂, ht₁, ht₂]
      glue := fun b₁ b₂ hb => by
        have hb' : e₁₂ (restriction hW₁ (e₁.symm b₁)) = e₁₂ (restriction hW₂ (e₂.symm b₂)) :=
          hb
        obtain ⟨x, hx₁, hx₂⟩ := exists_glue h₁ h₂ hW₁ hW₂ hcov hsub _ _
          (e₁₂.toAlgEquiv.injective hb')
        refine ⟨x, ?_, ?_⟩
        · change e₁ (restriction h₁ x) = b₁
          rw [hx₁, e₁.apply_symm_apply]
        · change e₂ (restriction h₂ x) = b₂
          rw [hx₂, e₂.apply_symm_apply]
      dense := denseRange_second U.algebra (presentationMap K U.algebra a₀) hg₂ hf₂ hg hf₀
        hf₁' t₂ ht₂
      bound := 4
      bound_nonneg := by norm_num
      split := exists_split U.algebra (presentationMap K U.algebra a₀) hρ hs₁ hs₂ hs₀ hs₁'
        hg₁ hf₁ hg₂ hf₂ hg hf₀ hf₁' t₁ ht₁ t₂ ht₂ }
  exact S.congr (restriction h₁) (restriction h₂) (restriction hW₁) (restriction hW₂)
    (BoundedAlgEquiv.refl K U.algebra) e₁ e₂ e₁₂ (fun _ => rfl) (fun _ => rfl)
    (fun b => by
      change _ = e₁₂ (restriction hW₁ (e₁.symm (e₁ b)))
      rw [e₁.symm_apply_apply])
    (fun b => by
      change _ = e₁₂ (restriction hW₂ (e₂.symm (e₂ b)))
      rw [e₂.symm_apply_apply])

end Domain

end BinaryLaurentSplit

open BinaryLaurentSplit in
/-- Real-radius binary Laurent splits of full domains are split squares. -/
theorem domainBinaryLaurentSplitSquare : DomainBinaryLaurentSplitSquareStatement.{u} := by
  intro K _ _ _ R U a ρ hρ
  obtain ⟨a₀, rfl⟩ := presentationMap_surjective K U.algebra a
  refine ⟨⟨U.extend (chart₁ U a₀ hρ).toDomain, U.extend (chart₂ U a₀ hρ).toDomain,
    extend_chart₁_locus U a₀ hρ, extend_chart₂_locus U a₀ hρ⟩, ?_⟩
  intro U₁ U₂ W h₁ h₂ hW₁ hW₂ hU₁ hU₂ hW
  exact ⟨splitSquare hρ h₁ h₂ hW₁ hW₂ hU₁ hU₂ hW⟩

end Langlands.Analytic.PresentedAffinoidAlgebra
