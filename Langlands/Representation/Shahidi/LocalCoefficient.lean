import Langlands.Representation.Shahidi.IntertwiningIntegral
import Langlands.Representation.Shahidi.JacquetIntegral
import Langlands.Representation.RankinSelberg.RationalContinuation

/-! # The local-coefficient relation (0.3) on function spaces, and its uniqueness -/

noncomputable section

open MeasureTheory

universe uF uH uV

namespace Langlands.Shahidi

open HarmonicAnalysis RankinSelberg

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (m n : ℕ) (ψ : UnitaryAdditiveCharacter F) (ρ : Representation ℂ H V)
  (ℓ ℓ' : V →ₗ[ℂ] ℂ) (μ μJ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
  (μJ' : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))

section Pointwise

/-- Equation (0.3) for one function `f` and one complex number `c`: `c` is
nonzero, so that `c⁻¹` is a genuine reciprocal; the intertwining integral `A f`
of (0.1) exists (against `μ`); the Jacquet integral (0.2) of `f` stabilizes to
`z` (against `μJ`, functional `ℓ`); the swapped Jacquet integral of `A f`
stabilizes to `z'` (against `μJ'`, functional `ℓ'`); and `z' = c⁻¹ z`. -/
def SatisfiesLocalCoefficientEquation
    (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V) (c : ℂ) : Prop :=
  c ≠ 0 ∧
    ∃ (A : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V) (z z' : ℂ),
      HasIntertwiningIntegral (m + 1) (n + 1) ρ μ f A ∧
      HasJacquetIntegral m n ψ ℓ μJ f z ∧
      HasSwappedJacquetIntegral m n ψ ℓ' μJ' A z' ∧
      z' = c⁻¹ * z

/-- `c` is the local coefficient on the set of functions `S`: equation (0.3)
holds with the same `c` for every `f ∈ S`. -/
def IsLocalCoefficientAt (S : Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V))
    (c : ℂ) : Prop :=
  ∀ f ∈ S, SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c

variable {m n ψ ρ ℓ ℓ' μ μJ μJ'}

omit [IsTopologicalRing F] in
/-- A local coefficient at one function is nonzero. -/
theorem SatisfiesLocalCoefficientEquation.ne_zero
    {f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V} {c : ℂ}
    (h : SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c) : c ≠ 0 :=
  h.1

omit [IsTopologicalRing F] in
/-- (0.3) without inverses: `c ≠ 0` and `c λ'(A f) = λ(f)`. -/
theorem satisfiesLocalCoefficientEquation_iff_mul
    {f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V} {c : ℂ} :
    SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c ↔
      c ≠ 0 ∧
        ∃ (A : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V) (z z' : ℂ),
          HasIntertwiningIntegral (m + 1) (n + 1) ρ μ f A ∧
          HasJacquetIntegral m n ψ ℓ μJ f z ∧
          HasSwappedJacquetIntegral m n ψ ℓ' μJ' A z' ∧
          c * z' = z := by
  refine and_congr_right fun hc => ?_
  simp only [eq_inv_mul_iff_mul_eq₀ hc]

section Unique

variable [IsTopologicalGroup H]
  (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K)
  (hρ : IsSmooth ρ)

include hcofinal hρ in
/-- For one function whose Jacquet integral is nonzero, (0.3) determines `c`. -/
theorem SatisfiesLocalCoefficientEquation.unique
    {f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V} {c c' z : ℂ}
    (hz : HasJacquetIntegral m n ψ ℓ μJ f z) (hz0 : z ≠ 0)
    (h : SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c)
    (h' : SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c') : c = c' := by
  obtain ⟨-, A, z₁, z₁', hA, hz₁, hz₁', rfl⟩ := h
  obtain ⟨-, B, z₂, z₂', hB, hz₂, hz₂', heq⟩ := h'
  obtain rfl := hA.unique hcofinal hρ hB
  obtain rfl := HasJacquetIntegral.unique _ _ _ _ hz₁ hz
  obtain rfl := HasJacquetIntegral.unique _ _ _ _ hz₂ hz
  obtain rfl := HasSwappedJacquetIntegral.unique _ _ _ _ hz₁' hz₂'
  exact inv_inj.1 (mul_right_cancel₀ hz0 heq)

include hcofinal hρ in
/-- The local coefficient on `S` is unique once some `f ∈ S` has a nonzero
Jacquet integral. -/
theorem IsLocalCoefficientAt.unique
    {S : Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)} {c c' : ℂ}
    (hS : ∃ f ∈ S, ∃ z, HasJacquetIntegral m n ψ ℓ μJ f z ∧ z ≠ 0)
    (h : IsLocalCoefficientAt m n ψ ρ ℓ ℓ' μ μJ μJ' S c)
    (h' : IsLocalCoefficientAt m n ψ ρ ℓ ℓ' μ μJ μJ' S c') : c = c' := by
  obtain ⟨f, hf, z, hz, hz0⟩ := hS
  exact (h f hf).unique hcofinal hρ hz hz0 (h' f hf)

end Unique

omit [IsTopologicalRing F] in
/-- Rescaling both functionals by the same scalar preserves (0.3). -/
theorem SatisfiesLocalCoefficientEquation.smul
    {f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V} {c : ℂ}
    (h : SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c) (a : ℂ) :
    SatisfiesLocalCoefficientEquation m n ψ ρ (a • ℓ) (a • ℓ') μ μJ μJ' f c := by
  obtain ⟨hc, A, z, z', hA, hz, hz', rfl⟩ := h
  refine ⟨hc, A, a * z, a * (c⁻¹ * z), hA, ?_, ?_, by ring⟩
  · exact HasStableIntegral.congr (HasStableIntegral.smul hz a) fun x => by
      simp [mul_left_comm]
  · exact HasStableIntegral.congr (HasStableIntegral.smul hz' a) fun x => by
      simp [mul_left_comm]

omit [IsTopologicalRing F] in
/-- For a nonzero scalar, (0.3) for the rescaled functionals is equivalent to
(0.3) for the original ones. -/
theorem satisfiesLocalCoefficientEquation_smul_iff
    {f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V} {c a : ℂ} (ha : a ≠ 0) :
    SatisfiesLocalCoefficientEquation m n ψ ρ (a • ℓ) (a • ℓ') μ μJ μJ' f c ↔
      SatisfiesLocalCoefficientEquation m n ψ ρ ℓ ℓ' μ μJ μJ' f c := by
  refine ⟨fun h => ?_, fun h => h.smul a⟩
  simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul a⁻¹

end Pointwise

section Rational

variable (q : ℕ)

/-- The rational function `C` of `q^(-s)` is the local coefficient of the
family of function sets `S s`: on some right half-plane, the denominator of
`C` does not vanish at `q^(-s)`, some `f ∈ S s` has a nonzero Jacquet
integral, and every `f ∈ S s` satisfies (0.3) with `c = C(q^(-s))`, that is
`C(q^(-s)) ≠ 0` and `λ'(A f) = C(q^(-s))⁻¹ λ(f)`. So `C` has neither poles
nor zeros on the half-plane (`IsLocalCoefficient.reciprocal`). -/
def IsLocalCoefficient
    (S : ℂ → Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V))
    (C : RatFunc ℂ) : Prop :=
  ∃ a : ℝ, ∀ s : ℂ, a < s.re →
    C.denom.eval (spectralPoint q s) ≠ 0 ∧
    (∃ f ∈ S s, ∃ z, HasJacquetIntegral m n ψ ℓ μJ f z ∧ z ≠ 0) ∧
    IsLocalCoefficientAt m n ψ ρ ℓ ℓ' μ μJ μJ' (S s)
      (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) C)

variable {m n ψ ρ ℓ ℓ' μ μJ μJ' q}

omit [IsTopologicalRing F] in
/-- On the half-plane of `IsLocalCoefficient`, `C` has no zero, and the
reciprocal rational function `C⁻¹` has no pole and takes the reciprocal
values: (0.3) reads `λ'(A f) = C⁻¹(q^(-s)) λ(f)` there. -/
theorem IsLocalCoefficient.reciprocal
    {S : ℂ → Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)} {C : RatFunc ℂ}
    (h : IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      C.num.eval (spectralPoint q s) ≠ 0 ∧
      C⁻¹.denom.eval (spectralPoint q s) ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) C⁻¹ =
        (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) C)⁻¹ := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun s hs => ?_⟩
  obtain ⟨hden, ⟨f, hf, -⟩, hC⟩ := ha s hs
  have hc := (hC f hf).ne_zero
  have hC0 : C ≠ 0 := by
    rintro rfl
    exact hc (RatFunc.eval_zero _ _)
  have hnum : C.num.eval (spectralPoint q s) ≠ 0 := fun h0 => hc (by
    rw [RatFunc.eval, Polynomial.eval₂_id, h0, zero_div])
  have hdeninv : C⁻¹.denom.eval (spectralPoint q s) ≠ 0 := fun h0 =>
    hnum (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ (RatFunc.denom_inv_dvd hC0) h0)
  refine ⟨hnum, hdeninv, eq_inv_of_mul_eq_one_right ?_⟩
  rw [← RatFunc.eval_mul _ _ hden hdeninv, mul_inv_cancel₀ hC0, RatFunc.eval_one]

omit [IsTopologicalRing F] in
/-- A local coefficient is not the zero rational function. -/
theorem IsLocalCoefficient.ne_zero
    {S : ℂ → Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)} {C : RatFunc ℂ}
    (h : IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C) : C ≠ 0 := by
  obtain ⟨a, ha⟩ := h.reciprocal
  have hs : a < ((a + 1 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  intro hC0
  apply (ha _ hs).1
  rw [hC0, RatFunc.num_zero, Polynomial.eval_zero]

/-- The local coefficient is unique when `q > 1`. -/
theorem IsLocalCoefficient.unique [IsTopologicalGroup H]
    (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ L ≤ K)
    (hρ : IsSmooth ρ) (hq : 1 < q)
    {S : ℂ → Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)} {C C' : RatFunc ℂ}
    (h : IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C)
    (h' : IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C') : C = C' := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  have hre : ∀ t ∈ Set.Ioi (max a a'), a < (t : ℂ).re ∧ a' < (t : ℂ).re := fun t ht => by
    rw [Complex.ofReal_re]
    exact max_lt_iff.1 ht
  apply rationalFunction_eq_of_infinite_eval_eq C C'
    ((fun t : ℝ => spectralPoint q t) '' Set.Ioi (max a a'))
    ((Set.Ioi_infinite _).image (spectralPoint_ofReal_injective hq).injOn)
  · rintro x ⟨t, ht, rfl⟩
    exact (ha t (hre t ht).1).1
  · rintro x ⟨t, ht, rfl⟩
    exact (ha' t (hre t ht).2).1
  · rintro x ⟨t, ht, rfl⟩
    obtain ⟨-, hS, hC⟩ := ha t (hre t ht).1
    obtain ⟨-, -, hC'⟩ := ha' t (hre t ht).2
    exact hC.unique hcofinal hρ hS hC'

omit [IsTopologicalRing F] in
/-- Rescaling both functionals by a nonzero scalar preserves the local
coefficient. -/
theorem IsLocalCoefficient.smul {S : ℂ → Set (Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)}
    {C : RatFunc ℂ} (h : IsLocalCoefficient m n ψ ρ ℓ ℓ' μ μJ μJ' q S C) {b : ℂ} (hb : b ≠ 0) :
    IsLocalCoefficient m n ψ ρ (b • ℓ) (b • ℓ') μ μJ μJ' q S C := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun s hs => ?_⟩
  obtain ⟨hden, ⟨f, hf, z, hz, hz0⟩, hC⟩ := ha s hs
  refine ⟨hden, ⟨f, hf, b * z, ?_, mul_ne_zero hb hz0⟩, fun g hg => (hC g hg).smul b⟩
  exact HasStableIntegral.congr (HasStableIntegral.smul hz b) fun x => by simp [mul_left_comm]

end Rational

end Langlands.Shahidi
