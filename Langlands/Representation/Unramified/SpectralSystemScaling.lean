import Langlands.Representation.Unramified.SpectralSystem
import Langlands.Representation.Unramified.EigenvalueScaling

/-! # Pointwise unit scaling of finite-exception spectral systems -/

noncomputable section
universe uI

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

variable {I : Type uI} {n m : ℕ}

/-- Multiply every spectrum by the specified unit at its index, keeping its
exceptional set and all eigenvalue multiplicities. -/
def scale (a : I → ℂˣ) (s : SpectralSystem I n) : SpectralSystem I n where
  exceptional := s.exceptional
  eigenvalues v hv := Eigenvalues.scale (a v) (s.eigenvalues v hv)

@[simp] theorem scale_exceptional (a : I → ℂˣ) (s : SpectralSystem I n) :
    (scale a s).exceptional = s.exceptional := rfl

@[simp] theorem scale_eigenvalues (a : I → ℂˣ) (s : SpectralSystem I n)
    (v : I) (hv : v ∉ s.exceptional) :
    (scale a s).eigenvalues v hv = Eigenvalues.scale (a v) (s.eigenvalues v hv) := rfl

@[simp] theorem scale_one (s : SpectralSystem I n) :
    scale (fun _ => 1) s = s := by
  cases s
  simp [scale]

theorem scale_scale (a b : I → ℂˣ) (s : SpectralSystem I n) :
    scale a (scale b s) = scale (fun v => a v * b v) s := by
  cases s
  simp only [scale, Eigenvalues.scale_scale]

@[simp] theorem scale_inv_scale (a : I → ℂˣ) (s : SpectralSystem I n) :
    scale (fun v => (a v)⁻¹) (scale a s) = s := by
  rw [scale_scale]
  simp

@[simp] theorem scale_scale_inv (a : I → ℂˣ) (s : SpectralSystem I n) :
    scale a (scale (fun v => (a v)⁻¹) s) = s := by
  rw [scale_scale]
  simp

/-- Scaling is invertible even when the specified unit varies with the index. -/
def scaleEquiv (a : I → ℂˣ) : SpectralSystem I n ≃ SpectralSystem I n where
  toFun := scale a
  invFun := scale (fun v => (a v)⁻¹)
  left_inv := scale_inv_scale a
  right_inv := scale_scale_inv a

@[simp] theorem scale_powerTrace (a : I → ℂˣ) (s : SpectralSystem I n)
    (v : I) (hv : v ∉ s.exceptional) (k : ℕ) :
    (scale a s).powerTrace v hv k = (a v : ℂ) ^ k * s.powerTrace v hv k :=
  Eigenvalues.powerTrace_scale _ _ _

theorem scale_eulerPolynomial (a : I → ℂˣ) (s : SpectralSystem I n)
    (v : I) (hv : v ∉ s.exceptional) :
    (scale a s).eulerPolynomial v hv =
      (s.eulerPolynomial v hv).comp (Polynomial.C (a v : ℂ) * Polynomial.X) :=
  Eigenvalues.eulerPolynomial_scale _ _

@[simp] theorem scale_eulerPolynomial_coeff (a : I → ℂˣ) (s : SpectralSystem I n)
    (v : I) (hv : v ∉ s.exceptional) (i : ℕ) :
    ((scale a s).eulerPolynomial v hv).coeff i =
      (a v : ℂ) ^ i * (s.eulerPolynomial v hv).coeff i :=
  Eigenvalues.eulerPolynomial_scale_coeff _ _ _

@[simp] theorem scale_restrict (a : I → ℂˣ) (s : SpectralSystem I n)
    (T : Finset I) (hT : s.exceptional ⊆ T) :
    scale a (s.restrict T hT) = (scale a s).restrict T hT := rfl

/-- A common nonzero pointwise scaling preserves and reflects equality of
all positive traces outside one finite set uniform in the power. -/
theorem samePowerTraces_scale_iff (a : I → ℂˣ)
    (s : SpectralSystem I n) (t : SpectralSystem I m) :
    (scale a s).SamePowerTraces (scale a t) ↔ s.SamePowerTraces t := by
  constructor
  · intro h
    exact h.mono fun v hv hs ht k hk =>
      mul_left_cancel₀ (pow_ne_zero k (Units.ne_zero (a v)))
        (by simpa only [scale_powerTrace] using hv hs ht k hk)
  · intro h
    apply h.mono
    intro v hv hs ht k hk
    calc
      (scale a s).powerTrace v hs k =
          (a v : ℂ) ^ k * s.powerTrace v hs k := scale_powerTrace _ _ _ _ _
      _ = (a v : ℂ) ^ k * t.powerTrace v ht k :=
        congrArg (fun z : ℂ => (a v : ℂ) ^ k * z) (hv hs ht k hk)
      _ = (scale a t).powerTrace v ht k := (scale_powerTrace _ _ _ _ _).symm

/-- Common pointwise scaling likewise preserves and reflects almost-everywhere
equality of Euler denominator polynomials, including systems of different ranks. -/
theorem sameEulerPolynomials_scale_iff (a : I → ℂˣ)
    (s : SpectralSystem I n) (t : SpectralSystem I m) :
    (scale a s).SameEulerPolynomials (scale a t) ↔ s.SameEulerPolynomials t := by
  constructor
  · intro h
    apply h.mono
    intro v hv hs ht
    apply Polynomial.ext
    intro i
    apply mul_left_cancel₀ (pow_ne_zero i (Units.ne_zero (a v)))
    simpa only [scale_eulerPolynomial_coeff] using
      congrArg (fun q : Polynomial ℂ => q.coeff i) (hv hs ht)
  · intro h
    apply h.mono
    intro v hv hs ht
    calc
      (scale a s).eulerPolynomial v hs =
          (s.eulerPolynomial v hs).comp (Polynomial.C (a v : ℂ) * Polynomial.X) :=
        scale_eulerPolynomial _ _ _ _
      _ = (t.eulerPolynomial v ht).comp (Polynomial.C (a v : ℂ) * Polynomial.X) :=
        congrArg (fun q : Polynomial ℂ =>
          q.comp (Polynomial.C (a v : ℂ) * Polynomial.X)) (hv hs ht)
      _ = (scale a t).eulerPolynomial v ht := (scale_eulerPolynomial _ _ _ _).symm

end Langlands.Unramified.SpectralSystem
