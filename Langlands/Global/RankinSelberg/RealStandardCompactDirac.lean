import Langlands.Global.RankinSelberg.RealStandardCompactBanachAction
import Langlands.Representation.Archimedean.BanachModerateGrowth
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages

/-! # A quantitative compact Dirac limit for real scalar principal series -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac

open RealStandardCompactBanach RealPrincipalSeriesHilbert

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## The diagonal sign subgroup and its sign character -/

/-- The real unit `±1` of an integer sign. -/
def signUnit : ℤˣ →* ℝˣ := Units.map (Int.castRingHom ℝ : ℤ →* ℝ)

@[simp]
theorem coe_signUnit (e : ℤˣ) : ((signUnit e : ℝˣ) : ℝ) = ((e : ℤ) : ℝ) := rfl

theorem signUnit_mul_self (e : ℤˣ) : ((signUnit e : ℝˣ) : ℝ) * ((signUnit e : ℝˣ) : ℝ) = 1 := by
  rw [coe_signUnit, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one]

/-- The diagonal sign matrix `diag(ε₀, …, ε_{n-1})` as an orthogonal matrix. The range of this
homomorphism is the diagonal sign subgroup `M` of `O(n)`. -/
def signMatrix : (Fin n → ℤˣ) →* O where
  toFun ε := ⟨Matrix.diagonal fun i => ((signUnit (ε i) : ℝˣ) : ℝ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, star_trivial]
    exact signUnit_mul_self (ε i)⟩
  map_one' := by
    apply Subtype.ext
    simp only [Pi.one_apply, map_one, Units.val_one, Matrix.diagonal_one]
    rfl
  map_mul' ε ε' := by
    apply Subtype.ext
    simp only [Pi.mul_apply, map_mul, Units.val_mul, Submonoid.coe_mul,
      Matrix.diagonal_mul_diagonal]

@[simp]
theorem signMatrix_val (ε : Fin n → ℤˣ) :
    ((signMatrix ε : O) : Mat) = Matrix.diagonal fun i => ((signUnit (ε i) : ℝˣ) : ℝ) := rfl

/-- In the general linear group, the sign matrix is the diagonal unit matrix of the signs. -/
theorem toUnits_signMatrix (ε : Fin n → ℤˣ) :
    Unitary.toUnits (signMatrix ε) =
      (Iwasawa.diagonalUnits fun i => signUnit (ε i) : G) :=
  Units.ext rfl

/-- The sign character `χ(diag ε) = ∏ᵢ χᵢ(εᵢ)` of the diagonal sign subgroup, determined by
the position characters `χᵢ` of the blocks `ds`. -/
def signCharacter (ds : List RealBlock) (ε : Fin n → ℤˣ) : ℂ :=
  ∏ i : Fin n, realPositionCharacter ds i (signUnit (ε i))

/-- At a diagonal sign matrix the principal-series character is the sign character: the
modulus factor is one. -/
theorem principalSeriesCharacter_sign (ds : List RealBlock) (ε : Fin n → ℤˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (ε i)) =
      signCharacter ds ε := by
  unfold principalSeriesCharacter signCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : ‖((signUnit (ε i) : ℝˣ) : ℝ)‖ = 1 := by
    rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
  rw [h, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- The compact function of a real standard vector is covariant for the sign character on the
left. -/
theorem compactRestriction_signMatrix_mul (ds : List RealBlock) (f : realStandardModule n ds)
    (ε : Fin n → ℤˣ) (k : O) :
    compactRestriction ds f (signMatrix ε * k) = signCharacter ds ε * compactRestriction ds f k := by
  have h := f.property.1.2 (fun i => signUnit (ε i)) 1 (Unitary.toUnits k)
  rw [Subgroup.coe_one, mul_one, ← toUnits_signMatrix, ← map_mul,
    principalSeriesCharacter_sign] at h
  simpa only [compactRestriction_apply] using h

/-! ## Compatible Lipschitz tests and the Haar pairing -/

/-- A continuous test `ψ` on `O(n)` in the sign sector compatible with `ds`:
`ψ(m k) = χ(m)⁻¹ ψ(k)` for every diagonal sign matrix `m`. -/
def IsSignCompatible (ds : List RealBlock) (ψ : C(O, ℂ)) : Prop :=
  ∀ (ε : Fin n → ℤˣ) (k : O), ψ (signMatrix ε * k) = (signCharacter ds ε)⁻¹ * ψ k

/-- `L` is a Lipschitz constant of `ψ` for the distance `‖k - l‖` that `O(n)` inherits from the
row-sum operator norm of real matrices. -/
def IsMatrixLipschitz (L : ℝ) (ψ : C(O, ℂ)) : Prop :=
  ∀ k l : O, ‖ψ k - ψ l‖ ≤ L * ‖(k : Mat) - (l : Mat)‖

/-- The bilinear pairing `∫_{O(n)} φ(k) ψ(k) dk` for the Haar probability measure. -/
def haarPairing (φ ψ : C(O, ℂ)) : ℂ :=
  ∫ k, φ k * ψ k ∂haarOrthogonal n

/-- The compact function of `b R(g) f` for a smooth real standard vector `f`, in the compact
Banach completion of the real standard module. -/
def compactFunction (ds : List RealBlock) (b : ℂ) (g : G) (f : realStandardModule n ds) :
    C(O, ℂ) :=
  (b • RealStandardCompactBanach.representation ds g (embed ds f)).val

/-- The compact function of `b R(g) f` is `k ↦ b f(k g)`. -/
theorem compactFunction_apply (ds : List RealBlock) (b : ℂ) (g : G)
    (f : realStandardModule n ds) (k : O) :
    compactFunction ds b g f k = b * f.val (Unitary.toUnits k * g) := by
  simp only [compactFunction, Submodule.coe_smul, ContinuousMap.smul_apply, smul_eq_mul,
    RealStandardCompactBanach.representation_embed, embed_val, compactRestriction_apply,
    translate_apply]

/-! ## The statement -/

/-- **Quantitative compact Dirac limit.** For every `GL_{r+1}(ℝ)` and every list `cs` of
`r + 1` real character data, write `ds` for the list of character blocks of `cs`. There are a
compact-finite vector `ξ` of the real standard module of `ds`, constants `C > 0` and `δ > 0`,
an exponent `N`, positive diagonal entries `a t` and scalars `b t` such that for every
`t ≥ 1`: the group element `a_t = diag(a t)` has height at most `C t^N`, `‖b t‖ ≤ C t^N`, and
for every continuous test `ψ` on `O(r+1)` compatible with the sign character and every
Lipschitz constant `L ≥ 0` of `ψ` for the row-sum operator norm,
`|∫_{O(r+1)} b_t ξ(k a_t) ψ(k) dk - ψ(1)| ≤ C t^(-δ) (‖ψ‖∞ + L)`, the integral being the Haar
pairing of the compact function of `b_t R(a_t) ξ` with `ψ`. -/
def RealStandardCompactDiracStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData), cs.length = r + 1 →
    ∃ ξ : realStandardModule (r + 1) (cs.map RealBlock.character),
      ξ.val ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ))
        (unitaryCompact ℝ (r + 1)) ∧
      ∃ (C δ : ℝ) (N : ℕ), 0 < C ∧ 0 < δ ∧
        ∃ (a : ℝ → Fin (r + 1) → ℝˣ) (b : ℝ → ℂ), ∀ t : ℝ, 1 ≤ t →
          (∀ i, 0 < (a t i : ℝ)) ∧
          unitHeight (A := Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
              (Iwasawa.diagonalUnits (a t)) ≤ C * t ^ N ∧
          ‖b t‖ ≤ C * t ^ N ∧
          ∀ (ψ : C(Matrix.unitaryGroup (Fin (r + 1)) ℝ, ℂ)) (L : ℝ),
            IsSignCompatible (cs.map RealBlock.character) ψ → 0 ≤ L →
            IsMatrixLipschitz L ψ →
              ‖haarPairing (compactFunction (cs.map RealBlock.character) (b t)
                  (Iwasawa.diagonalUnits (a t)) ξ) ψ - ψ 1‖ ≤
                C * t ^ (-δ) * (‖ψ‖ + L)

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac
