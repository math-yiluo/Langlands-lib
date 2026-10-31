import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.Topology.CompactNormCharacter
import Langlands.Representation.Whittaker.Iwasawa

/-! # Compact and finite-order symmetries in actual matrix Fourier tests -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.HarmonicAnalysis

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {r s : ℕ}

/-- Actual rectangular Schwartz tests invariant under left multiplication by
every element of the specified matrix subgroup. -/
def rectangularLeftInvariantTests (J : Subgroup (GeneralLinear r K)) :
    Submodule ℂ (SchwartzBruhat (Matrix (Fin r) (Fin s) K)) where
  carrier := {Φ | ∀ g ∈ J, ∀ Y, Φ (g.val * Y) = Φ Y}
  zero_mem' := by simp
  add_mem' := by
    intro Φ Ψ hΦ hΨ g hg Y
    change Φ (g.val * Y) + Ψ (g.val * Y) = Φ Y + Ψ Y
    rw [hΦ g hg, hΨ g hg]
  smul_mem' := by
    intro c Φ hΦ g hg Y
    change c * Φ (g.val * Y) = c * Φ Y
    rw [hΦ g hg]

omit [IsTopologicalRing K] in
@[simp] theorem mem_rectangularLeftInvariantTests
    (J : Subgroup (GeneralLinear r K))
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    Φ ∈ rectangularLeftInvariantTests J ↔
      ∀ g ∈ J, ∀ Y, Φ (g.val * Y) = Φ Y := Iff.rfl

end Langlands.HarmonicAnalysis

namespace Langlands.PadicField.TopologicalData

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A finite-order matrix has determinant norm one. -/
theorem determinantNorm_eq_one_of_pow_eq_one {r m : ℕ}
    (g : GeneralLinear r F.Carrier) (hm : m ≠ 0) (hg : g ^ m = 1) :
    T.determinantNorm r g = 1 := by
  apply Units.ext
  apply (pow_eq_one_iff_of_nonneg
    (show (0 : ℝ≥0) ≤ (T.determinantNorm r g : ℝ≥0) from zero_le) hm).mp
  have h := congrArg (fun a => (T.determinantNorm r a : ℝ≥0)) hg
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using h

/-- Every actual permutation matrix has determinant norm one. -/
theorem determinantNorm_permutation (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    T.determinantNorm r (GeneralLinear.permutation r F.Carrier σ) = 1 := by
  apply T.determinantNorm_eq_one_of_pow_eq_one _
    (Nat.ne_zero_of_lt (orderOf_pos σ))
  rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- The unsigned long Weyl representative has determinant norm one. -/
theorem determinantNorm_weylLong (r : ℕ) :
    T.determinantNorm r (GeneralLinear.weylLong r F.Carrier) = 1 :=
  T.determinantNorm_permutation r Fin.revPerm

/-- Coordinate sign diagonals have determinant norm one in every rank. -/
theorem determinantNorm_signDiagonal {r : ℕ} (ε : Fin r → F.Carrierˣ)
    (hε : ∀ i, ε i ^ 2 = 1) :
    T.determinantNorm r (GeneralLinear.Iwasawa.diagonalUnits ε) = 1 := by
  apply T.determinantNorm_eq_one_of_pow_eq_one _ (by decide : 2 ≠ 0)
  rw [← map_pow]
  have he : ε ^ 2 = 1 := by
    funext i
    exact hε i
  rw [he, map_one]

end Langlands.PadicField.TopologicalData

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uF

/-- A left-right symmetry of a test transfers to the corresponding
inverse-transpose symmetry of its actual full Fourier partner. -/
theorem padicMatrixFourierPair_leftRight_invariant
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (A B : GeneralLinear (n + 1) F.Carrier),
      T.determinantNorm (n + 1) A = 1 → T.determinantNorm (n + 1) B = 1 →
      ∀ Φ ΦHat : MatrixTestFunction n F.Carrier,
      MatrixFourierPair ψ ν Φ ΦHat →
      (∀ Y, Φ (A.val * Y * B.val) = Φ Y) →
      ∀ X, ΦHat ((GeneralLinear.inverseTranspose (n + 1) F.Carrier A).val * X *
        (GeneralLinear.inverseTranspose (n + 1) F.Carrier B).val) = ΦHat X := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro ψ ν A B hA hB Φ ΦHat hpair hinv X
  calc
    _ = rectangularFourierIntegral ψ ν Φ _ := (hpair _).2
    _ = rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X :=
      (padicRectangularFourierIntegral_leftRight F T (n + 1) (n + 1)
        ψ ν A B hA hB Φ X).symm
    _ = rectangularFourierIntegral ψ ν Φ X := by
      congr 1
      funext Y
      exact hinv Y
    _ = _ := (hpair X).2.symm

/-- Left invariance under a compact subgroup becomes left invariance of the
Fourier partner under its actual inverse-transpose image. -/
theorem padicMatrixFourierPair_compact_left_invariant
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (J : Subgroup (GeneralLinear (n + 1) F.Carrier)),
      IsCompact (J : Set (GeneralLinear (n + 1) F.Carrier)) →
      ∀ Φ ΦHat : MatrixTestFunction n F.Carrier,
      MatrixFourierPair ψ ν Φ ΦHat →
      Φ ∈ rectangularLeftInvariantTests J →
      ΦHat ∈ rectangularLeftInvariantTests
        (J.map (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro ψ ν J hJ Φ ΦHat hpair hinv
  rintro A ⟨g, hg, rfl⟩ X
  have h := padicMatrixFourierPair_leftRight_invariant F T n ψ ν g 1
    (T.determinantNorm_eq_one_of_mem_compact (n + 1) J hJ g hg)
    (map_one _) Φ ΦHat hpair (by
      intro Y
      simpa only [Units.val_one, Matrix.mul_one] using hinv g hg Y) X
  simpa only [map_one, Units.val_one, Matrix.mul_one, MulEquiv.coe_toMonoidHom] using h

end Langlands.GodementJacquet
