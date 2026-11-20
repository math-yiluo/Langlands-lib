import Langlands.BushnellKutzko.ConductorFormula
import Langlands.BushnellKutzko.ConductorBridge
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationProof
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # The Swan conductor and the normalized level in rank at least two

For an irreducible supercuspidal class `π` of `GL_{n+1}(K)` with `n ≥ 1` and normalized level
`x`, the first fixed level of `π` is a natural number `c` with `c - (n + 1) = (n + 1) x`
(truncated subtraction): `exists_firstFixedLevel_eq_of_isNormalizedLevel`. This is T2 in rank
at least two.

The proof chooses an additive character `ψ` of conductor `𝔬_K` and a self-dual measure, takes
the Godement–Jacquet functional-equation data of a representative of `π` from the Library, and
combines the exponent formula `max_exponent_eq_of_isNormalizedLevel` (module
`ConductorFormula`) with bridge B `exists_exponent_eq_firstFixedLevel` (module
`ConductorBridge`).
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis

namespace Langlands.BushnellKutzko

universe uK uV

section Padic

local instance slrTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance slrValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance slrLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance slrT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance slrDisconnected {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance slrMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance slrBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The truncated difference `c - N` from `max(c, N) = N (1 + x)`. -/
theorem natSub_eq_of_max_eq {c N : ℕ} {x : ℚ} (h : max (c : ℚ) N = N * (1 + x)) :
    ((c - N : ℕ) : ℚ) = (N : ℚ) * x := by
  rcases le_total c N with hcN | hNc
  · rw [Nat.sub_eq_zero_of_le hcN, Nat.cast_zero]
    have : (c : ℚ) ≤ N := by exact_mod_cast hcN
    rw [max_eq_right this] at h
    linarith
  · rw [Nat.cast_sub hNc]
    have : (N : ℚ) ≤ c := by exact_mod_cast hNc
    rw [max_eq_left this] at h
    linarith

/-- **T2 in rank at least two.** Let `n ≥ 1` and `π` an irreducible supercuspidal class of
`GL_{n+1}(K)` with normalized level `x`. Then the first fixed level of `π` is a natural number
`c`, and `c - (n + 1) = (n + 1) x` (truncated subtraction). -/
theorem exists_firstFixedLevel_eq_of_isNormalizedLevel {n : ℕ} (hn : 0 < n)
    (π : GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := n + 1)) {x : ℚ}
    (hlev : IsNormalizedLevel K (n + 1) (GeneralLinear.SupercuspidalClass.toSmoothDualClass π)
      x) :
    ∃ c : ℕ, GeneralLinear.SupercuspidalClass.firstFixedLevel π = (c : WithTop ℕ) ∧
      ((c - (n + 1) : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) * x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨ψ₀⟩ := padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨u, hψ⟩ := RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor K ψ₀
  obtain ⟨ν⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar K (ψ₀.scale u)
  obtain ⟨c, a, hFE⟩ := GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData
    K hn (ψ₀.scale u) ν.1 ν.2 A.obj.representation A.property.2 A.property.1
  have hmax := max_exponent_eq_of_isNormalizedLevel K (ψ₀.scale u) hψ ν.1 ν.2 A c a hFE hlev
  obtain ⟨m, hm, hfl⟩ := exists_exponent_eq_firstFixedLevel K (ψ₀.scale u) hψ ν.1 ν.2 hn A c a
    hFE
  refine ⟨m, hfl, ?_⟩
  apply natSub_eq_of_max_eq
  rw [hm] at hmax
  push_cast
  exact hmax

end Padic

end Langlands.BushnellKutzko
