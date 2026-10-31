import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonLatticeFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
import Langlands.HarmonicAnalysis.PadicLatticeHaarProof
import Langlands.LocalField.Normalization.Proof

/-! The actual Fourier transform of the rank-one comparison box. -/

noncomputable section

open MeasureTheory
open scoped BigOperators WithZero

namespace Langlands.RankinSelberg.RankOneBox

open HarmonicAnalysis UnequalRankMirabolicUnitTest

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

/-- The actual maximal-ideal power used by the published box is precisely the
negative-index valuation lattice. -/
theorem levelSet_eq_additiveLattice (a : ℕ) :
    levelSet F.Carrier a = (𝓛 (-(a : ℤ)) : Set F.Carrier) := by
  have hv : F.canonicalTopologicalData.discreteValuation.Integers F.canonicalTopologicalData.Integers := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      exact (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one x.val).1 x.property
    · intro x hx
      exact ⟨⟨x, (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one x).2 hx⟩, rfl⟩
  let π : F.canonicalTopologicalData.Integers := ⟨F.canonicalTopologicalData.uniformizer,
    (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one _).2 (by
      rw [F.canonicalTopologicalData.discreteValuation_uniformizer]
      norm_num)⟩
  have hπ : F.canonicalTopologicalData.discreteValuation (π : F.Carrier) = WithZero.exp (-1) :=
    F.canonicalTopologicalData.discreteValuation_uniformizer
  have hm : IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers = Ideal.span {π} := by
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one,
      ← SetLike.mem_coe, hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    change F.canonicalTopologicalData.discreteValuation x.val ≠ 1 ↔
      F.canonicalTopologicalData.discreteValuation x.val ≤ F.canonicalTopologicalData.discreteValuation (π : F.Carrier)
    rw [hπ]
    have hle := hv.map_le_one x
    have hstep : F.canonicalTopologicalData.discreteValuation x.val < 1 ↔
        F.canonicalTopologicalData.discreteValuation x.val ≤ WithZero.exp (-1) := by
      simpa [← WithZero.exp_add] using
        (WithZero.lt_mul_exp_iff_le (x := F.canonicalTopologicalData.discreteValuation x.val)
          (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
    rw [← hstep]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩
  have hp : ((IsLocalRing.maximalIdeal F.canonicalTopologicalData.Integers ^ a : Ideal F.canonicalTopologicalData.Integers) :
      Set F.canonicalTopologicalData.Integers) = {y : F.canonicalTopologicalData.Integers | F.canonicalTopologicalData.discreteValuation (y : F.Carrier) ≤ WithZero.exp (-(a : ℤ))} := by
    rw [hm, Ideal.span_singleton_pow,
      hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    change {y : F.canonicalTopologicalData.Integers | F.canonicalTopologicalData.discreteValuation (y : F.Carrier) ≤
      F.canonicalTopologicalData.discreteValuation ((π : F.Carrier) ^ a)} = _
    simp only [map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Set.ext_iff.1 hp y).1 hy
  · intro hx
    have hxO : x ∈ F.canonicalTopologicalData.Integers :=
      (F.canonicalTopologicalData.mem_additiveLattice_zero x).1 (F.canonicalTopologicalData.additiveLattice_mono (by omega) hx)
    refine ⟨⟨x, hxO⟩, ?_, rfl⟩
    exact (Set.ext_iff.1 hp ⟨x, hxO⟩).2 hx

/-- Independent lattice levels of the existing comparison box. -/
def boxLatticeLevels {n : ℕ} (A q : ℤ) (a : ℕ)
    (i j : Fin (n + 1)) : ℤ :=
  if i = 0 then (if j = 0 then A else q) else -(a : ℤ)

/-- The comparison box has centre zero in its first row and the identity in
all remaining rows. -/
def boxLatticeCentre (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier :=
  fun i j => if i = 0 then 0 else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j

/-- Identification of the actual published box as an entrywise affine lattice
coset; this is an equality of subsets of the full matrix space. -/
theorem box_eq_rectangularLatticeCoset {n : ℕ} (A q : ℤ) (a : ℕ) :
    box F (n := n) A q a = rectangularLatticeCoset F T
      (boxLatticeLevels A q a) (boxLatticeCentre F n) := by
  ext X
  rw [mem_rectangularLatticeCoset]
  change (∀ i j, X i j ∈ boxEntry F A q a i j) ↔ _
  simp only [boxEntry, boxLatticeLevels, boxLatticeCentre, levelSet_eq_additiveLattice]
  constructor <;> intro h i j
  all_goals
    specialize h i j
    split_ifs at h ⊢ <;> simpa only [sub_zero, Set.mem_ofPred_eq, SetLike.mem_coe] using h

/-- The original comparison box test, expressed through its actual lattice
coset rather than through an unspecified Fourier partner. -/
def boxLatticeTest {n : ℕ} (A q : ℤ) (a : ℕ) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  rectangularLatticeCosetTest F T (boxLatticeLevels A q a) (boxLatticeCentre F n)

@[simp] theorem boxLatticeTest_apply {n : ℕ} (A q : ℤ) (a : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    boxLatticeTest F A q a X = (box F A q a).indicator (fun _ => (1 : ℂ)) X := by
  rw [boxLatticeTest, rectangularLatticeCosetTest_apply, ← box_eq_rectangularLatticeCoset]

/-- This is exactly the compact-open indicator in the existing box-integral
proof, as a Schwartz test on all matrices. -/
theorem boxLatticeTest_eq_compactOpenIndicator {n : ℕ} (A q : ℤ) (a : ℕ) :
    boxLatticeTest F (n := n) A q a =
      compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a) := by
  ext X
  rw [boxLatticeTest_apply, coe_compactOpenIndicator]

/-- The centre phase of the box is its trailing diagonal sum. -/
theorem rectangularPairing_boxLatticeCentre {n : ℕ}
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    rectangularPairing (boxLatticeCentre F n) Y = ∑ i : Fin n, Y i.succ i.succ := by
  unfold rectangularPairing
  rw [Fin.sum_univ_succ]
  simp [boxLatticeCentre, Matrix.one_apply, Fin.succ_ne_zero]

/-- The genuine dual support of the comparison box. -/
def boxFourierSupport {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (A q : ℤ) (a : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  {Y | Y 0 0 ∈ 𝓛 (F.canonicalTopologicalData.additiveConductor ψ - A) ∧
    (∀ j, j ≠ 0 → Y 0 j ∈ 𝓛 (F.canonicalTopologicalData.additiveConductor ψ - q)) ∧
    ∀ i, i ≠ 0 → ∀ j, Y i j ∈ 𝓛 (F.canonicalTopologicalData.additiveConductor ψ + a)}

theorem boxFourierSupport_eq_rectangularLatticeCoset {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (A q : ℤ) (a : ℕ) :
    boxFourierSupport F (n := n) ψ A q a = rectangularLatticeCoset F T
      (fun i j => F.canonicalTopologicalData.additiveConductor ψ - boxLatticeLevels A q a i j) 0 := by
  ext Y
  rw [mem_rectangularLatticeCoset]
  simp only [Matrix.zero_apply, sub_zero]
  change (_ ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨h00, h0j, hij⟩ i j
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        simpa [boxLatticeLevels] using h00
      · simpa [boxLatticeLevels, hj] using h0j j hj
    · simpa [boxLatticeLevels, hi] using hij i hi j
  · intro h
    refine ⟨?_, fun j hj => ?_, fun i hi j => ?_⟩
    · simpa [boxLatticeLevels] using h 0 0
    · simpa [boxLatticeLevels, hj] using h 0 j
    · simpa [boxLatticeLevels, hi] using h i j

/-- The full plus Fourier integral of the actual box used by the published
rank-one integral extraction. No normalization of the supplied Haar is used. -/
theorem boxLatticeTest_fourierIntegral {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (A q : ℤ) (a : ℕ) (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    rectangularFourierIntegral ψ ν (boxLatticeTest F A q a) Y =
      rectangularLatticeVolume F T ν (boxLatticeLevels (n := n) A q a) *
        ψ.complex (∑ i : Fin n, Y i.succ i.succ) *
        (boxFourierSupport F ψ A q a).indicator (fun _ => (1 : ℂ)) Y := by
  rw [boxLatticeTest, rectangularLatticeCoset_fourierIntegral,
    rectangularPairing_boxLatticeCentre, ← boxFourierSupport_eq_rectangularLatticeCoset]

/-- Every actual Fourier partner of this test has the computed formula on all
matrices, including singular matrices. -/
theorem boxLatticeTest_fourierPartner {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (A q : ℤ) (a : ℕ)
    (ΦHat : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hpair : GodementJacquet.MatrixFourierPair ψ ν (boxLatticeTest F A q a) ΦHat)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    ΦHat Y = rectangularLatticeVolume F T ν (boxLatticeLevels (n := n) A q a) *
      ψ.complex (∑ i : Fin n, Y i.succ i.succ) *
        (boxFourierSupport F ψ A q a).indicator (fun _ => (1 : ℂ)) Y :=
  (hpair Y).2.trans (boxLatticeTest_fourierIntegral F ψ ν A q a Y)

end Langlands.RankinSelberg.RankOneBox
