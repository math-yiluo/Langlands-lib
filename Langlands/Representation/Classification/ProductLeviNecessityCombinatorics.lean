import Langlands.Representation.Classification.ProductLeviChamberBoundProof
import Langlands.Representation.Exponents.RealPartExistence

/-!
# Reduction of the refined chamber bound to test elements

A character of the refined split centre with open kernel satisfies `|ψ(a)| ≤ 1`
on the whole chamber increasing separately inside each outer block, once it
satisfies this bound on the test elements: the uniformizer on an initial segment
of refined blocks of one outer block, and the inverse uniformizer on all refined
blocks of one outer block.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.ProductLeviNecessity

open GeneralLinear Geometric ProductLeviChamber

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- The uniformizer power `ϖ ^ e` on the refined blocks of index below `k` of the
outer block `j`, and `1` elsewhere. -/
def testScalars (j : Fin C.length) (k : ℕ) (e : ℤ) : ∀ i, Fin (D i).length → F.Carrierˣ :=
  fun i l => if i = j ∧ l.val < k then LocalFactor.PadicAbelian.uniformizerUnit T ^ e else 1

theorem logAbs_uniformizerUnit_zpow (e : ℤ) :
    T.logAbs (LocalFactor.PadicAbelian.uniformizerUnit T ^ e) = -e := by
  simp only [PadicField.TopologicalData.logAbs, Units.val_zpow_eq_zpow_val,
    LocalFactor.PadicAbelian.uniformizerUnit_coe, T.ord_zpow, T.ord_uniformizer, mul_one]

/-- The pairing of a real vector with the H-map, as a sum over outer blocks and
refined blocks. -/
theorem sum_centreHMap_blocks (x : Fin (C.flatten D).length → ℝ)
    (a : Fin (C.flatten D).length → F.Carrierˣ) :
    ∑ y, x y * (T.centreHMap a y : ℝ) =
      ∑ i, ∑ l, x (C.flattenBlockEquiv D ⟨i, l⟩) *
        (T.logAbs (a (C.flattenBlockEquiv D ⟨i, l⟩)) : ℝ) := by
  rw [← (C.flattenBlockEquiv D).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [PadicField.TopologicalData.centreHMap_apply]

/-- The pairing of a real vector with the H-map of a flattened nested tuple, as a
sum over outer blocks and refined blocks. -/
theorem sum_centreHMap_flatScalars (x : Fin (C.flatten D).length → ℝ)
    (c : ∀ i, Fin (D i).length → F.Carrierˣ) :
    ∑ y, x y * (T.centreHMap (flatScalars C D c) y : ℝ) =
      ∑ i, ∑ l, x (C.flattenBlockEquiv D ⟨i, l⟩) * (T.logAbs (c i l) : ℝ) := by
  rw [← (C.flattenBlockEquiv D).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [PadicField.TopologicalData.centreHMap_apply, flatScalars_apply]

theorem sum_centreHMap_testScalars (x : Fin (C.flatten D).length → ℝ) (j : Fin C.length)
    (k : ℕ) (e : ℤ) :
    ∑ y, x y * (T.centreHMap (flatScalars C D (testScalars T C D j k e)) y : ℝ) =
      -(e : ℝ) * Exponents.partialSum (fun l => x (C.flattenBlockEquiv D ⟨j, l⟩)) k := by
  classical
  rw [sum_centreHMap_flatScalars, Finset.sum_eq_single j]
  · rw [Exponents.partialSum, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [testScalars, true_and]
    split_ifs
    · rw [logAbs_uniformizerUnit_zpow]
      push_cast
      ring
    · rw [PadicField.TopologicalData.logAbs_one]
      simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [testScalars, hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The test-element bounds give the chamber bound. -/
theorem norm_le_one_of_test (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ)
    (hψ : letI := T.topology; IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)))
    (htest : ∀ j k, 0 < k → k ≤ (D j).length →
      ‖(ψ (flatScalars C D (testScalars T C D j k 1)) : ℂ)‖ ≤ 1)
    (htest' : ∀ j,
      ‖(ψ (flatScalars C D (testScalars T C D j (D j).length (-1))) : ℂ)‖ ≤ 1)
    (a : Fin (C.flatten D).length → F.Carrierˣ)
    (ha : ∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
      T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) :
    ‖(ψ a : ℂ)‖ ≤ 1 := by
  obtain ⟨x, hx⟩ := T.exists_isRealPartOf ψ hψ
  rw [PadicField.TopologicalData.isRealPartOf_iff_pairing] at hx
  have hq := T.one_lt_residueCardinality_real
  have hle : ∀ s : ℝ, (T.residueCardinality : ℝ) ^ s ≤ 1 ↔ s ≤ 0 := by
    intro s
    conv_lhs => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
    exact Real.rpow_le_rpow_left_iff hq
  have hcone : ∀ j, Exponents.IsClosedPositiveRootCone
      (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩)) := by
    intro j
    have hval : ∀ k e, ‖(ψ (flatScalars C D (testScalars T C D j k e)) : ℂ)‖ ≤ 1 →
        -(e : ℝ) * Exponents.partialSum (fun l => x (C.flattenBlockEquiv D ⟨j, l⟩)) k ≤ 0 := by
      intro k e h
      rwa [hx, sum_centreHMap_testScalars, hle] at h
    have hfull : Exponents.partialSum (fun l : Fin (D j).length =>
        x (C.flattenBlockEquiv D ⟨j, l⟩)) (D j).length =
          ∑ l, x (C.flattenBlockEquiv D ⟨j, l⟩) := by
      rw [Exponents.partialSum]
      congr 1
      exact Finset.filter_true_of_mem fun l _ => l.isLt
    have hpos := C.positive j
    have hlen : 0 < (D j).length := Fin.pos ((D j).indexEquiv.symm ⟨0, hpos⟩).1
    refine ⟨?_, fun k hk hkL => ?_⟩
    · have h1 := hval _ 1 (htest j _ hlen le_rfl)
      have h2 := hval _ (-1) (htest' j)
      rw [hfull] at h1 h2
      push_cast at h1 h2
      linarith
    · have h1 := hval k 1 (htest j k hk hkL.le)
      push_cast at h1
      linarith
  rw [hx, hle, sum_centreHMap_blocks]
  refine Finset.sum_nonpos fun j _ => ?_
  have hmono : Monotone (fun l : Fin (D j).length =>
      T.logAbs (a (C.flattenBlockEquiv D ⟨j, l⟩))) :=
    fun l l' hll' => (T.logAbs_le_logAbs_iff _ _).mpr (ha j hll')
  exact ((Exponents.isClosedPositiveRootCone_iff_pairing _).mp (hcone j)).2 _ hmono

end Langlands.ProductLeviNecessity
