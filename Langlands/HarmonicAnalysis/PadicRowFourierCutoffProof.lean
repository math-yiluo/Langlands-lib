import Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Simultaneous normalized p-adic row Fourier cutoffs: proof

A compact open product subgroup `L = Sᵈ` of rows lies inside the prescribed
neighbourhood of zero, and the character of the row pairing is trivial on
`L × C`. The small cutoff is `κ = vol(L)⁻¹ · 1_L`, and the large cutoff is its
plus-sign row transform. Row inversion and the evenness of `κ` make the pair
`(Φ, κ)` a Fourier pair in the stated direction.
-/

noncomputable section

open MeasureTheory Topology Filter Set

namespace Langlands.HarmonicAnalysis

universe u

section Generic

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [NonarchimedeanAddGroup F] [LocallyCompactSpace F]

/-- A compact open additive subgroup `S` of the field whose product set `Sᵈ`
lies in a given neighbourhood of zero, with `ψ(rowPairing z x) = 1` for all
`z ∈ Sᵈ` and all `x` in a given compact set. -/
theorem exists_rowCutoffSubgroup (ψ : UnitaryAdditiveCharacter F) {d : ℕ}
    {C : Set (Fin d → F)} (hC : IsCompact C) {U : Set (Fin d → F)}
    (hU : U ∈ 𝓝 (0 : Fin d → F)) :
    ∃ S : OpenAddSubgroup F, IsCompact (S : Set F) ∧
      {z : Fin d → F | ∀ i, z i ∈ S} ⊆ U ∧
      ∀ z : Fin d → F, (∀ i, z i ∈ S) → ∀ x ∈ C, ψ.complex (rowPairing z x) = 1 := by
  classical
  have harc : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  let A : Set F := ψ.toAddChar ⁻¹' Circle.centeredArc (Real.pi / 2)
  have hA : IsOpen A := (Circle.isOpen_centeredArc _).preimage ψ.continuous_toFun
  have hcont : Continuous fun q : (Fin d → F) × (Fin d → F) => rowPairing q.1 q.2 :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hN : ∀ᶠ z in 𝓝 (0 : Fin d → F), ∀ x ∈ C, rowPairing z x ∈ A := by
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    refine hcont.continuousAt.preimage_mem_nhds (hA.mem_nhds ?_)
    change ψ.toAddChar (rowPairing 0 x) ∈ Circle.centeredArc (Real.pi / 2)
    simpa [rowPairing] using harc
  have hUN : U ∩ {z | ∀ x ∈ C, rowPairing z x ∈ A} ∈ 𝓝 (0 : Fin d → F) := inter_mem hU hN
  rw [nhds_pi, Filter.mem_pi] at hUN
  obtain ⟨I, -, t, ht, hIt⟩ := hUN
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : F)
  have hT : K ∩ ⋂ i, t i ∈ 𝓝 (0 : F) :=
    inter_mem hK0 (iInter_mem.mpr fun i => by simpa using ht i)
  obtain ⟨S, hS⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hT
  have hSU : ∀ z : Fin d → F, (∀ i, z i ∈ S) →
      z ∈ U ∩ {z | ∀ x ∈ C, rowPairing z x ∈ A} :=
    fun z hz => hIt fun i _ => mem_iInter.mp (hS (hz i)).2 i
  refine ⟨S, hKc.of_isClosed_subset S.isClosed fun x hx => (hS hx).1,
    fun z hz => (hSU z hz).1, ?_⟩
  intro z hz x hx
  have he : ψ.toAddChar (rowPairing z x) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    have hnz : ∀ i, (n • z) i ∈ S := fun i => nsmul_mem (hz i) n
    have h := (hSU (n • z) hnz).2 x hx
    have hp : rowPairing (n • z) x = n • rowPairing z x := by
      simp only [rowPairing, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum]
    rw [hp] at h
    change ψ.toAddChar (n • rowPairing z x) ∈ Circle.centeredArc (Real.pi / 2) at h
    rwa [AddChar.map_nsmul_eq_pow] at h
  change ((ψ.toAddChar (rowPairing z x) : Circle) : ℂ) = 1
  rw [he, Circle.coe_one]

variable [T2Space F] [MeasurableSpace F] [BorelSpace F] [TotallyDisconnectedSpace F]

/-- The cutoff pair for an arbitrary nonarchimedean locally compact field and a
supplied self-dual scalar Haar measure. -/
theorem exists_rowFourierCutoff (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (hsd : IsSelfDual ψ ν) {d : ℕ}
    {C : Set (Fin d → F)} (hC : IsCompact C) {U : Set (Fin d → F)} (hU : IsOpen U)
    (h0 : (0 : Fin d → F) ∈ U) :
    ∃ Φ κ : SchwartzBruhat (Fin d → F),
      IsRowFourierPair ψ ν Φ κ ∧
      (∀ x ∈ C, Φ x = 1) ∧
      Function.support ⇑κ ⊆ U ∧
      ∫ x, κ x ∂rowMeasure ν d = 1 ∧
      (∀ x, Φ (-x) = Φ x) ∧
      (∀ x, κ (-x) = κ x) := by
  classical
  have : SigmaFinite ν.measure := selfDualSigmaFinite F ψ ν hsd
  obtain ⟨hclosed, hinv⟩ := rowFourierCompatibility ψ ν d hsd
  obtain ⟨S, hSc, hSU, hSψ⟩ := exists_rowCutoffSubgroup ψ hC (hU.mem_nhds h0)
  let L : Set (Fin d → F) := Set.univ.pi fun _ => (S : Set F)
  have hmemL : ∀ z, z ∈ L ↔ ∀ i, z i ∈ S := fun z => Set.mem_univ_pi
  have hLo : IsOpen L := isOpen_set_pi Set.finite_univ fun _ _ => S.isOpen
  have hLcl : IsClosed L := isClosed_set_pi fun _ _ => S.isClosed
  have hLc : IsCompact L := isCompact_univ_pi fun _ => hSc
  have hLm : MeasurableSet L := MeasurableSet.univ_pi fun _ => S.isOpen.measurableSet
  have hLmeas : rowMeasure ν d L = ν.measure S ^ d := by
    have hLeq : L = {x : Fin d → F | ∀ i, x i ∈ (S : Set F)} := Set.ext hmemL
    rw [hLeq]
    exact rowMeasure_entries ν d S
  have hS0 : ν.measure S ≠ 0 := S.isOpen.measure_ne_zero ν.measure ⟨0, S.zero_mem⟩
  have hStop : ν.measure S ≠ ⊤ := hSc.measure_lt_top.ne
  set m : ℝ := (rowMeasure ν d).real L with hm
  have hmpos : 0 < m := by
    rw [hm, measureReal_def, hLmeas, ENNReal.toReal_pow]
    exact pow_pos (ENNReal.toReal_pos hS0 hStop) d
  let κ : SchwartzBruhat (Fin d → F) :=
    ((m : ℂ)⁻¹) • Hecke.TestFunction.characteristic ⟨hLcl, hLo⟩ hLc
  have hκ : (κ : (Fin d → F) → ℂ) = L.indicator fun _ => (m : ℂ)⁻¹ := by
    funext z
    change (m : ℂ)⁻¹ * L.indicator (fun _ => (1 : ℂ)) z = _
    by_cases hz : z ∈ L <;> simp [hz]
  have hκeven : ∀ x, κ (-x) = κ x := by
    intro x
    have hneg : -x ∈ L ↔ x ∈ L := by
      simp only [hmemL, Pi.neg_apply, neg_mem_iff]
    rw [hκ]
    by_cases hx : x ∈ L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hneg.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hneg.mp hx)]
  have hsupp : Function.support ⇑κ ⊆ U := by
    rw [hκ]
    exact Set.support_indicator_subset.trans fun z hz => hSU ((hmemL z).mp hz)
  have hint : ∫ x, κ x ∂rowMeasure ν d = 1 := by
    rw [hκ, integral_indicator_const _ hLm, ← hm, Complex.real_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hmpos.ne')]
  obtain ⟨Φ, hΦ⟩ := hclosed κ
  have hΦfun : (Φ : (Fin d → F) → ℂ) = rowFourierIntegral ψ ν d κ := funext hΦ
  have hpair : IsRowFourierPair ψ ν Φ κ := by
    intro y
    rw [hΦfun, (hinv κ).2 y, hκeven y]
  have hΦC : ∀ x ∈ C, Φ x = 1 := by
    intro x hx
    rw [hΦ x]
    unfold rowFourierIntegral
    have hfun : (fun z => ψ.complex (rowPairing z x) * κ z) = fun z => κ z := by
      funext z
      by_cases hz : z ∈ L
      · rw [hSψ z ((hmemL z).mp hz) x hx, one_mul]
      · rw [hκ, Set.indicator_of_notMem hz, mul_zero]
    rw [hfun, hint]
  have hΦeven : ∀ x, Φ (-x) = Φ x := by
    intro x
    have hκfun : (κ : (Fin d → F) → ℂ) = rowFourierIntegral ψ ν d Φ := funext hpair
    rw [← (hinv Φ).2 x, ← hκfun]
    exact (hΦ x).symm
  exact ⟨Φ, κ, hpair, hΦC, hsupp, hint, hΦeven, hκeven⟩

end Generic

/-- Simultaneous normalized row Fourier cutoffs for every supplied topology,
self-dual scalar Haar measure and dimension. -/
theorem padicRowFourierCutoff {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (d : ℕ) : PadicRowFourierCutoffStatement F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  have : NonarchimedeanAddGroup F.Carrier := rowFourierCutoff_nonarchimedean
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν hsd C hC U hU h0
  exact exists_rowFourierCutoff ψ ν hsd hC hU h0

end Langlands.HarmonicAnalysis
