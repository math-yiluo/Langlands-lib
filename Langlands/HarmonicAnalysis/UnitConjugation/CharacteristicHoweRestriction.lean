import Langlands.HarmonicAnalysis.UnitConjugation.CharacteristicExhaustion

/-! # Conic restriction after enlarging the frequency lattice -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function _root_.Topology

section Cosets

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

private theorem vanishing_latticeCosetTest_of_le {L M : AddSubgroup A} (hLM : L ≤ M)
    (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A))
    (hMo : IsOpen (M : Set A)) (hMc : IsCompact (M : Set A))
    (T : Distribution A) (x : A) (hT : ∀ l ∈ M, T (latticeCosetTest L hLo hLc (x + l)) = 0) :
    T (latticeCosetTest M hMo hMc x) = 0 := by
  classical
  let gx := latticeCosetTest M hMo hMc x
  let χ : LocallyConstant A ℂ := ⟨gx, gx.locallyConstant⟩
  let m := Distribution.multiplyTest χ
  let W := LinearMap.ker (T.comp m)
  let π := QuotientAddGroup.mk' L
  let Q := QuotientAddGroup.mk' M
  have hQM {y z : A} (hyz : π z = π y) : Q z = Q y := by
    obtain ⟨l, hl, rfl⟩ := (QuotientAddGroup.mk'_eq_mk' L).mp hyz.symm
    exact ((QuotientAddGroup.mk'_eq_mk' M).mpr ⟨l, hLM hl, rfl⟩).symm
  have hScale (y : A) : m (latticeCosetTest L hLo hLc y) = χ y • latticeCosetTest L hLo hLc y := by
    apply Hecke.TestFunction.ext
    intro z
    rw [Distribution.multiplyTest_apply]
    change χ z * latticeCosetTest L hLo hLc y z = χ y * latticeCosetTest L hLo hLc y z
    rw [latticeCosetTest_apply]
    by_cases hz : π z = π y
    · have h := hQM hz
      have hχ : χ z = χ y := by
        change gx z = gx y
        simp only [gx, latticeCosetTest_apply, show QuotientAddGroup.mk' M = Q from rfl, h]
      rw [hχ]
    · simp only [show QuotientAddGroup.mk' L = π from rfl, ite_eq_right hz, mul_zero]
  have hKer : latticeInvariantTests L ≤ W := by
    rw [← latticeCosetSpan L hLo hLc]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change T (m (latticeCosetTest L hLo hLc y)) = 0
    rw [hScale, map_smul]
    by_cases hy : Q y = Q x
    · obtain ⟨l, hl, rfl⟩ := (QuotientAddGroup.mk'_eq_mk' M).mp hy.symm
      rw [hT l hl, smul_zero]
    · have h : χ y = 0 := by
        change gx y = 0
        simp only [gx, latticeCosetTest_apply, show QuotientAddGroup.mk' M = Q from rfl, ite_eq_right hy]
      rw [h, zero_smul]
  have hG : gx ∈ latticeInvariantTests L :=
    fun l hl z => latticeCosetTest_mem M hMo hMc x l (hLM hl) z
  have hM : m gx = gx := by
    apply Hecke.TestFunction.ext
    intro z
    rw [Distribution.multiplyTest_apply]
    change gx z * gx z = gx z
    dsimp only [gx]
    rw [latticeCosetTest_apply]
    split_ifs <;> simp
  have h := hKer hG
  change T (m gx) = 0 at h
  rwa [hM] at h

end Cosets

section Restriction

variable {F A : Type*} [NontriviallyNormedField F] [NormedRing A] [NormedAlgebra F A]
  [FiniteDimensional F A] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace A] [IsUltrametricDist A]

/-- Finite dimensionality of the conic vanishing restrictions on arbitrarily
large compact open lattices, for a single positive cone parameter. -/
def CharacteristicConicFiniteness (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] : Prop :=
  ∃ δ > (0 : ℝ), ∀ (L : AddSubgroup A), IsOpen (L : Set A) → IsCompact (L : Set A) →
    ∃ (M : AddSubgroup A) (hMo : IsOpen (M : Set A)) (hMc : IsCompact (M : Set A)), L ≤ M ∧
      ∀ b > (0 : ℝ),
        let B := {x : A | b < ‖x‖ ∧ x ∉ characteristicCone F δ}
        FiniteDimensional ℂ ((vanishingOnLatticeCosets M hMo hMc B).map (restrictToLatticeTests M))

/-- A distribution with large-center vanishing outside the characteristic cone
agrees on the enlarged lattice with a compact-conjugacy-supported distribution. -/
def CharacteristicHoweRestrictionStatement (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (d : F) : Prop :=
  (∃ ω : Set A, IsCompact ω ∧ {x | characteristicSize F x ≤ 1} ⊆ conjugationSaturation ω) →
  CharacteristicConicFiniteness (A := A) F → 1 < ‖d‖ →
  ∃ δ > (0 : ℝ), ∀ (L : AddSubgroup A) (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A)),
    ∀ T : Distribution A, IsConjugationInvariant T →
      (∃ b > (0 : ℝ), ∀ x : A, b < ‖x‖ → x ∉ characteristicCone F δ →
        T (latticeCosetTest L hLo hLc x) = 0) →
      ∃ (M : AddSubgroup A) (_ : IsOpen (M : Set A)) (_ : IsCompact (M : Set A)), L ≤ M ∧
        ∃ (ω : Set A) (T' : Distribution A), IsCompact ω ∧ T' ∈ invariantSupportedIn ω ∧
          restrictToLatticeTests M T' = restrictToLatticeTests M T

set_option maxHeartbeats 1900000 in
theorem characteristicHoweRestriction (d : F) : CharacteristicHoweRestrictionStatement (A := A) F d := by
  intro hUnit hFiniteness hd
  obtain ⟨δ, hδ, hEnlarge⟩ := hFiniteness
  refine ⟨δ, hδ, fun L hLo hLc T hInv hVan => ?_⟩
  obtain ⟨M, hMo, hMc, hLM, hFin⟩ := hEnlarge L hLo hLc
  obtain ⟨b₀, hb₀, h₀⟩ := hVan
  obtain ⟨b₁, _, hConst⟩ := largeCharacteristicCoset (A := A) d δ hd hδ M hMc
  obtain ⟨b₂, _, hCut⟩ := characteristicExhaustion (A := A) d δ hUnit hd hδ M hMo hMc
  let b := max b₀ (max b₁ b₂)
  have hb : 0 < b := hb₀.trans_le (le_max_left _ _)
  let B := {x : A | b < ‖x‖ ∧ x ∉ characteristicCone F δ}
  have hTVan : T ∈ vanishingOnLatticeCosets M hMo hMc B := by
    apply (mem_vanishingOnLatticeCosets M hMo hMc B T).mpr
    refine ⟨hInv, fun x hx => vanishing_latticeCosetTest_of_le hLM hLo hLc hMo hMc T x ?_⟩
    intro l hl
    obtain ⟨hnorm, hφ⟩ := hConst x (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx.1) hx.2 l hl
    apply h₀ (x + l)
    · rw [hnorm]
      exact (le_max_left _ _).trans_lt hx.1
    · change ¬ (characteristicSize F (x + l) : ℝ) < δ * ‖x + l‖
      rw [hφ, hnorm]
      exact hx.2
  exact ⟨M, hMo, hMc, hLM, hCut b ((le_max_right _ _).trans (le_max_right _ _)) (hFin b hb) T hTVan⟩

end Restriction

end Langlands.HarmonicAnalysis.UnitConjugation
