import Langlands.HarmonicAnalysis.Bicharacter.CompactOpenDuality
import Langlands.HarmonicAnalysis.UnitConjugation.LatticeCharacterOrbit

/-! # The finite character sum of a lattice level -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set Function

variable {A : Type*} [Ring A] [TopologicalSpace A]
  {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
  (L N : AddSubgroup A)

/-- Restrict the character defined by an ambient frequency to a lattice. -/
def latticeAddCharHom : A →+ AddChar L ℂ where
  toFun := latticeAddChar he L
  map_zero' := AddChar.ext _ _ fun x => he.map_zero_right x.val
  map_add' a b := AddChar.ext _ _ fun x => he.map_add_right x.val a b

/-- The group of restricted characters obtained from the annihilator of the level. -/
def latticeLevelCharacters : AddSubgroup (AddChar L ℂ) :=
  (he.annihilator (N : Set A)).map (latticeAddCharHom he L)

theorem mem_latticeLevelCharacters_iff (χ : AddChar L ℂ) :
    χ ∈ latticeLevelCharacters he L N ↔
      ∃ z ∈ he.annihilator (N : Set A), latticeAddChar he L z = χ := Iff.rfl

section Finite

variable [IsTopologicalAddGroup A]

/-- The restrictions to a compact additive subgroup of the annihilator of a
compact open lattice form a finite group. -/
theorem latticeLevelCharacters_finite (hLc : IsCompact (L : Set A))
    (hNo : IsOpen (N : Set A)) (hNc : IsCompact (N : Set A)) :
    (latticeLevelCharacters he L N : Set (AddChar L ℂ)).Finite := by
  let D := he.annihilator (L : Set A)
  let B := he.annihilator (N : Set A)
  let q := QuotientAddGroup.mk' D
  let : DiscreteTopology (A ⧸ D) :=
    QuotientAddGroup.discreteTopology_iff.mpr (he.isOpen_annihilator hLc)
  have hker : D ≤ (latticeAddCharHom he L).ker := by
    intro z hz
    change latticeAddChar he L z = 0
    rw [← show latticeAddChar he L 0 = 0 from (latticeAddCharHom he L).map_zero,
      latticeAddChar_eq_iff, sub_zero]
    exact hz
  let c := QuotientAddGroup.lift D (latticeAddCharHom he L) hker
  have hBc : IsCompact (B : Set A) := he.isCompact_annihilator_compactOpen N hNo hNc
  have hQ := (hBc.image (QuotientAddGroup.continuous_mk (N := D))).finite_of_discrete
  have hR : (latticeLevelCharacters he L N : Set (AddChar L ℂ)) ⊆ c '' (q '' (B : Set A)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨q z, mem_image_of_mem q hz, rfl⟩
  exact (hQ.image c).subset hR

end Finite

/-- Summing the distinct restrictions of the frequencies in the annihilator of
`N` gives a scalar multiple of the indicator of `N` on `L`. -/
def LatticeLevelFourierStatement [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A] : Prop :=
  IsCompact (L : Set A) → IsOpen (N : Set A) → IsCompact (N : Set A) →
  ∃ S : Finset (AddChar L ℂ),
    (S : Set (AddChar L ℂ)) = latticeLevelCharacters he L N ∧ S.Nonempty ∧
    ∀ x : L, (∑ χ ∈ S, χ x) = (N : Set A).indicator (fun _ => (S.card : ℂ)) x.val

variable [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A]

theorem latticeLevelFourier (μ : Measure A) [μ.IsAddHaarMeasure] :
    LatticeLevelFourierStatement he L N := by
  classical
  intro hLc hNo hNc
  let B := latticeLevelCharacters he L N
  let : Fintype B := (latticeLevelCharacters_finite he L N hLc hNo hNc).fintype
  let S := (B : Set (AddChar L ℂ)).toFinset
  refine ⟨S, Set.coe_toFinset _, ⟨0, Set.mem_toFinset.mpr B.zero_mem⟩, ?_⟩
  intro x
  let ev : AddChar B ℂ := (AddChar.doubleDualEmb x).compAddMonoidHom B.subtype
  have hTriv : ev = 0 ↔ (x : A) ∈ N := by
    have hNN := compactOpenDoubleAnnihilator he N μ hNo hNc
    rw [← hNN, he.mem_annihilator]
    constructor
    · intro h z hz
      let χ : B := ⟨latticeAddChar he L z, ⟨z, hz, rfl⟩⟩
      have ht : e x.val z = 1 := congrArg (fun f : AddChar B ℂ => f χ) h
      exact (he.symm z x.val).trans ht
    · intro h
      apply AddChar.ext
      rintro ⟨χ, z, hz, rfl⟩
      change e x.val z = 1
      exact (he.symm x.val z).trans (h z hz)
  have hSum : (∑ χ ∈ S, χ x) = ∑ χ : B, ev χ :=
    Finset.sum_subtype S (fun _ => Set.mem_toFinset) _
  rw [hSum, AddChar.sum_eq_ite]
  by_cases hx : (x : A) ∈ N
  · rw [ite_eq_left (hTriv.mpr hx), indicator_of_mem hx, Set.toFinset_card]
    simp only [← Nat.card_eq_fintype_card]
    rfl
  · rw [ite_eq_right (mt hTriv.mp hx), indicator_of_notMem hx]

end Langlands.HarmonicAnalysis.UnitConjugation
