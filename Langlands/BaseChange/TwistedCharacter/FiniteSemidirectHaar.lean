import Langlands.BaseChange.TwistedCharacter.TranslatedCosetCharacter
import Langlands.BaseChange.TwistedCharacter.SemidirectTopology
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Right invariance of Haar measure in finite extensions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure _root_.Topology
open scoped SemidirectProduct

section OpenSubgroup

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [LocallyCompactSpace G]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]

/-- Right invariance extends from an open subgroup when every ambient element
has a positive power in the subgroup. -/
theorem isMulRightInvariant_of_powers_in_openEmbedding (i : G →* H) (hi : IsOpenEmbedding i)
    (ν : Measure H) [ν.IsHaarMeasure] (hν : (ν.comap i).IsMulRightInvariant)
    (hPower : ∀ x : H, ∃ n : ℕ, n ≠ 0 ∧ ∃ g : G, x ^ n = i g) :
    ν.IsMulRightInvariant := by
  let δ := modularCharacter (G := H)
  have hFactor (η : Measure H) [η.IsHaarMeasure] (he : η = ν) : haarScalarFactor η ν = 1 := by
    subst η
    exact haarScalarFactor_self ν
  have hδ (g : G) : δ (i g) = 1 := by
    change modularCharacterFun (i g) = 1
    rw [modularCharacterFun_eq_haarScalarFactor ν]
    have h := (measurePreserving_mulRight_of_openEmbedding i hi ν hν g).map_eq
    change ν.map (· * i g) = ν at h
    exact hFactor _ h
  refine ⟨fun x => ?_⟩
  obtain ⟨n, hn, g, hg⟩ := hPower x
  have hx : δ x = 1 := (pow_left_inj₀ zero_le zero_le_one hn).mp (by
    rw [one_pow, ← map_pow, hg, hδ])
  rw [map_right_mul_eq_modularCharacterFun_smul ν]
  change δ x • ν = ν
  rw [hx, one_smul]

end OpenSubgroup

section SemidirectProduct

variable {G C : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [Group C] [TopologicalSpace C] (φ : C →* MulAut G)
    [MeasurableSpace (G ⋊[φ] C)]

/-- A Haar measure on a semidirect product with finite discrete component group
is right invariant if its restriction to the open initial group is right invariant. -/
def FiniteSemidirectHaarStatement [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [Finite C]
    [DiscreteTopology C] [IsTopologicalGroup (G ⋊[φ] C)] [BorelSpace (G ⋊[φ] C)]
    (ν : Measure (G ⋊[φ] C)) [ν.IsHaarMeasure] : Prop :=
  (ν.comap (SemidirectProduct.inl (φ := φ))).IsMulRightInvariant → ν.IsMulRightInvariant

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [BorelSpace G] [Finite C] [DiscreteTopology C]
    [IsTopologicalGroup (G ⋊[φ] C)] [BorelSpace (G ⋊[φ] C)]

theorem finiteSemidirectHaar (ν : Measure (G ⋊[φ] C)) [ν.IsHaarMeasure] :
    FiniteSemidirectHaarStatement φ ν := by
  intro hν
  let : SecondCountableTopology (G ⋊[φ] C) :=
    (SemidirectProduct.homeomorphProd φ).secondCountableTopology
  apply isMulRightInvariant_of_powers_in_openEmbedding SemidirectProduct.inl
    (SemidirectProduct.isOpenEmbedding_inl φ) ν hν
  intro x
  let n := Nat.card C
  have hr : (x ^ n).right = 1 := by
    change SemidirectProduct.rightHom (x ^ n) = 1
    rw [map_pow, pow_card_eq_one']
  have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨n, hn, (x ^ n).left, ?_⟩
  exact SemidirectProduct.ext rfl hr

end SemidirectProduct

end Langlands.BaseChange
