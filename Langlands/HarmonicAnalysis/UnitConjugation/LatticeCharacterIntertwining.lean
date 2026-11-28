import Langlands.HarmonicAnalysis.Bicharacter.LatticeCharacterInnerProduct
import Langlands.HarmonicAnalysis.Bicharacter.ProjectedAnnihilator
import Langlands.Representation.Character.CompactCharacterInnerProduct

/-! # Intertwining from compact character expansions on a lattice -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set

section Lattice

variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y]
  {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- In measure-preserving coordinates that send negatives to inverses, compact
character expansions on a lattice detect intertwining by congruence of frequencies. -/
def LatticeCharacterIntertwiningStatement
    [IsTopologicalAddGroup Y] [BorelSpace Y] [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    {e : Y → Y → ℂ} (he : IsSelfDualBicharacter e) (μ : Measure Y) [μ.IsAddHaarMeasure]
    (ν : Measure K) [ν.IsHaarMeasure] (L : AddSubgroup Y)
    (E : L ≃ₜ K) (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
    {I J : Type*} (s : Finset I) (t : Finset J) (a : I → Y) (b : J → Y) : Prop :=
  IsOpen (L : Set Y) → IsCompact (L : Set Y) →
  MeasurePreserving E (μ.comap Subtype.val) ν →
  (∀ x : L, E (-x) = (E x)⁻¹) → IsSmooth ρ → IsSmooth σ →
  (∀ x : L, σ.character (E x) = ∑ i ∈ s, e x (a i)) →
  (∀ x : L, ρ.character (E x) = ∑ j ∈ t, e x (b j)) →
  ((∃ T : Representation.IntertwiningMap ρ σ, T ≠ 0) ↔
    ∃ i ∈ s, ∃ j ∈ t, a i - b j ∈ he.annihilator (L : Set Y))

variable [IsTopologicalAddGroup Y] [BorelSpace Y] [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

theorem latticeCharacterIntertwining
    {e : Y → Y → ℂ} (he : IsSelfDualBicharacter e) (μ : Measure Y) [μ.IsAddHaarMeasure]
    (ν : Measure K) [ν.IsHaarMeasure] (L : AddSubgroup Y)
    (E : L ≃ₜ K) (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
    {I J : Type*} (s : Finset I) (t : Finset J) (a : I → Y) (b : J → Y) :
    LatticeCharacterIntertwiningStatement he μ ν L E ρ σ s t a b := by
  intro hLo hLc hE hNeg hρ hσ hσEval hρEval
  let f (x : Y) := (∑ i ∈ s, e x (a i)) * starRingEnd ℂ (∑ j ∈ t, e x (b j))
  have hIntegral : (∫ k, σ.character k * ρ.character k⁻¹ ∂ν) = ∫ x in (L : Set Y), f x ∂μ := by
    let g (k : K) := σ.character k * ρ.character k⁻¹
    change (∫ k, g k ∂ν) = _
    rw [← hE.integral_comp' (f := E.toMeasurableEquiv) g,
      ← integral_subtype_comap hLo.measurableSet f]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change g (E x) = f x
      simp only [g, f, ← hNeg, hσEval, hρEval, map_sum, he.conj_apply, AddSubgroup.coe_neg]
  rw [← Representation.Character.compactCharacterInnerProduct_ne_zero_iff ν ρ σ hρ hσ, hIntegral]
  simpa only [one_mul, f] using
    latticeCharacterInnerProduct he μ L s t a b 1 1 hLo hLc one_ne_zero one_ne_zero

end Lattice

section Projection

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X]
    [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [CompactOpenExhaustion Y]
    [MeasurableSpace Y] [BorelSpace Y]
  {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- When the two expansions come from lattices `L` and `M` in ambient and slice
spaces, intertwining on the intersection is equivalent to frequency congruence
modulo the projected dual of `L` plus the dual of `M`. -/
theorem projectedLatticeCharacterIntertwining
    {eX : X → X → ℂ} {eY : Y → Y → ℂ} (hX : IsSelfDualBicharacter eX)
    (hY : IsSelfDualBicharacter eY) (μ : Measure X) [μ.IsAddHaarMeasure]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure]
    (i : Y →+ X) (p : X →+ Y) (hi : Continuous i) (hp : Continuous p)
    (hcomp : ∀ x y, eY (p x) y = eX x (i y))
    (L : AddSubgroup X) (M : AddSubgroup Y)
    (hLo : IsOpen (L : Set X)) (hLc : IsCompact (L : Set X))
    (hMo : IsOpen (M : Set Y)) (hMc : IsCompact (M : Set Y))
    (E : (L.comap i ⊓ M : AddSubgroup Y) ≃ₜ K)
    (hE : MeasurePreserving E (ν.comap Subtype.val) μK)
    (hNeg : ∀ x, E (-x) = (E x)⁻¹)
    (ρ : Representation ℂ K V) (σ : Representation ℂ K W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    {I J : Type*} (s : Finset I) (t : Finset J) (a : I → X) (b : J → Y)
    (hσEval : ∀ x, σ.character (E x) = ∑ r ∈ s, eX (i x) (a r))
    (hρEval : ∀ x, ρ.character (E x) = ∑ r ∈ t, eY x (b r)) :
    (∃ T : Representation.IntertwiningMap ρ σ, T ≠ 0) ↔
      ∃ r ∈ s, ∃ q ∈ t, p (a r) - b q ∈
        (hX.annihilator (L : Set X)).map p ⊔ hY.annihilator (M : Set Y) := by
  let Q := L.comap i ⊓ M
  have hQo : IsOpen (Q : Set Y) := (hLo.preimage hi).inter hMo
  have hQc : IsCompact (Q : Set Y) := hMc.inter_left ((L.isClosed_of_isOpen hLo).preimage hi)
  have hEval (x : Q) : σ.character (E x) = ∑ r ∈ s, eY (x : Y) (p (a r)) := by
    rw [hσEval]
    exact Finset.sum_congr rfl fun r _ => by rw [hX.symm, ← hcomp, hY.symm]
  have h := latticeCharacterIntertwining hY ν μK Q E ρ σ s t (p ∘ a) b
    hQo hQc hE hNeg hρ hσ hEval hρEval
  rw [projectedAnnihilator hX hY μ ν i p L M hp hcomp hLo hLc hMo hMc] at h
  exact h

end Projection

end Langlands.HarmonicAnalysis.UnitConjugation
