import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.Correspondence.HenniartNumericalReductionProof
import Langlands.Correspondence.HenniartOrbitStratumFinitenessProof

/-!
# Torsion numbers and counting versus surjectivity

Numerical injections preserve the refined strata and induce injections on their
orbit sets. Equal finite counts characterize surjectivity in the stated ranks
and slopes, with natural Artin conductors available for the converse.
-/

noncomputable section

namespace Langlands.Henniart

open Numerical Correspondence VirtualRepresentation

universe uK uW uV

section

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uK} p} {k : ℕ}
variable {φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
  SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat}

private theorem torsionNumber_eq (hφ : IsNumericalInjection K φ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    supercuspidalTorsionNumber K (φ σ) = weilTorsionNumber K σ :=
  Nat.card_congr (Equiv.subtypeEquivRight fun z => by
    rw [← hφ.2.2 z σ]
    exact hφ.1.eq_iff)

private theorem mapsWeilSwan (hφ : IsNumericalInjection K φ)
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat} {s : ℕ} :
    HasWeilSwan K σ s → HasSupercuspidalSwan K (φ σ) s := by
  rintro ⟨a, ha, hs⟩
  exact ⟨a, hφ.2.1 σ a ha, hs⟩

private theorem imageOrbit_eq_iff (hφ : IsNumericalInjection K φ)
    (σ τ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, φ σ⟩ =
        PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, φ τ⟩ ↔
      Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, σ⟩ =
        Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, τ⟩ := by
  simp only [supercuspidalOrbitClass_eq_iff, weilOrbitClass_eq_iff, ← hφ.2.2, hφ.1.eq_iff]

variable (φ) in
/-- Apply the injection to a representative witnessing membership in the refined stratum.
The orbit of the result is independent of that choice by `imageOrbit_eq_iff`. -/
private def refinedOrbitMap {s f : ℕ} (c : weilRefinedStratum.{uK, uW} K k s f) :
    PadicSupercuspidal.UnramifiedOrbitClasses.{uK, uV} K :=
  PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, φ (Classical.choose c.property)⟩

private theorem refinedOrbitMap_encard_range (hφ : IsNumericalInjection K φ) (s f : ℕ) :
    (Set.range (refinedOrbitMap (s := s) (f := f) φ)).encard =
      (weilRefinedStratum.{uK, uW} K k s f).encard := by
  apply Function.Injective.encard_range
  intro c d h
  have hOrbit := (imageOrbit_eq_iff hφ _ _).mp h
  exact Subtype.ext ((Classical.choose_spec c.property).1.symm.trans
    (hOrbit.trans (Classical.choose_spec d.property).1))

private theorem refinedOrbitMap_range_subset (hφ : IsNumericalInjection K φ) (s f : ℕ) :
    Set.range (refinedOrbitMap (s := s) (f := f) φ) ⊆
      supercuspidalRefinedStratum.{uK, uV} K k s f := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨_, hSwan, hTorsion⟩ := Classical.choose_spec c.property
  exact ⟨φ (Classical.choose c.property), rfl, mapsWeilSwan hφ hSwan,
    (torsionNumber_eq hφ _).trans hTorsion⟩

private theorem supercuspidalRefinedStratum_finite (K : PadicField.{uK} p) (k s f : ℕ) :
    (supercuspidalRefinedStratum.{uK, uV} K k s f).Finite := by
  -- Truncated subtraction permits several conductors when the Swan exponent is zero.
  refine ((Set.finite_Iic (s + (k + 1))).biUnion fun a _ =>
    supercuspidalOrbitStratumFiniteness.{uK, uV} p K k a).subset ?_
  rintro _ ⟨π, hπ, ⟨a, ha, hSwan⟩, _⟩
  have ha_le : a ∈ Set.Iic (s + (k + 1)) := by
    change a ≤ s + (k + 1)
    omega
  exact Set.mem_biUnion ha_le ⟨π, hπ, ha⟩

end

/-- The refined-strata preservation and counting-versus-surjectivity package. -/
theorem refinedStrata : RefinedStrataStatement.{uK, uW, uV} := by
  constructor
  · intro p _ K k φ hφ
    refine ⟨torsionNumber_eq hφ, fun _ _ => mapsWeilSwan hφ, fun s f => ?_⟩
    rw [← refinedOrbitMap_encard_range hφ s f]
    exact Set.encard_le_encard (refinedOrbitMap_range_subset hφ s f)
  · intro p _ K x N
    constructor
    · intro hCounts k hRank φ hφ π s hSwan hSlope
      let f := supercuspidalTorsionNumber K π
      obtain ⟨hCard, hFinite⟩ := hCounts k s f hRank hSlope
      have hRange := hFinite.eq_of_subset_of_encard_le'
        (refinedOrbitMap_range_subset hφ s f)
        ((refinedOrbitMap_encard_range hφ s f).trans hCard).ge
      have hπ : PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, π⟩ ∈
          supercuspidalRefinedStratum K k s f := ⟨π, rfl, hSwan, rfl⟩
      rw [← hRange] at hπ
      obtain ⟨c, hc⟩ := hπ
      obtain ⟨z, hz⟩ := (supercuspidalOrbitClass_eq_iff K π _).mp hc.symm
      exact ⟨weilUnramifiedTwist K k z (Classical.choose c.property), (hφ.2.2 _ _).trans hz⟩
    · intro hArtin hExists k s f hRank hSlope
      obtain ⟨φ, hφ, hReach⟩ := hExists k hRank
      have hRange : Set.range (refinedOrbitMap (s := s) (f := f) φ) =
          supercuspidalRefinedStratum.{uK, uV} K k s f := by
        refine (refinedOrbitMap_range_subset hφ s f).antisymm ?_
        rintro _ ⟨π, rfl, hSwan, hTorsion⟩
        obtain ⟨σ, rfl⟩ := hReach π s hSwan hSlope
        obtain ⟨a, ha⟩ := hArtin k hRank σ
        obtain ⟨b, hb, hsub⟩ := hSwan
        have hab : a = b := WithTop.coe_injective ((hφ.2.1 σ a ha).symm.trans hb)
        have hσ : HasWeilSwan K σ s := ⟨a, ha, by rw [hab, hsub]⟩
        have hf : weilTorsionNumber K σ = f := (torsionNumber_eq hφ σ).symm.trans hTorsion
        let c : weilRefinedStratum.{uK, uW} K k s f :=
          ⟨Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, σ⟩,
            ⟨σ, rfl, hσ, hf⟩⟩
        exact ⟨c, (imageOrbit_eq_iff hφ _ σ).mpr (Classical.choose_spec c.property).1⟩
      rw [← refinedOrbitMap_encard_range hφ s f, hRange]
      exact ⟨rfl, supercuspidalRefinedStratum_finite K k s f⟩

end Langlands.Henniart
