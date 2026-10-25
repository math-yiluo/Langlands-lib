import Langlands.Representation.Filtration.MultiplicityStatement
import Langlands.Representation.Filtration.JordanHolderComparisonProof

/-! Independence and uniqueness of the multiplicity of one factor. -/

namespace Langlands

universe uK uG uA uT

/-- The Jordan–Hölder matching restricts to the indices of any fixed factor. -/
theorem jordanHolderMultiplicityIndependence :
    JordanHolderMultiplicityIndependenceStatement.{uK, uG, uA, uT} := by
  intro k _ G _ A τ n m s t hs ht
  obtain ⟨e, he⟩ := jordanHolderSeriesComparison k G A n m s t hs ht
  unfold ObjectRepFiltration.factorMultiplicity
  apply Nat.card_congr
  refine e.subtypeEquiv ?_
  intro i
  obtain ⟨f⟩ := he i
  exact ⟨fun ⟨p⟩ => ⟨f.symm.trans p⟩, fun ⟨q⟩ => ⟨f.trans q⟩⟩

/-- Two actual composition-series witnesses assign the same multiplicity. -/
theorem HasJordanHolderMultiplicity.unique
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G} {τ : Rep.{uT} k G} {m n : ℕ}
    (hm : HasJordanHolderMultiplicity A τ m)
    (hn : HasJordanHolderMultiplicity A τ n) : m = n := by
  obtain ⟨r, s, hs, hsm⟩ := hm
  obtain ⟨r', t, ht, htn⟩ := hn
  exact hsm.symm.trans
    ((jordanHolderMultiplicityIndependence k G A τ r r' s t hs ht).trans htn)

end Langlands
