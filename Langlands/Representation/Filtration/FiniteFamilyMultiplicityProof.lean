import Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement
import Langlands.Representation.Filtration.MultiplicityIndependenceProof
import Langlands.Representation.Filtration.JordanHolderTransportProof

/-! Count the actual irreducible factors of a supplied indexed filtration. -/

namespace Langlands

universe uK uG uI uA uB uT

/-- A finite family matching the actual graded quotients determines exact
composition length and every Jordan–Hölder multiplicity. -/
theorem finiteFamilyFiltrationMultiplicity :
    FiniteFamilyFiltrationMultiplicityStatement.{uK, uG, uI, uA, uB, uT} := by
  intro k _ G _ I _ A family hfamily r e s he
  have hs : s.HasSimpleFactors := by
    intro i
    obtain ⟨f⟩ := he i
    exact (OrderIso.isSimpleOrder_iff
      (JordanHolderTransportProof.subrepOrderIso f)).mpr (hfamily (e i))
  have hr : r = Nat.card I := by
    calc
      r = Nat.card (Fin r) := by simp
      _ = Nat.card I := Nat.card_congr e
  refine ⟨?_, ?_⟩
  · rw [← hr]
    exact ⟨s, hs⟩
  · intro τ m
    have hc : s.factorMultiplicity τ =
        Nat.card {i : I // Nonempty ((family i).ρ.Equiv τ.ρ)} := by
      unfold ObjectRepFiltration.factorMultiplicity
      apply Nat.card_congr
      refine e.subtypeEquiv ?_
      intro i
      obtain ⟨f⟩ := he i
      exact ⟨fun ⟨p⟩ => ⟨f.symm.trans p⟩, fun ⟨q⟩ => ⟨f.trans q⟩⟩
    have hcanonical : HasJordanHolderMultiplicity A τ
        (Nat.card {i : I // Nonempty ((family i).ρ.Equiv τ.ρ)}) :=
      ⟨r, s, hs, hc⟩
    constructor
    · intro hm
      exact hm.unique hcanonical
    · intro hm
      rw [hm]
      exact hcanonical

end Langlands
