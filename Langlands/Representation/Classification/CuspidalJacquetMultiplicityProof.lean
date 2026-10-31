import Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-! Exact upper and opposite cuspidal Jacquet lengths and multiplicities. -/

namespace Langlands

open CuspidalSupport

universe uF uV uW

/-- Both actual normalized Jacquet modules have their full composition
length and every irreducible target's exact Jordan–Hölder multiplicity. -/
theorem glCuspidalJacquetMultiplicityPrerequisites :
    GLCuspidalJacquetMultiplicityPrerequisitesStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n _ B C V _ _ ρ hirr hcusp hassoc
  have hfiltration := associatedJacquetFiltration.{uF, uV} F T n
  have hupper := glUpperCuspidalJacquetMultiplicityFromFiltration.{uF, uV, uW}
    p F T n hfiltration B C V ρ hirr hcusp hassoc
  let σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of ρ hcusp.1.1
  obtain ⟨r, e, s, hs⟩ := glOppositeCuspidalJacquetFiltrationFromUpper.{uF, uV}
    p F T n hfiltration B C σ hcusp.2 hassoc
  let family (w : MinimalConjugatingPermutations (F := F.Carrier) B C) :
      Rep.{uV} ℂ (C.Levi F.Carrier) :=
    Rep.of (transport B C w.val.val w.property ρ)
  have hfamily : ∀ w, Representation.IsIrreducible (family w).ρ := by
    intro w
    exact JacquetLength.isIrreducible_transport w.val.val w.property hirr
  have hopposite := finiteFamilyFiltrationMultiplicity ℂ (C.Levi F.Carrier)
    (MinimalConjugatingPermutations (F := F.Carrier) B C) _ family hfamily r e s hs
  refine ⟨hupper.1, hopposite.1, ?_⟩
  intro W _ _ τ _ m
  exact ⟨hupper.2 W τ m, hopposite.2 (Rep.of τ) m⟩

end Langlands
