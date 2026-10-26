import Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof

/-! Count the actual upper Jacquet factors of irreducible cuspidal induction. -/

namespace Langlands

open CuspidalSupport

universe uF uV uW

/-- The actual associated Jacquet filtration supplies the exact upper
composition length and all Jordan–Hölder multiplicities. -/
theorem glUpperCuspidalJacquetMultiplicityFromFiltration :
    GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement.{uF, uV, uW} := by
  intro p _ F T n hfilt
  let := T.topology
  intro B C V _ _ ρ hirr hcusp hassoc
  let σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of ρ hcusp.1.1
  obtain ⟨_, r, e, s, hs⟩ := hfilt B C σ hcusp.2 hassoc
  let family (w : MinimalConjugatingPermutations (F := F.Carrier) B C) :
      Rep.{uV} ℂ (C.Levi F.Carrier) :=
    Rep.of (transport B C w.val.val w.property ρ)
  have hfamily : ∀ w, Representation.IsIrreducible (family w).ρ := by
    intro w
    exact JacquetLength.isIrreducible_transport w.val.val w.property hirr
  have result := finiteFamilyFiltrationMultiplicity ℂ (C.Levi F.Carrier)
    (MinimalConjugatingPermutations (F := F.Carrier) B C) _ family hfamily r e s hs
  refine ⟨result.1, ?_⟩
  intro W _ _ τ m
  exact result.2 (Rep.of τ) m

/-- Check the complete unapplied three-universe target. -/
example : GLUpperCuspidalJacquetMultiplicityFromFiltrationStatement.{uF, uV, uW} :=
  glUpperCuspidalJacquetMultiplicityFromFiltration.{uF, uV, uW}

end Langlands
