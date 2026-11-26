import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceReductionProof

/-!
# Building cyclic regular induction over a totally complex base

Proves `CyclicRegularInductionExistenceReductionTCStatement` by the argument
`CyclicRegularInductionExistence.cyclicRegularInductionExistenceOver_of_inputs` of
`CyclicRegularInductionExistenceReductionProof` (Arthur and Clozel 1989, Lemma III.6.4),
supplying the totally complex prime realizations, pair comparisons and Euler constituent
recovery over fields that extend the totally complex base.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open CyclicRegularInductionExistence

/-- The exact target `CyclicRegularInductionExistenceReductionTCStatement`. The intermediate
and upper fields of the common argument extend the totally complex base, so they are totally
complex by `NumberField.isTotallyComplex_of_algebra`, which is what the totally complex prime
realization, pair comparison and Euler constituent recovery over them require. -/
theorem cyclicRegularInductionExistenceReductionTC :
    CyclicRegularInductionExistenceReductionTCStatement.{uF, uE, uV, uW} := by
  intro hRealF hRealK hPairF hPairK hOrbitF hOrbitK hEquiv hRec hTrans hAttV hAttW
    F E _ _ _ _ _ _ _ _ _
  exact cyclicRegularInductionExistenceOver_of_inputs
    (fun E => hRealF F E)
    (fun K E _ _ _ _ _ _ _ _ _ => by
      have := NumberField.isTotallyComplex_of_algebra F K
      exact hRealK K E)
    (fun E => hPairF F E)
    (fun K E _ _ _ _ _ _ _ _ _ _ => by
      have := NumberField.isTotallyComplex_of_algebra F K
      exact hPairK K E)
    hOrbitF hOrbitK hEquiv
    (fun E _ _ _ _ => by
      have := NumberField.isTotallyComplex_of_algebra F E
      exact hRec E)
    hTrans hAttV hAttW E

end Langlands.Automorphic.Unramified
