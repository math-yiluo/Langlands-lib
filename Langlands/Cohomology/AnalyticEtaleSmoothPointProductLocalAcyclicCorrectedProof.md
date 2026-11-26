# Local acyclicity of actual restricted smooth point products, for a topological group

The theorem `analyticEtaleSmoothPointProductLocalAcyclicCorrected` proves
`AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement` in
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`, with every argument, universe
and instance hypothesis of the statement: a complete ultrametric field `K`, a normed extension
`L`, an analytic space `X` with point axioms `h`, a coefficient ring `R` in universe
`max u (v + 1) uL`, and a topological group `G`, small in that universe, acting by `ρ` with
admissible refinements of the distinguished lift system. Under Hausdorffness of `X`,
surjectivity of `pointProjection L X` and continuity of the action, the positive ordinary
higher direct images `etaleUnderlyingHigherDirectImage` vanish on
`etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R` applied to every injective
discrete coefficient diagram on the field points.

## The proof

The proof composes two theorems of the Library.

- `analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced`
  (module `Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction`) derives the
  corrected statement from `AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. It shows that
  the fixed sections of the actual restricted smooth point product on equivariant finite Galois
  data are coinduced, so the smooth point product satisfies `HasCoinducedGaloisFixedSections`.
- `analyticEtaleGaloisCoinducedLocalAcyclic`
  (module `Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclicProof`) proves
  `AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`: an étale `G`-sheaf with coinduced
  Galois fixed sections has vanishing positive ordinary higher direct images after restriction
  to the ordinary étale site.

Applying the first theorem to the second gives the statement. The proof uses no other
hypothesis. In particular it does not use the older
`AnalyticEtaleSmoothPointProductLocalAcyclicStatement`, which lacks the topological-group
hypothesis.

## Source

Vladimir G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, Proposition
1.5.1, condition (1′), printed pp. 10–11 (the `Equish_1996` manuscript, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`). The argument
there passes to finite Galois neighbourhoods, shrinks the acting group to an open subgroup and
uses products of coinduced finite Galois modules; the two Library theorems above formalize the
algebraic and the analytic halves of that argument.
