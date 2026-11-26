# Compact étale global comparison

`analyticEtaleGlobalComparison` proves `AnalyticEtaleGlobalComparisonStatement`.
For a continuous action on a compact Hausdorff analytic space `X`, it makes
the canonical comparison `etaleComparison ρ R q` an isomorphism of functors
in every degree `q`. The coefficient ring, size hypothesis on the group, and
admissible-refinement instance are those of the statement.

The proof chooses a complete algebraically closed field `L` realizing every
underlying point of `X`, using `commonAlgebraicallyClosedPointField`. The field
lies in universe `max u (v + 1) uL`, so adjoining it as an auxiliary parameter
preserves the module universe of the original comparison.
`EtaleSite.geometricPointStatement` supplies the étale point axioms, and applying
`ULift.down` transfers the common field's surjectivity to `pointProjection L X`.
The resulting field-valued point fibres jointly detect sheaf morphisms by
`analyticEtalePointFibersJointlyFaithful`.

The proof applies `analyticEtaleGaloisCoinducedLocalAcyclic` to the smooth point
products with discrete coefficient diagrams to obtain their positive ordinary
higher direct image vanishing. Their underlying ordinary sheaves are c-soft,
so `cSoftAcyclicity` gives vanishing of their positive ordinary compactly
supported cohomology.
`analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary` combines
these inputs to obtain compact-support acyclicity of the restricted Godement
terms. Joint faithfulness makes the Godement coaugmentation monic, so an
injective equivariant sheaf retracts from its Godement term. The vanishing passes
to its restriction, and compactness identifies compactly supported cohomology
with ordinary cohomology. These are the two steps of
`analyticEtaleRestrictedInjectiveAcyclic_of_godement`.

`isIso_etaleGlobalInclusion_of_compactSpace` identifies the smooth global
sections with all global sections.
`isIso_etaleComparison_of_injective_acyclic` applies the exact base-change
criterion to this identification and the acyclicity of restricted injectives.

## Sources

- Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, 1995–1996
  manuscript, Proposition 1.5.1, printed pp. 10–11, and Theorem 1.6.1(ii) and its
  proof, printed p. 13. The source uses the softness of restricted Godement
  terms, with the finite Galois and ordinary softness calculations providing
  the two inputs above. Literature ID
  `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
  file `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
- Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
  Lemma 3.2(i), printed p. 544, uses vanishing of positive ordinary higher direct
  images and of positive ordinary cohomology to deduce étale acyclicity.
  Literature ID `berkovich-1994-vanishing-cycles-formal-schemes`, PDF SHA-256
  `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
