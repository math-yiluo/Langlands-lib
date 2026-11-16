# Compact quasi-étale comparison from restricted-injective acyclicity

Author: Worker 512. The generic derived-comparison criterion was developed by
Worker 284 and is imported from its module.

The internal construction
`quasiEtaleComparisonIsoOfRestrictedInjectivesAcyclic` supplies a natural
isomorphism from `quasiEtaleGSheafCohomology ρ R q ⋙ smoothForget R G` to
`quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCohomology X R q`, assuming
restricted-injective acyclicity, compactness of X, and continuity of ρ.
Its forward map is exactly the published `quasiEtaleComparison ρ R q`;
the final simp theorem records this equality by reflexivity.

The supporting conditional theorem proves the unchanged
`AnalyticQuasiEtaleGlobalComparisonStatement` from the premise
`QuasiEtaleRestrictedInjectivesAcyclicStatement`, retaining all universes and
instance hypotheses of both published proposition definitions.

For compact X and continuous ρ, the degree-zero result makes
`quasiEtaleGlobalInclusion` an isomorphism. The proof installs the published
sheafification, enough-injectives, right Kan extension, and exactness instances
for quasi-étale restriction. It applies
`ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic` to the actual
degree-zero inclusion. Its acyclicity premise is exactly the hypothesis on
positive cohomology of restrictions of injective G-sheaves, since
`quasiEtaleCohomology` is the right derived functor of quasi-étale global
sections and `quasiEtaleComparison` is the induced base-change map.

The reduction does not prove the retained restricted-injective acyclicity
premise and does not establish the unconditional comparison theorem. Its
provenance is the internal combination of the imported degree-zero result,
the exact functor infrastructure, and the generic derived-comparison criterion.
