# Actual left translation on source-normalized coefficient fibers

This internal adapter constructs the left-translation part of Waldspurger's
V.3 formula (1), printed p.295 / PDF p.61 of *La formule de Plancherel pour
les groupes p-adiques* (2003), registered as `waldspurger-2003-plancherel`,
DOI 10.1017/S1474748003000082. The original page was read directly. The
published source-map guidance distinguishes the convergence-domain adjunction
results from the unproved full-unitary extension properties.

All declarations are in `Langlands.Plancherel.CoefficientConjugation`.
The construction uses actual semidirect decompositions `P = M U` and
`P' = M' U'` in a locally compact nonarchimedean group, an actual conjugating
point `g`, the three subgroup conjugation relations, and closed unimodular
radicals. Representation-carrier universes are independent of the group universe.

`leviInductionCongr` transports an inducing representation equivalence through
the published value-preserving normalization comparisons and the actual induced
equivalence. Its evaluation formula is pointwise application of that equivalence.

`leviLeftTranslation` transports `inductionConjugationIsoApp` through those same
normalization comparisons. Its evaluation formula is exactly
`f(x) ↦ f(g⁻¹*x)`. The dual factor `leviDualLeftTranslation` additionally applies
`conjugateDualEquiv`, the inverse of the actual smooth-dual pullback comparison
`contragredientPullbackIso`. This identification preserves the underlying linear
functional, as proved by `conjugateDualEquiv_apply` and the dual evaluation law.

`leviCoefficientLeftTranslation` and its pure-tensor, evaluation and action
laws additionally require `SecondCountableTopology G`,
`CompactSpace (Induction.LeftQuotient P)` and
`CompactSpace (Induction.LeftQuotient P')`. These are explicit hypotheses of
the product-induction tensor comparisons; they are not needed by the preceding
inducing-factor and smooth-dual constructions.

`leviCoefficientLeftTranslation` tensors these two actual maps and transports
through `leviNormalizedProductInductionTensorEquiv` on source and target. Its
source is the original `leviProductInducedCoefficientObject h hU A`, and its
target is the same construction for the conjugated inducing object. The
pure-tensor, evaluation and `G × G` action laws are proved by the implemented
tensor comparison and the representation equivalences' intertwining laws.
No quotient measure, compact probability measure or formal degree is rescaled.
The construction alone asserts no equality between source and target integrated
coefficient maps.

This file contains constructions and elementary transport proofs. It supplies
neither a standard intertwining operator nor a generic inverse, rational
continuation, unitary extension, coefficient-preservation theorem, or the
substantive V.3 cocycle/descent conclusions. Those require the actual standard
families and the separately specified analytic targets.
