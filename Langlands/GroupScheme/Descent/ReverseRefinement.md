# Recovering actual solutions from a refinement

This internal construction derives recovery across a refinement from actual
Čech data, transition composition, pullback coherence, and étale homomorphism
descent. All schemes lie in one arbitrary universe.

Let `D : Datum p G`, where `p : S → B`, and let `q : V → S` have surjective
étale composite `t = q ≫ p`. A supplied `s : Solution (D.refine q)` has a group
scheme `C = s.obj` over `B` and a compatible comparison `t*C ≅ q*G`.
`Datum.solutionOfRefinement q s` constructs a solution of the original `D`.
Its descended group remains `C`. The construction does not require `q` to be
surjective or any affineness hypothesis. It requires a supplied refined solution.

The cross overlap is `W = V ×_B S`, with projections `v : W → V` and
`r : W → S`. Since `r` is the pullback of `t`, it is surjective and étale.
`refinementSolutionOnCover` restricts `s` across this square and uses
`collapseReindexSolution` to compare double and composite pullbacks. The
result solves `D.reindex r (v ≫ q) p w` with descended group `p*C` over `S`.
The same datum has the transition solution with descended group `G`.

`Solution.descendIsoOfEtale` descends any compatible isomorphism between the
covering groups of two supplied solutions. Its homomorphism is the existing
`descendHomOfEtale`. Pullback identifies it with the conjugated original
isomorphism, so `isoOfEtaleBaseChange` reflects its invertibility. Applying
this to the identity between the two covering groups constructs
`refinementComparison : p*C ≅ G`.

`refinementComparison_baseChange` describes this comparison on `W`: it is the
square comparison `r*(p*C) ≅ v*(t*C)`, followed by `v*s.iso`, the comparison
`v*(q*G) ≅ (v ≫ q)*G`, and the transition `(v ≫ q)*G → r*G`.
`refinementComparison_restrict` proves the same formula after arbitrary
further pullback to a test scheme with specified coordinates. It uses
naturality of transitions, comparison associativity, naturality in `s.iso`,
and `squareComparison_pullback`. The last helper is proved by comparing
projections to the original group scheme. `refinementComparison_local`
applies this formula to the map into `W` supplied by a commuting pair.

To prove original overlap compatibility, take the surjective étale cover
`Z = V ×_B (S ×_B S) → S ×_B S`. Its two maps to `S` share one `V` coordinate.
For such a pair, `refinementComparison_transition` substitutes the local
formula at both endpoints. Composition of the original transitions identifies
the two final transports. Canonical transitions preserve the square comparison,
as proved by `canonicalDatum_transition_squareComparison` using projection
extensionality. This proves transition compatibility on `Z`.
`pullHom_overlap` identifies each pulled overlap with its endpoint transition.
Cancelling the endpoint comparisons and using faithful surjective étale
pullback gives `refinementComparison_compatible` on the original overlap.
Together with the recovered actual isomorphism and the object `C`, this is
exactly the three fields of `Solution D`.

This module recovers a solution from a supplied refined solution. Constructing an
initial refined solution and applying this to the quasi-split inner-form
existence statement remain separate obligations.
