# Positive-rank product derivative gluing

This internal prerequisite defines `PositiveRankDerivativeLeibnizGluing` and
proves it in `positiveRankDerivativeLeibnizGluing`. It derives the natural
positive-rank product derivative filtration from published actual minus
identities, with every mixed-product derivative premise discharged. Its
provenance is the explicit composition of Library constructions and proofs
described below, rather than a new transcription of a literature statement.

## Exact scope

The field universe `uF` and carrier universe `uV` are independent. The result
quantifies arbitrary prime `p`, `F : PadicField p`, supplied topological data
`T`, and every bundled continuous nontrivial unitary additive character `ψ`
for `T.topology`. It applies to arbitrary smooth complex inputs on
`GL_(m+1)` and `GL_(n+1)`, with no admissibility, irreducibility, finiteness,
genericity or nonzero-carrier premise.

For every positive order `i ≤ (m+1)+(n+1)`, the conclusion is
`IsGluedFromFamily` for the literal `leibnizSource T ψ (m+1) (n+1) i hi.2`
and the complete feasible family `leibnizPiece T ψ (m+1) (n+1) i`.
The source is normalized binary induction, then the actual general-linear
derivative, then forgetting smoothness. A piece indexed by `(a,b)` is the
normalized binary product of the actual factor derivatives of orders `a,b`,
followed by the explicit equality-based rank transport. The index condition
is exactly `a ≤ m+1`, `b ≤ n+1`, and `a+b=i`. Every feasible index occurs once
in a finite filtration, in some enumeration and permutation, including zero
pieces and distinct indices with isomorphic pieces. Naturality is in both
input objects and all input maps.

The top order is included. Factor derivatives of order zero or top order
are retained literally; in particular an arbitrary representation of `GL_0`
is not replaced by a scalar or a chosen unit. The public proposition only
asserts positive input ranks and positive order. It is not the entire
all-rank, all-order Leibniz proposition.

## Implemented proof

The helper namespace is `Langlands.Derivative.LocalPositiveLeibniz`.

`derivative_succ_cast` peels the initial `Φ⁻` from a derivative of successor
order. It uses the published definitional recursion
`RightMixedDerivative.derivative_succ_eq` and composes the actual output rank
casts. `leftSourceSuccIso` applies this equality to the left mixed product,
uses the proved `MirabolicProductMinus.leftPhiCompatibility`, and moves the
expected mirabolic rank cast across the next derivative. Its residual rank
is an arbitrary supplied `c` with the displayed rank equality, so the helper
also applies above the second factor's rank.

`product_rankCast_cancel` and `rankCast_subsingleton` are proved by equality
elimination. The former cancels a second-factor rank transport against the
compensating transport after binary induction. The latter preserves a zero
carrier under rank transport.

`leftIsoPos` proves the left mixed-product derivative isomorphism by
induction on the mirabolic rank, simultaneously for all feasible positive
orders. Order one uses `leftMixedProductFirstDerivativeIso`. In a successor
rank and an order of at least two, `leftSourceSuccIso` moves the initial
minus to the second factor; the induction hypothesis supplies the previous
order comparison. `RightMixedDerivative.phiMinus_derivative_eq` identifies
the resulting second-factor composite with the desired derivative. The
explicit compensating casts are removed by `product_rankCast_cancel`.
The all-rank comparison uses the published
`leftMixedProductDerivativeIso`, including its arbitrary-`GL_0` tensor case.

`leftVanishPos` proves vanishing above the second factor's rank by the same
mirabolic-rank induction. At source `P_1` every such order is at least two;
the actual `leftPhiBoundary` gives a zero initial minus carrier, and
`mirabolicDerivativeOfOrder_obj_subsingleton` preserves that zero. At a
successor rank the same natural successor comparison reduces to the
induction hypothesis. A cast and its inverse cancel explicitly, so the
conclusion concerns the unmodified derivative carrier. The all-rank
vanishing uses the published `leftMixedProductDerivativeVanishing`; in
GL rank zero the inequalities are incompatible. Thus neither half
of the left mixed-product derivative formula is an assumed premise.

`rightFiltration` uses the existing conditional
`RightMixedDerivative.filtration_pos`, supplying the proved actual
`rightPsiCompatibility`, `rightPhiShortExact`, the published `leftMixedProductDerivativeIso` and
`leftMixedProductDerivativeVanishing`, and `Mirabolic.minusExactness` at carrier universe
`max uF uV`. The published `rightMixedProductDerivativeFiltration_zero`
supplies the full GL-zero case. This yields the complete right mixed-product
filtration proposition, without a remaining formula or exactness premise.

Finally `positiveGlued` applies the existing
`leibnizSource_glued_pos`, supplying `leftMixedProductDerivativeIso`,
`leftMixedProductDerivativeVanishing`, and
`rightFiltration`. That construction differentiates the actual mirabolic
restriction short exact sequence, glues its subobject from the
positive-first derivative pieces, glues its quotient from the feasible
zero-first piece or the empty family, then splices and reindexes these
families. The public theorem supplies this argument at precisely the
parameters of the new proposition.

## Dependency audit and independence

Before integration, a recursive scan of the six original direct imports gave
315 project modules, including this entry. The other 314 Lean files equaled the published
Library base `e058cb4d3adbd71764731d87c4cbfcb5805696e8` byte for byte, and
had paired Markdown. Integration additionally imports
`LeftMixedProductDerivativeProof` and reuses its two exact all-rank results
in place of the duplicate `leftIso` and `leftVanish` declarations. The
positive-rank induction helpers remain available. The integrated closure has
320 project modules, each with a nonempty Markdown companion. External imports
are from Mathlib and Lean. The only Classification modules in this closure are `Supercuspidal`,
`SupercuspidalContragredientAux`, and
`SupercuspidalContragredientStatement`. These enter lower induction,
compact-section and transport infrastructure; none supplies a segment or
classification conclusion here.

The actual minus identities are the proved clauses assembled in
`MirabolicProductMinusCompatibility`. The left-Psi comparison computes the
actual radical quotient by a split-kernel induction comparison. The
left-Phi comparison uses the two-orbit restriction and character-localization
sequence, vanishing of its cycle piece, and the explicitly normalized
stabilizer and source quotient identifications. Its `P_1` boundary proves
zero using a nontrivial radical character. The right-Psi comparison computes
the quotient with the full source coinvariants. The right-Phi short exact
sequence uses elementary matrix two-orbit coverage, the localized Mackey
sequence, and actual cycle/identity piece isomorphisms. Their inverses,
coefficient maps, both-input naturality and normalization characters are
retained. The source-rank-one right comparison and all GL-zero tensor
comparisons retain the entire arbitrary zero-rank carrier.

Minus exactness uses compact containment of the actual radical, character
localization exactness by compact averaging, continuous pullbacks and
character twists. Iterated derivative exactness composes these proved
short-exact functors and equality casts. The product restriction sequence
used by `LeibnizRestrictionExact` is the actual two-orbit Mackey sequence;
its differentiated sequence follows from proved derivative exactness.
The remaining gluing, splice and index arguments are finite filtration and
category algebra. The recursion and cast lemmas reused from
`RightMixedProductDerivativePositive` are definitional equalities; its
conditional filtration theorem is used only with every displayed premise
supplied above.

No excluded analytic segment classification, special-head or ordered-head
existence, multisegment exhaustion, global support decomposition, general
ordered quotient coverage, tempered uniqueness, regular or square-integrable
exhaustion, or square-integrable Langlands classification is imported or
used. The proof uses neither a segment derivative theorem nor a special-head
product irreducibility result. It does not turn a proposition definition
into a proved hypothesis by assumption.

## Remaining host obligations

This result supplies actual product derivative gluing only. It computes no
specific length-two quotient product, proves no such product irreducible,
and proves neither repeated-cuspidal triple transfer. Those concrete
applications and the final exact ambient conjunction remain obligations
of the host task.
