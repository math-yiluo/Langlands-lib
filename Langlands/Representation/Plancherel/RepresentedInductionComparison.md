# Actual represented and literal Levi induction comparison

This internal comparison uses the canonical point maps, the full rational-norm
character homeomorphism and the published actual normalized-induction functor.
It introduces no detector-existence assertion. The field and representation
carrier have independent universes.

The local affine, point-topology and Hausdorff instances have explicit names
specific to this module. This lets the comparison and the unchanged generic
irreducibility target coexist in one Lean environment without generated
declaration-name collisions.

`intrinsicLeviRep` pulls a literal Levi representation back to its intrinsic
rational points. The two canonical Levi point homeomorphisms have the same
underlying point map. `representedLeviTwistEquiv` therefore identifies the
corresponding full unramified twists after inverse pullback, on the original
vector space via its identity linear equivalence. The inverse pullback includes
the explicit equality between the point-image subgroup used by represented
induction and the range-carrier subgroup used by the literal model.
`intrinsicLeviRep_isIrreducible_iff` applies the published preservation of
irreducibility under pullback by a continuous multiplicative equivalence.

`representedInductionLeviEquiv` compares the represented
`leviInductionFunctor` of that intrinsic twist with the actual
`UnramifiedLeviInduction`. It allows any supplied geometric unipotent radical
whose multiplication with the Levi is an isomorphism on the represented side,
and the displayed geometric radical, semidirect decomposition and closedness
on the literal side. The root presentation identifies the two radical point
images. A private helper first transports the parabolic, Levi and radical
subgroups along explicit subgroup equalities and then applies the published
normalized-induction equivalence. The published unimodularity theorem for the
actual geometric radical identifies positive full-parabolic normalization with
positive Levi normalization. Thus both the original action and the
normalizing modulus are compared.

`canonicalRepresentedInductionLeviEquiv` specializes this construction to the
root presentation's actual canonical radical. Connected reductivity supplies
smoothness, after which the published canonical-radical and multiplication
theorems supply the represented-side hypotheses. No extra radical choice is
needed for this specialization.

`representedInduction_uniformDetector_transfer` retains a common detector
as an explicit hypothesis: every irreducible subquotient of every represented
intrinsic-Levi unramified twist has a nonzero vector fixed by the supplied open
subgroup `K`. The full rational-norm character homeomorphism selects the
corresponding represented parameter for each literal parameter. The comparison
equivalence gives an isomorphism of smooth representations; transport of
subquotients along its inverse lets the same detector hypothesis apply. The
conclusion therefore detects all irreducible subquotients of all the literal
positive Levi-normalized twists with that same `K`.

These are derived comparisons of published constructions. They assert no
existence of a uniform detector, compactness of `K`, square-integrability
transport, or existence of an irreducible induced fiber. In particular, they
do not prove generic irreducibility or the host task's nonempty open locus.
