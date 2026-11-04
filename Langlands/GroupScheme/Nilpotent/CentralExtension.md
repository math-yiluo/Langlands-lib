# Nilpotence of maps with central kernel

This internal derived module applies the abstract central-kernel nilpotence
criterion to actual group-scheme homomorphisms. Over any base scheme, centrality
of the scheme-theoretic kernel puts the kernel of the point homomorphism in the
abstract centre for every relative scheme test. The existing kernel membership
criterion and the all-test centre predicate prove this directly. Abstract
nilpotence then reflects from the target to the source without any surjectivity
assumption.

Over a field of arbitrary universe, a lower-central-series bound `d` for every
test of the target gives bound `d + 1` for every test of the source. The image
of the source's `d`th lower central term lies in the target's corresponding
term, which vanishes. Thus the source term lies in the central kernel, and its
next term vanishes. This includes nonreduced tests.

The existing `HasUniformNilpotentPoints.isNilpotentGroupScheme` from
[`TorusDescent`](TorusDescent.md) turns any uniform all-test bound into
geometric nilpotence by the actual base-change point equivalence. Geometric
nilpotence also reflects along every central-kernel map: base change preserves centrality of the kernel using the
canonical kernel comparison, and the pointwise criterion applies over the
algebraic closure. No smoothness, connectedness, affineness, finiteness or
surjectivity hypothesis is needed for this reflection.

Finally, an affine finite-type unipotent target has an existing uniform
nilpotence bound. The preceding result supplies a uniform bound for the source,
and hence geometric nilpotence. All assertions are consequences of the named
Library and Mathlib results; no external structural premise is introduced.
