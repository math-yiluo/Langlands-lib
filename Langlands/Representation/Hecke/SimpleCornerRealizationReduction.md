# Realization through the general corner correspondence and Hecke equivalence

Author: Worker 136. This module supports the proof of
`SimpleCornerModuleRealizationStatement` in
[SimpleCornerRealizationProof](SimpleCornerRealizationProof.md).
Its theorem `Langlands.Hecke.simpleCornerRealization_of_general_theorems`
has three explicit premises:

- `Algebra.NonUnitalModuleCornerSimpleStatements.SimpleInducedQuotientStatement.{u,v}`;
- `Algebra.NonUnitalModuleCornerSimpleStatements.FixedPartInducedQuotientStatement.{u,v}`;
- `HeckeNondegenerateModuleEquivalenceStatement.{u,max u v}`.

It concludes exactly `SimpleCornerModuleRealizationStatement.{u,v}`.
The companion proof module applies this reduction to the published proofs of
those three statements. The reduction itself is conditional; its premises are
ordinary arguments, with no new axioms.

The original mathematical assertion is Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, III.1.5 Theorem (iii),
printed p.61 / PDF p.67, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read PDF pp.66–67. The source refers to I.3.2 for the correspondence,
after establishing the Hecke-module equivalence in III.1.4.

The implementation first identifies the published bi-invariant Hecke corner with
the abstract corner of the normalized-indicator idempotent. Both equivalence maps
keep the underlying Hecke function; their membership certificates are equivalent
by `mem_biInvariant_iff_sandwich`. It also obtains `IsIdempotented` for the Hecke
algebra from the published finite-family normalized-indicator local units.

Transport a given simple concrete corner module `W` along this ring equivalence.
Simplicity is checked using the surjectivity of the action on each nonzero vector.
The first premise then gives the simple nondegenerate module
`N = (H(G) ⊗_{eH(G)e} W)_e`. The III.1.4 premise gives a smooth representation `A`
with an isomorphism from its actual integrated Hecke module to `N`, in carrier
universe `max u v`. Van Dantzig's theorem supplies the nonarchimedean group
instance required by III.1.4 from the target's locally profinite hypotheses.
Categorical simplicity transports to `A`.

A private helper shows that a categorically simple smooth representation is
irreducible in the published invariant-submodule sense. It excludes a zero carrier
using its nonzero identity map. The inclusion of any nonzero invariant subspace is
a nonzero monomorphism and hence an isomorphism, making the subspace the whole
representation.

Finally, identify the actual `K`-fixed vectors with the idempotent fixed part in
the integrated Hecke module using the published normalized-indicator projection
identities. Apply the fixed-part functor to the Hecke-module isomorphism, and then
compose with the inverse of the corner-linear equivalence supplied by the second
premise. The resulting additive equivalence is linear for the concrete corner:
transporting a concrete scalar back to the abstract corner makes each constituent
map linear, and the ring equivalence cancels at the end.

All helper constructions are internal to this realization reduction. The
complex representation is supplied by the Hecke category equivalence; the proof
requires no additional scalar compatibility hypothesis on the tensor carrier.
