# Existence of an irreducible induced unramified twist

Author: Worker 145.

This module states
`Langlands.Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement`.
It supplies no proof. This is a derived existence consequence of Konno's
Theorem 4.2, rather than a transcription of its full analytic conclusion.

## Exact content

For a connected reductive group `G` over a nonarchimedean local field `k` of
any characteristic, let `p : P ⟶ G` be an actual rational parabolic,
`l : M ⟶ P` a rational Levi, and `r : U ⟶ P` a geometric unipotent radical,
with `subgroupMultiplication l r` an isomorphism. For every irreducible
admissible smooth complex representation `ρ` of `M(k)`, the statement asserts
an unramified character `ψ` for which the actual normalized induction
`leviInductionFunctor p l r hp hr hl hmul` of `ρ.twist ψ` is irreducible.

The topology on `G(k)` is canonical `RationalPointFamily.pointTopology`;
local compactness and the nonarchimedean group property are displayed
hypotheses. The topology on `M(k)` is the published `leviPointTopology`;
its local compactness and nonarchimedean group property come from the
published Levi-point comparison. The field and representation-carrier
universes `u,v` are independent. The field is Hausdorff, as in the published
Renard openness interface. There is no restriction to split, quasisplit,
characteristic-zero, positive-rank or supercuspidal data. The case `P = G`
is included.

The characters belong to `Plancherel.unramifiedCharacters` of the full
family of rational-character norms of the actual group scheme `M`. They
are continuous characters into `ℂˣ` that kill the common norm kernel, with
smooth twisting supplied by `unramifiedCharacter_isOpen_ker`. This is the
same character family used in `InducedIrreducibilityOpenStatement` in
`RenardGenericIrreducibilityStatements`. In particular the statement does
not restrict the parameter to unitary characters or to a rank-one family.
The induction is exactly the published `leviInductionFunctor`, including
its normalization and its pullback through the actual Levi-point map.

## Source and derivation

The registered original is `konno-2003-langlands-classification`, Takuya
Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups*, Kyushu Journal of Mathematics 57 (2003),
383–409. Section 2, printed p.384, permits a nonarchimedean local field of
any characteristic and a connected reductive group. Theorem 4.2, printed
p.402, and its proof on pp.402–405 treat an arbitrary irreducible admissible
representation `π` of the Levi, without a supercuspidality or discrete-series
hypothesis. Corollary 4.3, which assumes square integrability, is not the
source of this statement.

Theorem 4.2 provides a neighborhood of zero in the complexified real
unramified parameter space, in which the induced twist is irreducible when
the real parameter avoids all relative-coroot walls. There is such a
parameter in this neighborhood: finitely many proper real hyperplanes
cannot cover a neighborhood. If there are no relative roots, the wall
condition is empty. Its exponential unramified character is an element of
the full rational-norm family used here. This extracts existence only;
there is no asserted analytic neighborhood or Zariski-open conclusion in
the Lean statement.

Konno chooses parabolics containing a fixed minimal Levi. For the present
single-parabolic conclusion, one may choose the maximal split torus and
minimal Levi inside the supplied rational Levi. The point identification,
exponential parameter comparison, and actual normalized-induction
comparison are part of the proof obligation. Neither a choice of abstract
labels for a Weyl group nor a replacement induction model can discharge it.

## Dependency and proof boundary

The only direct project import is
`Langlands.Representation.Families.RenardGenericIrreducibilityStatements`.
It supplies the already published actual rational parabolic, Levi-point,
normalized-induction, twist and rational-norm character interfaces. No
existing file or statement is changed. No theorem proving this existence
consequence is introduced.

A proof following Konno must establish or reuse his representation-theoretic
inputs at their actual hypotheses: cuspidal support and embeddings, the
Bruhat filtration, Frobenius reciprocity, Jacquet-module detection,
finite-length and admissibility facts where used, and the rank-one
argument behind Lemma 4.1 and Claim 4.2.4, including its use of the Langlands
classification. Claim 4.2.1 supplies local separation of constituents;
Claims 4.2.2–4.2.4 complete the irreducibility argument. These are proof
obligations, not additional premises or external structural assumptions.

For a polynomial locus, this existence statement must be combined with a
proved algebraic-openness theorem and actual coordinate comparisons.
Renard VI.8.4 is the existing separate openness obligation. Applying the
result to two actual parabolics and intersecting their principal opens is
further work. This module proves neither generic irreducibility on a
polynomial locus, generic isomorphism, nor any induced composition-factor
or Grothendieck-class identity.
