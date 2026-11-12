# Models of finitely presented étale scheme equivalence relations

Author: Worker 116.

`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModelExistence`
is a proposition stating descent of an entire étale equivalence relation of
schemes, along every small cofiltered diagram of affine schemes with an actual
limit cone. No proof is supplied in this file.

The relation is the existing `EtaleEquivalenceRelation`: its two projections
are étale, its map into the absolute product is a monomorphism, and on every
scheme of test points it satisfies reflexivity, symmetry and transitivity.
The statement also supplies a compatible structure map from its object scheme
to the limit base.

The hypotheses are:

- the object scheme `E.U` is affine;
- its structure map `b` is locally of finite presentation;
- the two composites `E.t ≫ b` and `E.s ≫ b` agree;
- the relation's structure map `E.t ≫ b` is quasi-compact.

These are finite presentation hypotheses on both scheme objects. Affineness of
the object scheme and of the limit base makes `b` quasi-compact and separated.
The relation's structure map is locally finitely presented by composition with
the étale projection. It is separated because the relation is a monomorphism
into the product of two affine schemes.

The conclusion gives one stage, a new étale equivalence relation `Ei`, a
compatible structure map `bi` to that stage, and actual comparison maps on
object and relation schemes. The stage object scheme remains affine, `bi`
remains locally finitely presented, and the relation over the stage remains
quasi-compact. The object comparison square is a pullback over the chosen cone
leg. The relation comparison is `E.IsCartesianHom Ei fU fR`: it commutes with
the first projections, and the square with the second projections is a
pullback. Thus both the object and relation schemes recover the original ones
by the same change of base; the full equivalence relation laws and étaleness
hold at the stage.

This is an internal, reusable scheme presentation lemma extracted from the
existence argument in the proof of Stacks Project Lemma 70.7.1, Tag 07SK,
the paragraphs descending `W`, `R'`, their projections, and the étale relation
before taking the quotient. Source:
`stacks-limit-morphism-review-2026-11-07`, directory SHA-256
`35f3718ed86ff158e3a8f3765940bd0a8e69861a3af500daf315ec210efe1663`,
file `07SK.html`. The original treats directed sets and more general qcqs
algebraic-space bases. The small cofiltered category formulation with affine
scheme bases is a derived generalization of its scheme descent step, not a
literal quotation.

This statement does not construct a quotient or assert algebraic-space model
existence. Those are separate steps in
`SpaceLimitModelExistenceQuasiSeparated`. In particular, it does not assume the
model-existence result that it is intended to help prove.
