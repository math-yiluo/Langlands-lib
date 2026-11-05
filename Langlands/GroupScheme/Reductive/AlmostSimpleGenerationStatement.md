# Generation by normal almost-simple subgroups

Author: Worker 1454.

`SemisimpleAlmostSimpleGenerationStatement.{u}` is the following proposition
for actual group schemes over any algebraically closed field `k : Type u`,
without a restriction on its characteristic. If `G` is semisimple and
`d : D → G` is a closed subgroup inclusion whose full range functor contains
the range of every closed normal almost-simple subgroup `a : A → G`, then
the range of `d` is the whole functor of points of `G`. The definition of
almost-simple is the corrected one in `AlmostSimple.md`. Containment,
normality, and the conclusion use all test schemes over `Spec k`.

The source is J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, Theorem 21.51, printed pp.440–441 (PDF
pp.456–457), first assertion, and Note 21.55 on printed p.441. The first
assertion gives finitely many normal almost-simple factors whose multiplication
is a surjective homomorphism. A closed subgroup containing those factors must
be the entire smooth group scheme. The stated proposition retains this
generation consequence; it does not assert finiteness, pairwise commutation,
or finiteness of the multiplication kernel.

The official author errata,
`milne-2017-algebraic-groups-errata-2026-11-02`, correct Definition 19.7 on
printed p.399 and state that the proof of Theorem 21.51 was rewritten in the
2022 reprint. This is a statement target, not a proof by citation or a use of
the uncorrected proof. Its independent proof remains required. In particular,
no almost-simple decomposition or root-group generation is assumed as an
extra premise of this proposition.

This is the substantial structural prerequisite for the semisimple normal
complement construction. It says nothing about a chosen smooth connected
normal subgroup or the existence of a complement, and it does not assert
flatness or surjectivity of a multiplication involving a proposed complement.
