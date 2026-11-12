# Descent of eight properties of algebraic-space morphisms along limits

`Langlands.AlgebraicGeometry.AlgebraicSpace.spaceLimitPropertyDescent`
proves the published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentStatement.{u}`
in every universe `u`, with no additional hypotheses.

For a small cofiltered diagram of affine schemes with an actual limit cone,
take any stage morphism between quasi-separated algebraic spaces whose
surjective étale atlases have locally finitely presented, quasi-compact
structure morphisms. For each of the following eight properties, the morphism
has the property after base change to the limit if and only if it has it after
base change to some incoming stage: closed immersion, separated, proper,
smooth, affine, open immersion, finite, and nonempty geometrically connected
fibres. The predicates and quantifiers are exactly those of
[`SpaceLimitPropertyDescentStatement`](SpaceLimitPropertyDescentStatement.md).

## Implemented proof

The proof applies `spaceLimitPropertyDescent_of_foundations` from
`SpaceLimitProperDescentOfSchemeCovers` to two published theorems:

- `representedAtlasEffectivity` from `RepresentedAtlasEffectivityProof`
  proves `RepresentedAtlasEffectivityStatement.{u}`. It supplies effective
  descent from a surjective étale target atlas for closed immersions,
  affine morphisms, open immersions and finite morphisms, including the
  representability conclusion.
- `properSchemeCover` from `ProperSchemeCoverProof` proves
  `ProperSchemeCoverStatement.{u}`. It supplies a proper, locally finitely
  presented scheme cover for a proper algebraic space over an affine base
  with the specified atlas.

The assembly theorem combines the four represented-property limit reductions
with proved model uniqueness and the first theorem. It combines proper
scheme-cover descent with the second theorem to obtain the properness clause.
The other three entries are the published separatedness, smoothness and
nonempty-geometrically-connected-fibre descent theorems. The conjunction is
assembled in the exact order of the target statement.

Both foundational inputs are discharged by the imported proofs. Thus the
entry theorem has no effectivity or cover-existence premise. The statement's
Lean/Markdown pair and its import closure are unchanged.

## Provenance and scope

This is an internal composition of the published reduction and foundational
proofs, whose paired Markdown explains their constructions. The target's
original source and precise derived formulation are recorded in
[`SpaceLimitPropertyDescentStatement.md`](SpaceLimitPropertyDescentStatement.md):
Conrad, *Weil and Grothendieck approaches to adelic points*, Theorem 3.4(2)
(printed p.5), extended to algebraic spaces on printed p.13. The target
contains eight properties; flatness and pure fibre dimension are outside its
scope. This proof retains the full arbitrary-universe and cofiltered-diagram
generality of that target.
