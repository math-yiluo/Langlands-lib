# Statement: induction preserves étale and quasi-étale morphisms

Author: Worker 21.

This module states, without proof, that induction of analytic spaces with
group actions (`InducedSpace.inductionFunctor`, module
`InducedSpaceAdjunction`) preserves quasi-étale and étale morphisms. It
contains one Prop-valued definition,
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.MorphismPropertyStatement`.

## The statement

`MorphismPropertyStatement : Prop`. Let `K` be a complete ultrametric normed
field in universe `u`, `G : Type z` a group and `H` a subgroup. Let
`f : X ⟶ X'` be a morphism of `Action (LocalizedCategory.{u, max z v, max z v}) H`.
Then:

1. if `f.hom` is quasi-étale (Library `quasiEtale`, module `QuasiEtaleSite`),
   so is `((inductionFunctor H).map f).hom : X_{G/H} ⟶ X'_{G/H}`;
2. if `f.hom` is étale (Library `etale`, module `EtaleSite`), so is the
   induced morphism.

By `copy_inductionFunctor_map`, the induced morphism sends the copy of `X`
indexed by `c ∈ G/H` to the copy of `X'` indexed by `c`, by `f`. It is the
disjoint union of copies of `f`. The statement says that this disjoint union
inherits the property from `f`. No topology on `G` is involved.

## Original source and derived provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, Example 1.2.1(i), printed p.3: "Let N be an open subgroup of a
topological group G, and let X be an N-space. Then the morphism
X(N) → X_{G/N}(G) induces an isomorphism of sites X(N)_qét ⥲ X_{G/N}(G)_qét
(resp. X(N)_ét ⥲ X_{G/N}(G)_ét) and, therefore, an isomorphism of the
corresponding topoi."

Berkovich does not state this property separately. It is the derived input
that lets induction send objects `U(N) → X(N)` of the quasi-étale (resp.
étale) site to objects `U_{G/N}(G) → X_{G/N}(G)`. It is used in this way in
`InducedEquivariantSite`. Quasi-étale and étale morphisms are local on the
source (Berkovich, *Vanishing cycles for formal schemes* (1994), registered
as `berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed p.544;
Berkovich 1993, Definition 3.3.4). The expected proof restricts to the open
and closed copies.

## Scope

This is a `lean.statement`: nothing is proved here.
