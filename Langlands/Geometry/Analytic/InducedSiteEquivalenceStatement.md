# Statement: the quasi-étale sites of `X(H)` and `X_{G/H}(G)` are equivalent

Author: Worker 21.

This module states, without proof, Berkovich's Example 1.2.1(i) for
quasi-étale sites, in the form of the induction functor of
`InducedEquivariantSite`. It contains one Prop-valued definition,
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.QuasiEtaleSiteEquivalenceStatement`.

## The statement

`QuasiEtaleSiteEquivalenceStatement : Prop`. Let `K` be a complete
ultrametric normed field in universe `u`. Let `G : Type z` be a topological
group (`IsTopologicalGroup G`), `H` an open subgroup, and
`X : GSpace.{u, max z v, max z v} K H` an `H`-space. Let `hC` and `hQ` be
proofs of `InducedSpace.ContinuityStatement` and
`InducedSpace.MorphismPropertyStatement`. Then:

1. `quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))`,
   `U(H) ↦ U_{G/H}(G)`, is an equivalence of categories (Mathlib's
   `Functor.IsEquivalence`);
2. it preserves and reflects coverings. For every object `U` and presieve
   `R` on `U`, the image `R.map (quasiEtaleSiteInduction hH hC hQ X)` is a
   covering of the image of `U` in `equivariantQuasiEtalePrecoverage` exactly
   when `R` is a covering of `U`.

The coverings are Berkovich's (module `EquivariantQuasiEtaleSite`): families
whose underlying families are quasi-étale coverings. An equivalence that
preserves and reflects the generating coverings identifies the generated
topologies `X(H)_qét` and `X_{G/H}(G)_qét`. This is Berkovich's isomorphism of
sites.

The hypotheses `hC` and `hQ` are needed to define the functor. If either
statement were false, this statement would hold vacuously. It is meant to be
proved together with, or after, those two statements.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, Example 1.2.1(i), printed p.3: "Let N be an open subgroup of a
topological group G, and let X be an N-space. Then the morphism
X(N) → X_{G/N}(G) induces an isomorphism of sites X(N)_qét ⥲ X_{G/N}(G)_qét
(resp. X(N)_ét ⥲ X_{G/N}(G)_ét) and, therefore, an isomorphism of the
corresponding topoi."

Derived choices: Berkovich's comparison is the pullback along
`X(N) → X_{G/N}(G)`. The statement uses its expected inverse, induction (see
`InducedEquivariantSite`). Only the quasi-étale case is stated. The étale case
and the isomorphism of topoi are not stated.

## Expected proof route

Not formalized here. A quasi-inverse is the preimage of the copy indexed by
`H` with its action of `H`. Objects over `X_{G/H}` with an action of `G` are
determined by the part over that copy. Induced morphisms are disjoint unions
of copies (`copy_inductionFunctor_map`). Quasi-étale coverings are local on
the open and closed copies.

## Scope

This is a `lean.statement`: nothing is proved here.
