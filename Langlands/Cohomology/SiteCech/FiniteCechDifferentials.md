# Differential compatibility of finite tuple-cone presentations

This is an internal construction for the finite Čech route to Berkovich's
comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X` in the quasi-étale case
(`AnalyticQuasiEtaleGlobalComparisonStatement`, module
`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement`).
It extends `FiniteCechPresentation`: the canonical decomposition supplied by
limiting tuple cones identifies the actual presheaf nerve maps and the actual
free-sheaf differentials with explicit maps between finite coproducts.

The ambient category is locally small in the presheaf value universe. Fix a
finite basis cover `s`, a limiting wide pullback cone `c n α` for every tuple
`α : Fin (n + 1) → Fin s.size`, a basis index `b n α`, and an isomorphism
`e n α : (c n α).pt ≅ B (b n α)`. All these geometric cones and isomorphisms
are supplied inputs. For the free-sheaf constructions, a commutative ring and
module-sheafification are also supplied.

`cechTupleIndexMap θ` sends the fixed finite enumeration of a tuple `α` to the
enumeration of `α ∘ θ.toOrderHom`. The universal property defines `tupleConeMap`
from the cone for `α` to the cone for the reindexed tuple; its projections are
the selected projections of the source cone, and its base is unchanged.
`tupleMapArrowTo` transports this arrow by the chosen basis isomorphisms and
an explicit equality identifying the target tuple. Its projection and base
identities follow by eliminating that equality, cancelling the basis
isomorphisms, and applying the universal lift identities. `tupleMapArrow`
specializes this construction to the enumerated tuples.

`cechPresentationOfCones_ι_inv_map` proves naturality on one representable
summand. The proof uses extensionality of the presheaf wide pullback: each
projection follows from the projection formula for the canonical presentation
and the transported tuple arrow, and the base follows from their base formulas.
Coproduct extensionality gives `cechPresentationOfCones_inv_map`, whose right
side uses the explicit `Sigma.map'` map `tuplePresheafMap`.

For an arbitrary supplied `CechPresentation`, `ι_freeTermIso_inv` computes each
summand of its inverse free-term comparison as the image of the inverse
presheaf comparison under `freeSheafFunctor`. This follows from the coproduct
comparison isomorphism. Applying the functor to the presheaf summand identity
then proves `cechPresentationOfCones_free_inv_map` for `tupleFreeMap`.

Finally, `tupleFreeBoundary n` is the sum over `j : Fin (n + 2)` of the tuple
map for `SimplexCategory.δ j`, with integer coefficient `(-1)^j`. The theorem
`cechPresentationOfCones_free_inv_d` states the exact square

```
(p.freeTermIso (n + 1)).inv ≫ d (n + 1) n =
  tupleFreeBoundary n ≫ (p.freeTermIso n).inv,
```

with the topology, basis and coefficient arguments explicit in Lean and
`p = s.cechPresentationOfCones ...`. The proof expands Mathlib's alternating
face differential and distributes composition over the finite sum and integer
scalar multiplication, then applies the free nerve-map square term by term.
Its symmetry gives the ordinary differential compatibility needed by a
three-term model.

No equivariant action, compatibility with an action, existence of tuple cones,
exactness, fixed coefficient sections, or cohomological comparison is proved
by this module. These are separate inputs or obligations. The provenance is
internal: the construction follows only from the imported canonical finite
presentation, universal properties, functoriality and the definition of the
alternating face differential; no additional external source is used.
