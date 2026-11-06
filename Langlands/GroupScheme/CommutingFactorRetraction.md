# Retraction onto a factor of a commuting multiplication isomorphism

Authors: Worker 1356; Worker 1326 (consumer interface).

This is an internal construction from the published group-scheme product,
commuting multiplication, kernel and centralizer interfaces. It is not an
existence theorem for complements.

Let `S : Scheme.{u}` be any base scheme, and let `j : H ⟶ G` and `i : K ⟶ G`
be homomorphisms of actual group schemes over `S`. Suppose their images
commute on every test scheme:

```text
∀ (T : Over S) (h : T ⟶ H.X) (n : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (n ≫ i.hom.hom).
```

Write `hc` for this condition. Assume that the actual group-scheme
homomorphism `commutingSubgroupMultiplicationHom j i hc : H ⊗ K ⟶ G`
is an isomorphism. The construction
`Langlands.GroupScheme.commutingFactorRetraction j i hc : G ⟶ H` is its
inverse followed by the first product projection.

The supporting theorems prove that:

- `j ≫ commutingFactorRetraction j i hc = 𝟙 H`.
- On each test scheme, the projection sends `j(h)i(n)` to `h`.
- A point of `G(T)` is sent to the identity if and only if it is in the
  range of `K(T) → G(T)` on that same test scheme.
- Every such point commutes with every point of `H(T)`.
- The range of the actual scheme-theoretic kernel is contained in
  `(AutomorphicAction.conjugation j).fixedSubgroup`, the centralizer of `j`
  with its condition after every change of test scheme.

There are no field, smoothness, connectedness, normality, closed-immersion,
semisimplicity or simple-connectedness assumptions in this construction.
The explicit commutation and multiplication-isomorphism assumptions are
retained. This module does not prove that a prescribed normal subgroup has
a complement, or that a central isogeny is an isomorphism.

## Implemented argument

Inverse multiplication gives a unique pair of coordinates for each point.
Composition with multiplication followed by its inverse proves the
projection formula and the section identity. If the first coordinate is
the identity, multiplication expresses the original point as the second
coordinate's image; the converse is the projection formula. The
commutation hypothesis then proves kernel commutation. The existing
comparison between the conjugation fixed subgroup and all-test
commutation gives the final kernel containment.

This proof is an elementary consequence of the published constructions in
`Reductive.CommutingMultiplication`, `Reductive.NormalCentralizer` and
`CentralIsogeny.Basic`. It is intended as the projection and
kernel-commutation step for the anisotropic-factor centralizer argument.
The arbitrary-field structural existence of the required complement is
a separate proof obligation.
