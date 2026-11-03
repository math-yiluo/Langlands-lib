# A cocharacter with the fixed subgroup of a split torus

Let `k : Type u` be any field, `S` a commutative group scheme over `Spec k`
whose underlying group scheme is a split torus, and `G` an affine group scheme
locally of finite type over `k`. For any actual homomorphism `i : S.toGrp → G`,
`centralizingCocharacter hS i` chooses an actual cocharacter of `S`.
The theorem `centralizingCocharacter_spec` states

```text
Dynamic.centralizer (groupHom (centralizingCocharacter hS i) ≫ i)
  = torusCentralizer i.
```

Both sides are subgroup functors, so the equality includes all test schemes and
all their refinements. The homomorphism `i` need not be injective or closed.
There are no smoothness, connectedness, reductivity, perfectness, or density
assumptions. The field and every test algebra have the same arbitrary universe `u`.
The construction does not assert that the chosen cocharacter is nonzero.

The stronger intermediate result
`AutomorphicAction.exists_cocharacter_fixedSubgroup` applies to every actual
automorphic action `b` of `S` on `G`. It constructs `ν` such that restricting
`b` along `groupHom ν` preserves its full all-test fixed subgroup.

The implemented proof uses actual affine coordinates as follows.

1. `CoordinateWeights.exists_finset_eigenfunction_generators` obtains finitely
   many algebra generators that are eigenfunctions for `b`. The published
   coordinate-weight decomposition splits each element of an initial finite
   generating set into finitely many components. All these components still
   generate the coordinate algebra, because each original generator is their
   sum.
2. `CoordinateWeights.characterValue_cocharacter` evaluates a character `χ`
   along `ν` as the integer power with exponent `latticePairing S χ ν`. It uses
   the existing integer classification of multiplicative-group endomorphisms.
3. `CoordinateWeights.eigenfunction_eq_zero_of_cocharacter_fixed` proves that
   an eigenfunction of nonzero pairing vanishes at a cocharacter-fixed affine
   point over any coefficient algebra `A`. Extend coefficients to
   `LaurentPolynomial A` and use the multiplicative-group point corresponding
   to the universal Laurent unit. Fixedness and the eigenfunction equation
   identify the constant polynomial of the coordinate value with its product
   by `T (latticePairing S χ ν)`. The coefficient at that nonzero exponent
   forces the value to vanish. This uses coefficient equality, with no
   cancellation or reducedness assumption on `A`.
4. Choose one weight for each of the finitely many homogeneous generators.
   The published `IsSplitTorus.exists_pairings_ne_zero` supplies `ν` pairing
   nontrivially with every selected nonzero weight. At a cocharacter-fixed
   point, nonzero-weight generator values vanish by step 3; zero-weight
   generators are invariant under the entire torus. Thus the torus translate
   and the original point have equal coordinate maps on a generating set,
   hence are equal. The published `AutomorphicAction.isFixed_of_affine`
   extends this equality from affine refinements to every test scheme.
   The opposite fixed-subgroup inclusion follows by restriction.
5. Apply the action result to conjugation along `i`. The published comparison
   between conjugation-fixed subgroups and whole-torus centralizers, together
   with the multiplicative-group/dynamic-centralizer comparison, proves
   `IsSplitTorus.exists_cocharacter_centralizer`. The selected definition and
   its specification use this existence theorem.

This is an internal construction derived from the named Library results and
the finite-coordinate Laurent argument above; no external source assertion is
used as a premise. It supplies a cocharacter for a given whole split torus.
It does not construct rational parabolics, identify a dynamic parabolic with a
given rational parabolic, or prove the minimal-parabolic Levi centralizer
statement. Those geometric steps remain separate obligations.
