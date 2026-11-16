# The actual absolute-Galois character functor

For a field `k : Type u`, `MultiplicativeTypeGroup k` is the full subcategory
of actual commutative group schemes over `Spec k` satisfying the existing
`IsMultiplicativeType` predicate. An object has only the original property:
it becomes diagonalizable with a finitely generated abelian character group
after some field extension. No finite or separable splitting field is required
as extra data. All ground-field homomorphisms remain morphisms.

`MultiplicativeTypeGroup.characterFunctor k` is a contravariant functor to
`FGDiscreteGaloisModule k`, with carrier universe `u`. Its object is the full
actual character group over the chosen separable closure, with exactly
`characterLattice.galoisRepresentation`. Its morphism is the pullback along
the actual base-changed homomorphism. The module can have torsion.

The construction lifts the published unrestricted `galoisFunctor` through
the full subcategory of smooth representations, using the proved open-stabilizer
assertion, then through the full subcategory of finitely generated integral
modules, using the proved finite-generation assertion. The functor laws are
inherited. `characterFunctor_representation` and `characterFunctor_map_apply`
give the actual action and map formulas. `characterFunctor_forget` identifies
the composite with the original unrestricted functor by definitional equality.

This is a derived categorical packaging of actual constructions. It does not
assert full faithfulness, essential surjectivity, an anti-equivalence, or finite
Galois splitting. Those require their own exact statements and proof
publications.

## Provenance and inputs

The imported theorems `multiplicativeTypeAbsoluteCharacterFinite` and
`multiplicativeTypeAbsoluteCharacterSmooth` prove the two membership properties
without changing `IsMultiplicativeType`. Both are independently published
Library results. The construction uses their public imports and the existing
`characterLattice.galoisFunctor`; it introduces no additional mathematical
premise. The three formula lemmas are definitional equalities of this
construction.

This packages the character functor described in J. S. Milne, *Algebraic
Groups* (2017), section 12.g, printed p.239 / PDF p.255, with the target
category of Theorem 12.23, printed p.240 / PDF p.256. The registered source
is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original pages and complete retained official 2017 errata were read;
no correction affects these passages. The full-subcategory packaging is
derived from the published group-scheme and representation constructions.
