# The absolute-Galois character anti-equivalence

This statement uses the actual character functor constructed from the
independently published finite-generation and smoothness theorems.
No proof of the equivalence is supplied here.

`Langlands.GroupScheme.MultiplicativeTypeAbsoluteEquivalenceStatement.{u}`
asserts, for every field `k : Type u`, that the specific functor

```text
MultiplicativeTypeGroup.characterFunctor k :
  (MultiplicativeTypeGroup k)ᵒᵖ ⥤ FGDiscreteGaloisModule.{u,u} k
```

has Mathlib's `Functor.IsEquivalence` property.

The source is the opposite of the full category of actual commutative
`k`-group schemes satisfying the unchanged `IsMultiplicativeType` predicate.
That predicate requires a finitely generated diagonalizable model after
some field extension. It supplies no chosen finite or separable splitting
field. All ground-field group-scheme homomorphisms are retained.

The target consists of finitely generated integral modules with a smooth
action of the actual automorphism group of the chosen separable closure,
with its Krull topology. Smoothness means open vector stabilizers and is
equivalent to continuity for the discrete module topology. Morphisms are all
equivariant integral linear maps. The target uses carrier universe `u`;
the separate category construction also supports independent module
universes.

The specified functor assigns the actual character group over that separable
closure, with the canonical Galois transport representation. It sends a
group-scheme homomorphism to precomposition by its actual scalar extension.
Its action, morphism and forgetful formulas identify these constructions
exactly. Thus the target asks for full faithfulness and essential
surjectivity of this functor. It does not merely assert the existence of
some equivalence of the categories.

No smoothness, connectedness, reducedness, freeness, perfectness or
characteristic restriction is imposed on the group schemes or base field.
Integral torsion modules and finite nonsmooth multiplicative-type groups
are included.

## Source and remaining obligations

The original source is J. S. Milne, *Algebraic Groups* (2017),
registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g, printed p.239 / PDF p.255, defines the actual character
functor with continuous absolute-Galois action. Theorem 12.23,
printed p.240 / PDF p.256, states this equivalence with finitely
generated integral Galois modules. The continuous finite-generation
argument and Galois descent in that section explain passage through finite
Galois extensions. The original pages and complete retained official
2017 errata were read; no correction affects this statement.

This is the absolute-Galois formulation of that theorem, with the existing
group-scheme and smooth-representation constructions. It extends the
separate `MultiplicativeTypeGaloisEquivalenceStatement`, whose source is
restricted to groups split by one specified finite Galois extension.
The proposition here does not assume that finite-level equivalence, finite
splitting or finite factorization: those are possible proof inputs that must
be independently supplied. Exactness of the character correspondence is a
separate assertion, and no equivalence proof is included in this unit.
