# Actual vector-group homomorphisms from central Galois products

This internal construction takes fields `k, L : Type u`, a finite Galois extension
`L/k`, and an affine group scheme `G/k`. For a natural number `n`, its input is an
actual `G`-point over `L[X₁,…,Xₙ]` belonging to the full center subgroup functor and
satisfying the universal-pair additive identity. It constructs an actual
homomorphism from the `n`-dimensional vector group over `k` to `G`. Extending its
underlying polynomial point to `L` gives the product of all coefficient
conjugates of the input, with the variables fixed.

The full center condition means that the point commutes with every point after
every refinement of its test scheme. Pullback along any algebra map preserves
this condition. Thus `centralAffinePoints` is a commutative group even when `G`
is noncommutative. `substituteAlg` substitutes base-field polynomials while
retaining the extension-field coefficients; its compatibility with coefficient
maps is checked on constants and variables. The universal-pair additive identity
defines the subgroup `centralAdditivePoints`, which coefficient maps preserve.
The substitution helpers allow arbitrary variable types in `Type`, including
`Fin n` and its twofold disjoint union.

For small variable types, `liftVariables` and `lowerVariables` rename variables
along `ULift.up` and `ULift.down`. Their composite is the identity, and both
commute with coefficient maps. `descendSmallVariables` uses these maps and the
existing effective polynomial-point descent to descend an invariant point.
Its extension recovers that point. Coefficient extension is also injective on
small-variable points, by the actual global-section coordinate equivalence and
injectivity of polynomial coefficient extension.

`centralConjugateProduct` multiplies the entire finite family of coefficient
conjugates in the full center. Left translation of the Galois group permutes the
factors, proving invariance. Each conjugate satisfies the additive identity;
closure of `centralAdditivePoints` under products proves the identity for the
product. `centralNormPoint` descends this invariant point. Substitution commutes
with coefficient extension, so injectivity on the polynomial algebra in two
independent tuples reflects the additive identity to the descended point.
The existing `homOfAdditive` then constructs `centralNormHom`, and
`centralNormHom_extension` proves the stated extension formula.

These arguments use the polynomial universal property, the existing
coefficientwise finite-Galois descent, the full-center functor and the existing
vector-group homomorphism constructor. They are internal constructions, with
no division by the extension degree. The result allows all characteristics and
all fields; it imposes no commutativity, smoothness, connectedness or unipotence
condition on `G`. It does not yet assert full-center membership after descent,
nontriviality, a nonzero tangent, split-unipotence descent or maximal-torus
conjugacy.
