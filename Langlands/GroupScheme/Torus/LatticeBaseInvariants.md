# Canonical base change into Galois-invariant lattices

Worker 1107, with Worker 1001's contribution to the character-injectivity route
and identification of the existing character fixedness API.

This is a derived internal construction using the published actual character
and cocharacter Hom groups, canonical `Gm` base-change comparisons, geometric
coefficient transport, faithful field pullback and Mathlib's invariant submodules.
It supplies canonical integer-linear maps from the lattices over the original
base ring to the invariant parts of the lattices after base change. These maps
are injective for every field extension.

## Cocharacter evaluation and fixedness over schemes

Let `b : S → B` be any morphism of schemes and let `T` be a commutative group
scheme over `B`. The existing `cocharacterLattice.baseChange b T` pulls back an
actual morphism `Gm_B → T` and precomposes with the inverse canonical `Gm`
comparison. For every test `U` over `S` and every `x : U → Gm_S`,
`cocharacterLattice.baseChange_points` identifies its value through
`baseChangePointsEquiv` with the original cocharacter at the same unit,
read over the underlying `B`-test `(Over.map b).obj U`.

If `a : S → S` satisfies `a ≫ b = b`, then
`cocharacterLattice.transport_baseChange` proves that geometric transport
along `a` fixes this canonical base change. The proof evaluates both morphisms
on all test schemes, applies the published transport and base-change point
formulas, and uses naturality of the `Gm` point equivalence. The descent test
isomorphism has identity underlying scheme map, so its action on units is the
identity. The endomorphism need not be invertible. There are no assumptions of
reducedness, smoothness, affineness, finite type, or that `T` is a torus.

The corresponding character fixedness and Galois fixedness are reused from
`Rational/CharacterBaseChange`: `characterLattice.transport_baseChange` and
`characterLattice.galoisRepresentation_baseChange`. This module does not
redeclare them.

## Faithful pullback and character injectivity

Assuming `(Over.pullback b).Faithful`,
`rationalCharacters.baseChange_injective` proves injectivity on actual
rational characters of any group scheme `G` over `B`, including a
noncommutative one. An equality after base change gives an equality after
postcomposition with the canonical `Gm` comparison. Cancel that isomorphism,
then apply faithfulness of the induced pullback on group objects.
`characterLattice.baseChange_injective` is the specialization to a commutative
group scheme, using the definitional identification of its characters with
actual rational characters.

For fields `k` and `K` in the same arbitrary universe, with any `k`-algebra
structure on `K`, `rationalCharacters.algebraBaseChange_injective` installs the
published `GaloisCocharacterDescent.faithful_algebraPullback`. Its commutative
specialization is `characterLattice.algebraBaseChange_injective`.
`cocharacterLattice.algebraBaseChange_injective` is a lattice-facing wrapper
of the already published
`GaloisCocharacterDescent.baseChangeCocharacter_injective`, with the same
actual canonical base-change formula. No finite-dimensionality, Galoisness,
separability, affineness, or torus hypothesis is used in these field results.

## Integer-linear maps to invariant lattices

Let `k` and `K` be commutative rings with a `k`-algebra structure on `K`, and
let `T` be a commutative group scheme over `Spec k`. The theorem
`cocharacterLattice.galoisRepresentation_baseChange` specializes the scheme
fixedness result to every `σ : K ≃ₐ[k] K`.

For either `characterLattice` or `cocharacterLattice`,
`baseChangeToInvariants k K T` has type

`lattice T →ₗ[ℤ] (galoisRepresentation k K T).invariants`.

Here the representation and lattices are the published ones of the actual
base-changed group scheme, and the codomain is Mathlib's invariant submodule:
its elements are fixed by every `k`-algebra automorphism of `K`. The map is the
existing additive base-change map, viewed as an integer-linear map and
restricted in codomain using the proved fixedness. In each namespace,
`coe_baseChangeToInvariants` states that forgetting invariant membership
recovers exactly canonical base change. Over any field extension,
`baseChangeToInvariants_injective` follows by forgetting the subtype equality
and applying the corresponding lattice injectivity result.

The invariant maps are defined even for a noninjective map of rings, but their
injectivity theorems here assume fields. They do not assert that every invariant
character or cocharacter descends. They impose no topology or continuity
condition, and do not assert norm-one lattice vanishing, anisotropy, or a
classification equivalence.
