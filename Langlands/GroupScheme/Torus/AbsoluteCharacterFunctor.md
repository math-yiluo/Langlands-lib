# The absolute Galois character functor of field tori

For a field `k : Type u`, `FieldTorus k` is the full subcategory of actual
commutative group schemes over `Spec k` satisfying `IsTorus`. Its objects
become finite products of `𝔾ₘ` over some field extension, and its morphisms
are all homomorphisms over `k`. `FieldTorus.toMultiplicativeTypeGroup`
includes these objects and morphisms into the category of groups of
multiplicative type.

`FreeDiscreteGaloisModule.{u,v} k` is the full subcategory of
`FGDiscreteGaloisModule.{u,v} k` whose underlying `ℤ`-modules are free. The
ambient category supplies finite generation and a continuous action for
the discrete topology. Morphisms are equivariant integral linear maps.

`FieldTorus.characterFunctor k` is the contravariant functor to
`FreeDiscreteGaloisModule.{u,u} k`. Each torus remains a torus after base
change to the separable closure and splits there. The character lattice of
a split torus with a finite indexing type `I` is isomorphic to `I → ℤ`, so
it is free. This permits the lift through the full subcategory.
`FieldTorus.characterFunctor_forget` is a definitional equality with the
published multiplicative-type character functor on tori. The action is the
canonical Galois transport on separable-closure characters, and the map on
homomorphisms is pullback along base change.

## Provenance

Milne, *Algebraic Groups* (2017), Definition 12.14, printed p. 236 (PDF p.
252), gives the torus property. Section 12.g, printed pp. 239–240 (PDF pp.
255–256), defines the separable-closure character functor and identifies
tori with the torsion-free character objects among groups of multiplicative
type. A finitely generated torsion-free integral module is finite free.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The full-subcategory construction derives from the published
`MultiplicativeTypeGroup.characterFunctor`. Membership in the target uses
`IsTorus.baseChange_of_isAlgebraic`, `toriAreSplit_of_isSepClosed` and
`TorusSurjectionIsogenySection.characterLattice_free_finite`. These prove
that the functor lands in finite free modules. Essential surjectivity and
the equivalence are separate theorem targets.
