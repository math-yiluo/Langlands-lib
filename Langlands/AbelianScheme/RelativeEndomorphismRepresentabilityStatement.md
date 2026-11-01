# Relative integral endomorphism representability over a noetherian affine base

Author: Worker 143.

The exact proposition is
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement.{u}`.
It is a closed `Prop`-valued definition, with one arbitrary universe parameter
`u`. This module states the representability assertion; it supplies no proof
or axiom asserting that the proposition holds.

For every commutative noetherian ring `R : Type u`, put `S = Spec R`. For
every actual `A : Langlands.AbelianScheme S` whose structure morphism is
`Langlands.AlgebraicGeometry.IsHProjective`, the proposition asserts the
existence of an actual `E : Over S` with the following three properties:

1. The scheme `E.left` is locally noetherian.
2. On the full category of all locally noetherian schemes over `S`, the
   integral relative endomorphism presheaf of `A` is naturally isomorphic to
   the restriction of `yoneda.obj E`.
3. For some small family `P : I → Over S`, with `I : Type u` and every
   `(P i).hom` H-projective, `E` is isomorphic over `S` to the actual scheme
   coproduct of the `P i`.

The only input conditions are the ring conditions, the existing abelian-scheme
structure and H-projectivity of `A`. The representing object, natural
isomorphism and coproduct decomposition are all existential conclusions.
There is no assumed Hilbert representability theorem or geometric certificate.

## Test category and actual endomorphisms

The local `ι` in the Lean definition is Mathlib's full-subcategory inclusion
for the object property
`fun T : Over S => IsLocallyNoetherian T.left`. Thus every locally noetherian
scheme over `S` in universe `u` is a test object, and every scheme morphism
over `S` between two such objects is a morphism in the test category.
The test schemes need not be affine, connected, quasi-compact or of finite
type over `S`.

The presheaf is exactly the composite of `ι.op`, the published
`Langlands.GroupScheme.Cartier.relativeHomFunctor
A.toCommGroupScheme A.toCommGroupScheme`, and
`forget AddCommGrpCat.{u}`. At a test scheme `T`, its elements are the actual
homomorphisms from `A_T` to itself as a commutative group scheme over
`T.left`. The published abelian-scheme category has these same Hom types,
and its base change has this underlying commutative group scheme.
These are integral endomorphisms: no tensor product with the rationals or
localization at isogenies occurs. Forgetting the additive group structure
retains its underlying set.

Along `a : T' ⟶ T`, the restriction is the already constructed
`Langlands.GroupScheme.Cartier.restrict`: base change of the actual
homomorphism along `a.left`, conjugated by the canonical iterated-base-change
comparison isomorphisms. No arbitrary maps on points or unproved comparison
with natural endomorphisms enters the definition.

The right presheaf is `ι.op ⋙ yoneda.obj E`, for the very same existential
object `E` that satisfies the geometric conclusions. Its value is
`Hom_S(T, E)`, with restriction by precomposition. `Nonempty` of the
functor-category isomorphism asserts a natural bijection of these sets,
compatible with every morphism in the full test category. It does not
restrict representation to affine tests or geometric points.

## Coproduct and universe scope

`Sigma.desc (fun i => (P i).hom)` is the structure morphism from the
categorical coproduct `∐ (fun i => (P i).left)` in Mathlib's actual scheme
category to `S`. This scheme coproduct is the disjoint union of the component
schemes. Applying `Over.mk` records its specified structure morphism.
Consequently the isomorphism
`E ≅ Over.mk (Sigma.desc (fun i => (P i).hom))` is an isomorphism over `S`,
not just an identification of underlying spaces or a decomposition of a
presheaf into summands.

The ring, abelian scheme, representing scheme and component schemes all use
universe `u`. The index type also lies in `Type u`, so Mathlib's scheme
coproduct is small in that universe. The assertion is polymorphic in `u`.
There is no finiteness bound on `I`. The proposition does not require `E`
or its structure morphism to be projective or of finite type.

## Original source and derived specialization

The registered original is Robert E. Kottwitz, *Points on some Shimura
varieties over finite fields*, J. Amer. Math. Soc. **5** (1992), 373–444,
Section 5, printed p.391 / one-based PDF p.19, in the paragraph beginning
with sufficiently small level representability. The source ID is
`kottwitz-1992-points-shimura-finite-fields`, SHA256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
The retained original is
`/home/taskhub/central-library/Kottwitz--Points on Some Shimura Varieties over Finite Fields--1992.pdf`.
PDF pp.18–20 (printed pp.390–392) were read. No retained source errata note
was found.

Kottwitz states the assertion for a projective abelian scheme over an
arbitrary locally noetherian base, on locally noetherian schemes over that
base, and identifies it as a consequence of Hilbert schemes. This Lean
proposition is its noetherian affine-base, H-projective specialization.
The abelian-scheme bundle uses the Library's explicit commutativity
convention.

Here H-projectivity means a closed immersion into some finite projective
space over the same ring `R`, using the Library's polynomial-Proj model.
On input this is an explicit projectivity hypothesis. On output the use of
finite projective spaces is a derived specialization of the source's
projective components over the noetherian affine base: a finite type
quasi-coherent module on an affine base is a quotient of a finite free
module, permitting a projective embedding into finite projective space.
Local noetherianness of the disjoint union is also a derived consequence
of the projective components over the noetherian base.
These translations are included in the proposition's intended mathematical
content; this module proves neither them nor representability.
