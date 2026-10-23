# Affine group schemes from explicit corepresentations

This module constructs a group scheme from a group-valued functor on
commutative algebras whose underlying set-valued functor has a specified
corepresentation. It also constructs group-scheme homomorphisms from natural
group homomorphisms and identifies their underlying spectrum maps and action
on affine points.

All declarations lie in `Langlands.GroupScheme.Corepresented`. The base ring
`R`, its commutative algebras, and the point groups use one arbitrary universe
`u`. The hypotheses are an actual functor `F : CommAlgCat R ⥤ GrpCat`, an
algebra `B`, and `e : (F ⋙ forget GrpCat).CorepresentableBy B`. Thus `e`
contains a natural equivalence from algebra homomorphisms `B → S` to `F(S)`.
The module does not assume a group scheme as input.

## Internal provenance

This is an internal categorical adapter for the explicit coordinate algebras
used in the unitary Shimura development. It combines the published
`Langlands.AbelianScheme.GroupScheme` definition of a group scheme as a group
object in `Over (Spec R)` with Mathlib's representability and affine spectrum
constructions. It attributes no new formula or theorem to an external paper.

The implementation uses `GrpObj.ofRepresentableBy`,
`yonedaGrpObjIsoOfRepresentableBy`, and `yonedaGrpFullyFaithful` from Mathlib's
cartesian group-object API, together with `algSpec`, `algSpec.fullyFaithful`,
and its induced functor `mapGrp` from
`Mathlib.AlgebraicGeometry.Group.Affine`. The multiplicative point comparison
uses `Functor.FullyFaithful.homMulEquiv`. The commutative variant uses
`CommGrpObj.ofRepresentableBy` and preservation of commutative monoid objects.
These are reused constructions, not copied proofs.

## Construction and point recovery

`presheaf F` regards `F` as a presheaf on the opposite category of algebras,
using the double-opposite equivalence. `representableBy F e` transports the
hom-set equivalence by taking the opposite of each algebra morphism. Its
naturality is exactly the naturality field of `e`.

`cogroup F e` is the resulting group object on `op B`. The word cogroup
refers to its interpretation on algebras: multiplication, identity and inverse
are genuine morphisms in the opposite algebra category, with the group-object
laws supplied by the represented group functor. `pointsIso F e` identifies
its group-valued Yoneda functor with `presheaf F`.

`groupScheme F e` applies the product-preserving affine spectrum functor to
this group object. Its underlying object is `(algSpec R).obj (op B)`, as
recorded by `groupScheme_X`: the actual affine scheme `Spec B` over `Spec R`.
The construction includes its multiplication, identity and inverse morphisms
and their laws.

For every commutative `R`-algebra `S`, `affinePointsEquiv F e S` is a group
isomorphism between morphisms over `Spec R` from `Spec S` to this group scheme
and `F(S)`. It first uses full faithfulness of `algSpec` to recover an algebra
map and then uses `pointsIso`. The supporting equations state:

- `affinePointsEquiv_apply`: a scheme map is sent to `e.homEquiv` of its
  recovered algebra map.
- `affinePointsEquiv_map`: for the spectrum map induced by `f : B → S`,
  this value is exactly `e.homEquiv f`.
- `affinePointsEquiv_naturality`: precomposing a point by the spectrum map of
  `g : S → T` corresponds to applying `F.map g`.

The naturality proof uses preservation of composition by the inverse hom-set
map and then the naturality of `e`. These comparisons apply to every algebra
in the stated universe, without field or reducedness assumptions.

## Natural homomorphisms and commutativity

Given a second corepresented functor `G`, represented by `C` with equivalence
`d`, and a natural group homomorphism `α : F ⟶ G`, `cogroupMap e d α`
uses the fully faithful group-valued Yoneda functor to construct the induced
cogroup homomorphism. `cogroupMap_hom` identifies its underlying algebra map
as

`d.homEquiv.symm (α.app B (e.homEquiv (𝟙 B))) : C ⟶ B`.

Thus the coordinate map classifies the image of the universal source point.
`groupSchemeMap e d α` applies `algSpec.mapGrp` to this homomorphism.
`groupSchemeMap_hom` identifies its underlying scheme morphism with the
spectrum of that exact algebra map. `groupSchemeMap_affinePoints` proves
that postcomposing any affine point with this morphism corresponds to
`α.app S` under the two multiplicative point comparisons. The proof uses
corepresentation naturality and the naturality square for `α`.

Finally, `commGroupScheme` starts with `F : CommAlgCat R ⥤ CommGrpCat`.
Commutativity of the represented point groups gives commutativity of the
cogroup, and `algSpec` preserves it, producing the existing
`Langlands.CommGroupScheme` structure on the same underlying affine group
scheme.

The generic adapter imposes no finite-presentation, smoothness, connectedness
or reductivity condition. It does not by itself identify a specific source
with a split torus or construct a Shimura variety. Concrete coordinate-algebra
and natural-homomorphism specializations are separate consumers of this module.
