# Conditional dual abelian schemes over a base scheme

`dualAbelianSchemeFromEvaluation` equips the already constructed dual
commutative group scheme with the three geometric properties in an
explicit proof of `DualSchemeGeometry A hA`. The base `S : Scheme.{u}`
is arbitrary. The construction and its map laws are valid for any such
proof; no unconditional general-base geometry theorem is asserted.

## Source and provenance

This is a derived construction using `DualGroupScheme`,
`DualGroupSchemeMap`, and `RelativeDualSchemeGeometryStatement`. It
extends the existing field constructor by taking the geometry of each
chosen endpoint separately, and does not alter that field constructor.

The source convention is Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, thesis revised March 14, 2021, registered
as `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
Definition 1.3.1.1, printed p.67 (PDF p.95), gives the three geometric
properties of an abelian scheme. Theorem 1.3.2.3 and Definition
1.3.2.5, printed p.74 (PDF p.102), describe the dual abelian scheme and
its universal rigidified Poincare bundle. Definition 1.3.2.9, printed
p.75 (PDF p.103), defines dual homomorphisms by pullback of rigidified
Picard-zero classes.

Lan's scheme convention is quasi-separated (printed p.xxvi/PDF p.26).
The separate `RelativeDualSchemeGeometryStatement` retains that
hypothesis. If `S` is quasi-separated and that statement is proved,
`geometry S A hA` supplies the local geometry proof used here. For a
base without that hypothesis, a proof of `DualSchemeGeometry A hA`
remains an explicit obligation; this conditional construction does not
extend the source theorem. The exact comparison of the Library's
geometric-fibre functor with the source functor belongs to the geometry
statement's documented proof obligation.

## Explicit inputs

For each endpoint the construction requires the existing
`A : AbelianScheme S`, `hA : HasDualScheme A`, and
`geometryA : DualSchemeGeometry A hA`. The representability proposition
selects an actual universal rigidified family over every test scheme.
The geometry predicate asserts smoothness, properness and geometric
connectedness of that same selected scheme, rather than supplying a
new abelian scheme as data.

It also requires an ordinary line bundle `MA` on the parameter-first
space `dualScheme A hA ×_S A`, together with an actual module-sheaf
isomorphism `poincareFamily A hA ⊗ MA ≅ O`. This input is used by the
existing construction of the inverse group operation.

The seven fixed-map inputs remain explicit:

- `pullbackTensorComparisonIsIsoStatement`;
- `PicardZeroPullbackStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`.

They concern the Library's actual tensor and pullback maps. This
module neither proves those propositions nor assumes a desired dual
map or group structure as additional data.

## Construction and implemented proofs

The `toCommGroupScheme` field of `dualAbelianSchemeFromEvaluation` is
exactly `dualCommGroupSchemeFromEvaluation`. Its smoothness, properness
and geometric connectedness fields are the corresponding projections
of `geometryA`. The two simplification lemmas for `X` and
`toCommGroupScheme` are proved by reflexivity, preserving the chosen
parameter scheme and all the already constructed group operations.

`dualAbelianSchemePointMulEquiv` reuses multiplicative Poincare
classification on every `T : Over S`, including nonreduced schemes.
Its application lemma is reflexivity and identifies the class with
`dualPointClass`. The original universal family and its conventional
Poincare bundle on `A ×_S dualScheme A hA` remain available unchanged
from `DualScheme`.

For `f : A ⟶ B`, `dualAbelianSchemeMapFromEvaluation` is exactly the
existing `dualCommGroupSchemeMapFromEvaluation`, now viewed as an
abelian-scheme homomorphism from the constructed dual of `B` to that
of `A`. The lemma ending in `_hom` identifies its underlying scheme
morphism with `(dualSchemeMap homPicardZeroPullback f hA hB).left` by
reflexivity. Identity and reversed composition reuse the existing
group-scheme equations, since the Hom types of abelian schemes are
those of their underlying commutative group schemes. The identity law
uses the same representability, geometry and inverse/evaluation data
at both ends; the composition law uses the same data at its middle
endpoint.

Finally, `dualAbelianSchemeFromEvaluation_field` identifies the result
on `Spec k`, using `geometry k F hF`, with the existing
`fieldDualAbelianSchemeFromEvaluation`. The proof is reflexivity:
both constructions have the same underlying group scheme and the
same geometric proof fields. No existing field theorem is replaced.

## Boundary

The module proves the constructor's comparison and functoriality laws.
It does not supply representability, the geometry theorem, ordinary
inverse existence or missing tensor comparisons. Additivity as `f`
varies, rational dualization, biduality, the Mumford morphism and
polarizations are separate constructions or proof obligations.
