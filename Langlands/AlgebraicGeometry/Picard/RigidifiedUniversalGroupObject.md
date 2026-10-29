# The commutative group object on a universal rigidified parameter

Let `f : X ⟶ S` have a section `ε` with `ε ≫ f = 𝟙 S`. Let `P : Over S`
carry a rigidified family `L : relative f ε section_eq P` that is universal
(`IsUniversal f ε section_eq L`). This module makes `P` a commutative group
object of `Over S`. On `T`-points the group law is the tensor product of
rigidified line-bundle classes on `X ×_S T`. The identity is the trivial
class and the inverse is the tensor inverse.

## Inputs

The construction takes the same explicit named hypotheses as the Library
module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassGroup`:
`pullbackTensorComparisonIsIsoStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, `PullbackTensorSymmetryStatement`,
`LocallyFreeRankOneIffTensorInvertibleStatement Y` for every scheme `Y`, and
`PullbackTensorCompositionStatement`. These are ordinary Library propositions,
and each is passed as an explicit argument, so a caller must supply a proof of
it. Supplying the proofs yields the group object; no group axiom, inverse
function or group-valued presheaf is supplied by the caller.

Six of these propositions have published theorems in the namespace
`Langlands.Scheme.Modules` (files under `Langlands/AlgebraicGeometry/Modules`):
`pullbackTensorComparisonIsIso`, `pullbackTensorUnitCoherence`,
`explicitPullbackTensorAssociativity`, `tensorMonoidalLeftUnitorComparison`,
`pullbackTensorSymmetry` and `pullbackTensorComposition`. The local comparison
`LocallyFreeRankOneIffTensorInvertibleStatement Y` is equivalent to the
conjunction of the two directional statements in
`Langlands.AlgebraicGeometry.Picard.LocalComparisonDirections`. When this
module was written, only the direction
`TensorInvertibleLocallyFreeRankOneStatement` had a published proof
(`Langlands.AlgebraicGeometry.Picard.tensorInvertibleLocallyFreeRankOne`). A consumer therefore instantiates the
first six arguments with the published theorems. Until the converse direction
is published, the consumer must supply the local comparison itself. Nothing in
this module depends on which of the arguments are proved.

The universality hypothesis `hL` is the published `IsUniversal`: the
classifying map `classifyingMap f ε section_eq L T : (T ⟶ P) → Classes f ε section_eq T`
is bijective for every test object `T : Over S`.

## Declarations

- `classCommGrpPresheaf` is the Library's `classGroupPresheaf` (rigidified
  classes with tensor product as addition) composed with
  `AddCommGrpCat.toCommGrp`. It is the same presheaf of groups written
  multiplicatively.
- `universalClassRepresentableBy` shows that `P` represents the underlying
  presheaf of sets of `classCommGrpPresheaf`. Its bijection is the published
  `classifyingEquiv f ε section_eq L hL T`. Naturality in `T` is the published
  `classifyingMap_comp`, which uses the proved
  `RigidifiedModule.pullbackCoherence`.
- `universalCommGrpObj : CommGrpObj P` is Mathlib's
  `CommGrpObj.ofRepresentableBy` applied to that representation. By the
  Yoneda lemma, a representation of a presheaf of commutative groups gives a
  commutative group object structure on the representing object. The
  structure is a `def`, not a global instance, because it depends on the
  hypotheses and on `L`.
- `universalPointMulEquiv T : (T ⟶ P) ≃* Classes f ε section_eq T` is the
  classifying bijection, as a multiplicative equivalence. Its domain carries
  the group structure on `(T ⟶ P)` induced by `universalCommGrpObj` (Mathlib's
  `Hom.group`/`Hom.commGroup`). Its codomain carries the Library's
  `classesCommGroup`. Its `map_mul'` proof unfolds the multiplication
  `lift p q ≫ μ` and repeatedly uses naturality of the representation
  (`homEquiv'_comp`), as in Mathlib's `yonedaMonObjIsoOfRepresentableBy`.
- `universalPointMulEquiv_apply` states, by `rfl`, that the underlying
  function is `classifyingMap f ε section_eq L T`.
- `classifyingMap_mul`, `classifyingMap_inv` and `classifyingMap_one` are
  the resulting identities. The classifying map sends a product of points to
  the tensor product of classes, an inverse point to the inverse class, and
  the identity point to `trivialClass f ε section_eq T`.
- `one_eq_trivialParameter` says that the identity section
  `1 : Over.mk (𝟙 S) ⟶ P` is the published
  `trivialParameter f ε section_eq L hL` from
  `Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality`. Both
  sections classify the trivial rigidified class (`classifyingMap_one` and
  `classifyFamily_spec`), and universality makes the classifying map
  injective.

## Provenance

This construction is derived; the source has no formal statement of it.
Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(registered `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`;
PDF page = printed page + 4).

- Paragraph (6.2), printed p.88 (PDF p.92), defines the functor
  `P_{X/S,ε} : (Sch/S)^op → Ab` of isomorphism classes of line bundles on
  `X ×_S T` rigidified along `ε`. Its group law is
  `(L, α)·(M, β) = (L ⊗ M, α ⊗ β)`. The Library formalizes this group in
  `RigidifiedClassGroup`. The same paragraph says that if `P_{X/S,ε}` is
  representable, the representing scheme carries a universal rigidified line
  bundle (the Poincaré bundle). Every rigidified bundle on `X ×_S T` is then
  isomorphic to its pullback along a unique `T`-point. The published
  `IsUniversal` formalizes this universal property.
- Chapter VI, §3, printed p.95 (PDF p.99), admits from the general theory
  that `Pic_{X/k}` is a group scheme, and notes that it represents the functor
  `P_{X/k,0}` of line bundles rigidified along the zero section. Theorem
  (6.18), printed p.96 (PDF p.100), uses this group structure through the
  homomorphism `ϕ_L : X → Pic^0_{X/k}`.

The module turns this around. It starts from an actual universal family `L`
(the hypothesis `hL`), not from a representability statement. It then
transports the class group to the representing object by the Yoneda lemma
(`CommGrpObj.ofRepresentableBy`). The source works in (6.2) under its
hypotheses (∗): `f` is quasi-compact and quasi-separated,
`f_*(O_{X_T}) = O_T` for every `T`, and `f` has a section `ε`. The Lean module
keeps the section but does not assume the first two conditions. The class group
needs only the seven named propositions, and the classifying map and the
universality hypothesis need nothing more.

## Scope

The module constructs no Picard scheme. It proves no representability,
smoothness, dimension or reducedness result. The only representability input
is the hypothesis `hL`, which the caller supplies together with `P` and `L`.
