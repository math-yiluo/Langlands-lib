# The commutative group scheme of a chosen dual

This module equips the chosen dual parameter scheme with an actual
commutative group scheme structure. Its multiplication, origin and inverse
are identified with the existing morphisms obtained by Poincaré
classification. The construction uses the proved groups of dual-valued
points on every test scheme.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI,
paragraph (6.2), printed p.88 (PDF p.92), describes tensor multiplication
of rigidified line-bundle classes, parameter pullback, and unique
classification by a universal Poincaré family. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This module is a derived categorical construction from those operations
on the existing geometric Picard-zero classes. It reuses
`DualSchemeInverse`, which constructs actual groups of dual-valued
points from a supplied Poincaré evaluation. Mathlib's
`CommGrpObj.ofRepresentableBy` reconstructs the group-object laws from
the group-valued presheaf and its representation. Its implementation is
in `Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_`, using the
group and monoid constructions in the adjacent `Grp` and `Mon` modules.
No group-object laws are supplied as additional fields by the caller.

The source's hypotheses for identifying the rigidified functor with
the Picard sheaf are not used to assert that identification here.

## Data and hypotheses

Fix an abelian scheme `A/S` over an arbitrary base scheme and a proof
`hA : HasDualScheme A`. This is the existence of an actual universal
rigidified geometric Picard-zero family; write `D = dualScheme A hA`.
Supply an ordinary line bundle `M` on `D ×_S A` and an actual evaluation
isomorphism `poincareFamily.carrier ⊗ M.obj ≅ O`. The module does not
construct this ordinary tensor inverse.

All declarations retain the hypotheses needed to construct the point
groups:

- `pullbackTensorComparisonIsIsoStatement`;
- `PicardZeroPullbackStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`.

These name preservation or coherence propositions about the existing
geometric predicate and fixed maps. The resulting group scheme is
conditional on these propositions and the supplied family data.

## Presheaf and represented group object

`dualPointGroupPresheafFromEvaluation` takes `T` to the constructed
commutative group on `T ⟶ D`. A morphism of parameters acts by
precomposition. The existing `dualPointPullbackMonoidHom` supplies the
homomorphism laws; a monoid homomorphism between groups is also a group
homomorphism. Identity and composition of the functor follow from
identity and associativity of composition in `Over S`.

`dualPointGroupRepresentableBy` represents the underlying set-valued
presheaf by `D`, using the identity equivalence on morphisms. Its
naturality equation is definitional.

`dualCommGroupSchemeFromEvaluation` applies
`CommGrpObj.ofRepresentableBy` to these data and bundles the result
as `Langlands.CommGroupScheme S`. Its underlying object is definitionally
`D`, recorded by `dualCommGroupSchemeFromEvaluation_X`.

## Comparison of operations

The cartesian monoidal structure of `Over S` uses a chosen pullback
product, which is not definitionally the categorical product used in
`dualTensor`. For their projections `fst` and `snd`,
`dualCommGroupSchemeFromEvaluation_mul` states that the reconstructed
multiplication is
`prod.lift fst snd ≫ dualTensor`.
This is definitional from the identity representation and the existing
point multiplication. `dualCommGroupSchemeFromEvaluation_prod_mul`
precomposes it with the canonical map from the categorical product and
recovers `dualTensor` exactly. The proof uses the two product universal
properties and their projection equations.

`dualCommGroupSchemeFromEvaluation_inv` identifies the inverse with
`dualInverseFromEvaluation`. Reconstruction evaluates the inverse of
the identity point, so the proof removes an identity composition.

`dualCommGroupSchemeFromEvaluation_one` identifies the unit with
`dualOrigin` after the structural map from the chosen monoidal unit
to `Over.mk (𝟙 S)`. This formulation keeps the terminal-object choice
explicit; the equality follows by unfolding the point unit.

## Points and Poincaré classification

`dualCommGroupSchemePointsIso` is a natural isomorphism from the actual
group scheme's group-valued point functor to the constructed presheaf
after forgetting commutativity. It uses Mathlib's
`yonedaGrpObjIsoOfRepresentableBy`. Every component is the identity
function on scheme morphisms, as `dualCommGroupSchemePointsIso_apply`
records.

`dualCommGroupSchemePointMulEquiv` composes this component equivalence
with `dualPointMulEquiv`. It identifies points of the actual group scheme
multiplicatively with the existing tensor monoid of geometric
Picard-zero classes. Its forward map is exactly `dualPointClass`,
the actual pullback of the Poincaré family, as the final apply lemma
states. This result is valid for every test scheme, including nonreduced
ones.

The module constructs a commutative group scheme, with no claim here
that it is smooth, proper or geometrically connected. It does not prove
existence of a dual, ordinary line-bundle inverses, a group structure on
all Picard-zero classes, or additivity of dualization as the input
homomorphism varies. Those remain separate constructions or geometric
obligations.
