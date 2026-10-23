# Inversion on a chosen dual from a supplied Poincaré evaluation

This module constructs an inverse morphism of the chosen dual parameter
scheme by classifying an actual tensor inverse of its Poincaré family.
It proves the inverse equation as an equality of scheme morphisms and
on every test scheme. The existing commutative monoids of dual-valued
points then become commutative groups.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI,
paragraph (6.2), printed p.88 (PDF p.92), describes tensor multiplication,
parameter pullback, compatible isomorphisms and the universal property
of rigidified line bundles. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The module is a derived application of this universal-property
construction to the existing geometric Picard-zero classes. It reuses
`GeometricPicardZeroInverse` to prove membership of the supplied inverse
family. That result implements closure for the existing fibrewise
translation-invariance predicate; it does not invoke a new geometric
existence theorem. The source's additional hypotheses for identifying
the rigidified functor with the Picard sheaf are not used here.

## Data and hypotheses

Fix an abelian scheme `A/S`, a proof `hA : HasDualScheme A`, and write
`D = dualScheme A hA`. The latter hypothesis asserts the existence of an
actual universal rigidified Picard-zero family, from which the Library
chooses `D` and `poincareFamily A hA`.

The additional data are an ordinary line bundle `M` on `D ×_S A` and an
actual module-sheaf isomorphism
`poincareFamily.carrier ⊗ M.obj ≅ O`.
The construction does not assume an inverse scheme morphism or its
group laws. It does not construct the supplied ordinary bundle or
evaluation.

`dualInverseFromEvaluation` needs only these data and
`pullbackTensorComparisonIsIsoStatement`. Its classification and inverse
equations use `PicardZeroPullbackStatement`. The inverse equation also
retains `PullbackTensorCompositionStatement` and
`PullbackTensorUnitCoherenceStatement` (its left-unitor part is used).
The commutative-group construction additionally retains:

- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`.

These are the same fixed-map hypotheses used by the existing point
monoids. No new coherence or inverse-existence proposition is assumed.

## Construction and inverse equations

`dualInverseFromEvaluation` first uses `picardZeroInverseClass` to equip
`M` with the evaluation-induced rigidification and prove geometric
Picard-zero membership. It then applies `dualClassify` over the parameter
scheme `D`. Thus the result is an actual `S`-scheme morphism `D → D`.
`dualPointClass_inverseFromEvaluation` records its classifying equation.

`dualPointClass_id` identifies the class of the identity point of `D`
with the Poincaré family itself, using the proved identity law for
rigidified pullback.

`dualTensor_right_inverseFromEvaluation` proves
`m ∘ (id, inverse) = e ∘ structure`.
Injectivity of Poincaré classification reduces this scheme-morphism
equation to the tensor inverse equation for the supplied rigidified
family. The proof uses the established multiplication formula and the
fact that the origin classifies the trivial bundle.

For every `S`-scheme `T` and point `p : T → D`,
`dualTensor_points_right_inverseFromEvaluation` proves
`m ∘ (p, inverse ∘ p) = e ∘ structure`.
It precomposes the preceding morphism equation with `p`; the product
universal property identifies the two factors, and the defining equation
of a morphism over `S` identifies the resulting structural map.

## Groups of points

`dualPointCommGroupFromEvaluation T` extends the existing
`dualPointCommMonoid T`. Its multiplication and unit remain the actual
tensor-classifying multiplication and origin. Its inverse sends
`p` to `p ≫ dualInverseFromEvaluation`.
Commutativity changes the proved right-inverse equation into the
left-inverse equation required by Lean's group structure. All other
monoid laws are reused from the existing construction.

The result applies to every test scheme, including nonreduced ones.
It supplies a group structure from one actual supplied Poincaré
evaluation; it does not yet package a group scheme, establish the
geometric properties of a dual abelian scheme, or prove existence of
ordinary tensor inverses.
