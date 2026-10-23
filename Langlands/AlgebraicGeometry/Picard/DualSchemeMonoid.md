# Commutative monoids of dual-scheme points

Given an abelian scheme `A/S` with an actual universal geometric Picard-zero
family, this module equips the points of the chosen dual parameter scheme
with a commutative monoid. Its multiplication is the existing morphism
classifying tensor product and its unit is the existing distinguished origin.
Classification by the Poincare family is a multiplicative equivalence with
the geometric Picard-zero classes, natural under parameter pullback.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines tensor of rigidified classes and
classification by a universal rigidified family. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This is a derived construction from the existing restricted universal
property, actual tensor-classifying multiplication and origin. It reuses
the existing geometric Picard-zero subset and the proofs of associativity,
commutativity, unit laws and classification. It does not claim a new
representability theorem.

## Explicit inputs

The construction retains `HasDualScheme A`, asserting existence of an
actual universal family, and `PicardZeroPullbackStatement`, asserting
preservation of the existing geometric condition under parameter pullback.
It also takes six published fixed-map propositions:

- `pullbackTensorComparisonIsIsoStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`.

The unit-coherence input supplies the left-unitor part needed in the
point formula for multiplication. These hypotheses concern specified
Library maps. The monoid laws and the multiplicative equivalence are
proved from them; they are not additional inputs.

## Implemented operations and proofs

For any test scheme `T` over `S`, `dualPointCommMonoid` has carrier
`T ⟶ dualScheme A hA`. Its product of `f` and `g` is
`prod.lift f g ≫ dualTensor`, and its unit is the composite from `T` to
the base followed by `dualOrigin`.
Associativity and commutativity use the existing point laws.
For the two unit laws, injectivity of `dualPointClass` reduces the goals
to the Picard-zero tensor unit equations, using the classification
formulas for multiplication and the origin.

`dualPointMulEquiv` has forward map exactly `dualPointClass`, the actual
pullback classification by the Poincare family, and inverse exactly
`dualClassify`. Their inverse identities follow from the universal
property. Its multiplicativity is the existing `dualTensor_points` law.
The target monoid is precisely `picardZeroClassesCommMonoid`.

For `h : T ⟶ U`, `dualPointPullbackMonoidHom` is precomposition by `h`.
Its unit equation is the structural-morphism equation for `h` in `Over S`;
its multiplication equation follows from the binary-product universal
property and associativity of composition.
`dualPointMulEquiv_naturality` states that these monoid homomorphisms
commute with the multiplicative classification equivalences and actual
Picard-zero pullback. It is the existing `dualPointClass_comp` equation.

The structures are named definitions that can be installed locally.
No inverse operation, full group structure, or abelian-scheme structure
on the dual parameter scheme is asserted. Additivity in an input
homomorphism of abelian schemes is also outside this module.
