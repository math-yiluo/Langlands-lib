# The commutative-monoid presheaf of geometric Picard-zero classes

For an abelian scheme `A/S`, this module packages the existing tensor on
`PicardZeroClasses A T` and the canonical trivial class into a commutative
monoid. Actual parameter pullback gives monoid homomorphisms, and the
inclusion into all rigidified classes is a natural monoid homomorphism.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines rigidified line-bundle classes, their
tensor product and their contravariant parameter pullback. Chapter VII,
Corollary (7.22), printed p.106 (PDF p.110), identifies `Pic⁰` over a field
with the kernel of the homomorphism associated to a line bundle.
The existing `GeometricPicardZero` and `RelativePicardZero` modules use
translation invariance after restriction to every geometric fibre.

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This contribution is a derived categorical packaging of the existing
geometric subset, tensor, trivial family, pullback and their proved laws.
It does not introduce a new definition of the geometric condition or prove
the source's identity-component characterization anew.

## Assumptions and scope

The monoid and inclusion take the same five published fixed-map proposition
inputs as `RigidifiedLineBundle.classesCommMonoid`:
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, and
`PullbackTensorSymmetryStatement`.

The parameter pullback and presheaf additionally take
`PullbackTensorCompositionStatement` and `PicardZeroPullbackStatement`.
The latter is the explicit geometric assertion that the existing
Picard-zero condition is preserved by parameter pullback. Identity and
composition use the proved `RigidifiedModule.pullbackCoherence`.
The construction does not require a dual representing scheme.
It gives a commutative monoid, without asserting inverse closure, a group
structure, or representability.

## Implemented construction

`picardZeroClassesCommMonoid` uses exactly
`picardZeroClassesTensor` and `trivialPicardZeroClass`.
The four structure laws are the existing Picard-zero associativity,
left/right unit, and commutativity lemmas. These are laws of the actual
restricted tensor operation, with its already proved geometric closure.

`picardZeroInclusionMonoidHom` is `Subtype.val`; preservation of the trivial
class and tensor holds definitionally.
`picardZeroClassesPullbackMonoidHom` has underlying function exactly
`picardZeroClassesPullback`. Its unit and tensor laws are
`picardZeroClassesPullback_trivial` and
`picardZeroClassesPullback_tensor`.

`picardZeroMonoidPresheaf` packages these objects and maps in
`CommMonCat`. Its identity and composition follow pointwise from the
existing `picardZeroPresheaf`. The comparison
`picardZeroMonoidPresheafForgetIso` has identity components, since its
underlying objects and map functions agree definitionally with that
set-valued presheaf.

`picardZeroMonoidInclusion` has components
`picardZeroInclusionMonoidHom`. Its naturality is definitional: the
restricted pullback forgets to the same pullback on rigidified classes.
Thus the geometric condition is retained throughout the construction,
while forgetting that condition preserves all supplied monoid operations.
