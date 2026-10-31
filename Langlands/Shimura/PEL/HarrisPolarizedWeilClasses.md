# Harris determinant classes with actual polarizations and Weil levels

This derived construction restricts the actual polarized Weil-level isogeny
quotient to the constructed regular Harris source module and its actual
Lie/reflex determinant condition. It constructs the restricted transporter
functor, level-forgetting maps and both Hecke legs. The canonical specialization
uses the constructed positive auxiliary left involution and its matching
normalized alternating trace form. The namespace is
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines isogenies as invertible rational
homomorphisms and polarizations by geometric fibres. Section III.1,
printed pp.90–91 / PDF pp.98–99, specifies Lie compatibility and the pointed
PEL quadruples with prescribed dimension, faithful rational action, geometric
polarization, involution compatibility and a monodromy-invariant compatible
level orbit. Equivalence uses actual rational isogenies and a rational-unit
polarization multiple. Page 91 gives the right action on frames and the
representability conclusion under its additional hypotheses.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
section 5, printed pp.389–391 / PDF pp.17–19, specifies a positive left
involution, its adjoint alternating form, Hodge homomorphism and positivity.
It constructs the reflex polynomial and requires equality with the polynomial
of the actual relative Lie action. It then gives the polarization, isogeny
equivalence and invariant-orbit level conditions for its integral prime-to-p
moduli problem. The registered source is
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

The present unit combines the existing `HarrisHodgeInput`,
`RationalLieDeterminantClasses` and `PolarizedWeilLevelClasses`
constructions. Its provenance is the pullback of the already well-defined
determinant predicate along the actual forget-action map, followed by
restriction of the existing quotient maps. It is a rational fixed-base
construction, and is not identified with Kottwitz's integral moduli functor
or Harris–Taylor's complete compatibility condition.

## Arithmetic source and involution

Fix a totally real number field `E`, a totally complex quadratic number
field extension `F/E`, and `D : CentralSimpleUnitaryData E F A n`.
The compatible rational, `E` and `F` scalar towers on `A` are explicit.
Fix the existing Harris signature charts `C` and a CM-section proof `hΦ`.
The source module is the actual regular left `A`-module `A`, and its form
is `D.harrisHodgePELForm C`.

`auxiliaryStarRing D C` makes the involution of
`D.harrisHodgePELAlgebra C` the actual `StarRing A` operation.
Its involution, multiplication and addition laws are the corresponding
algebra-involution laws. `auxiliary_star` computes its value.
The published `harrisHodgePELAlgebra_isPositive` proves positivity of this
auxiliary involution after real base change. The same whole
`harrisHodgePELUnit` witness is used in the form and the auxiliary algebra.
The published form is alternating and nondegenerate, and
`auxiliary_form_adjoint` identifies its left adjoint with this star.
The original Harris involution remains the right adjoint, as proved in
`HarrisHodgeInput`; it is not installed as the left star here.

The first section retains a general `[StarRing A]` parameter so the restriction
API can be reused with any chosen star. That section does not identify an
arbitrary star with the source involution. The `Positive...` definitions
explicitly specialize every object, class and map using
`letI := auxiliaryStarRing D C`; they have no independently supplied star
parameter.

## Actual geometric inputs

Fix `S : Scheme.{0}` and the actual map
`b : S → Spec (D.kottwitzCocharacterReflexField C)`.
All arithmetic types are universe zero, and the class types and the functor
codomain are `Type 1`.

The following existing geometric theorem inputs remain explicit: tensor
pullback comparison isomorphisms, composition, unit, associativity,
left-unitor comparison and symmetry; Picard-zero pullback stability,
Mumford-bundle Picard-zero and universal base change; finite Weil transition;
the rational profinite-integer/finite-adele scalar comparison; and torsion
finite étaleness. Fix `s : Spec Ω → S` with `[Field Ω]` and finiteness of
the fibres of every finite étale cover at `s`. No algebraic-closedness
instance is required by this API. Also retain invertibility on `S` of every
positive full-tower order, finite étaleness of its root-of-unity group scheme,
and quasi-separatedness of `S`.

`PolarizedAction`, reused from `PolarizedWeilLevelClasses`, retains an
actual abelian scheme, an injective unital rational algebra action, the
existing universal Picard-zero dual witnesses and geometry, an inverse
Poincaré bundle with evaluation, and an actual homomorphism to the constructed
dual. Its `IsPolarization` proof includes an actual isogeny and ample Mumford
presentations on all algebraically closed geometric fibres after possible
field extension. The actual rational involution compatibility equation is
retained. `PairAdditivity` remains an explicit proposition for the constructed
dual map on every ordered pair of these objects.

At `K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)`,
`LevelData K` retains such an object and a `K`-orbit of actual tensor-linear,
Weil-compatible frames, fixed by the automorphism group of the actual
finite-étale fibre functor at `s`. Compatibility uses an existential
trivialization of the actual Tate twist. Fixedness of the orbit does not
require fixedness of a representative.

## Restriction and exact equality

`ObjectCondition X` is the existing
`D.HarrisRationalLieDeterminantCondition C hΦ b` on the actual abelian scheme
and rational action of `X`. It quantifies over every finite family in the
constructed Harris order, every finite free local Lie chart and every smaller
open. Equality is equality of the actual section polynomials, with reflex
coefficients mapped through the structure morphism `b`.

`ClassCondition q` applies the already descended action-class determinant
predicate to the actual `forgetAction q`. `classCondition_classOf` is the
definitional equivalence with `ObjectCondition`. The
`classCondition_iff_of_classOf_eq` theorem gives the same equivalence for
every specified representative, and `classCondition_iff_exists` uses the
surjectivity of the ambient quotient map to characterize satisfying classes.

`IsoClass K` is the subtype of ambient polarized Weil-level classes satisfying
`ClassCondition`. `classOf x hx` constructs a class from an actual
representative and its determinant proof. `classOf_eq_iff` retains precisely
the original relation: there exist a rational unit `q`, an actual equivariant
rational isomorphism `e`, the actual equation
`eᵛ ∘ λ_Y ∘ e = (q : ℚ) • λ_X`, and equality of the transported compatible
level orbit with the target orbit. The rational inverse is part of `e`.
Subtype extensionality and the ambient exact quotient criterion prove this
equivalence. No sign assertion is added to the rational-unit multiplier.
`classOf_surjective` gives a determinant-compatible actual representative for
each existing restricted class; it asserts no nonemptiness.

`forgetDeterminantAction` forgets polarization and level data into the
constructed actual determinant action class. Its representative formula is
definitional.

## Level maps and canonical-positive API

`classCondition_classMap` proves that the determinant predicate is unchanged
under every actual transporter map, since the ambient map preserves the
forgotten action class. `classMap` therefore restricts that ambient map.
Its underlying-class and representative formulas are definitional.
Subtype extensionality and the ambient laws prove identity and composition.
These maps form `isoClassTower`. Its indices are the actual compact-open
transporter category of the scalar-extension similitude group of the
regular module and trace form. An arrow with element `g` has condition
`g⁻¹ K g ≤ L`, and its actual frame map is `η ↦ η ∘ g`.
`inclusionNatTrans` is natural subtype inclusion into the ambient polarized
tower. `forgetDeterminantActionNatTrans` packages the proved invariance of
the determinant action class along every level arrow.

`forgetLevel` is the restricted map of an inclusion. Its representative formula
is the existing actual Weil-level forgetting map, retaining the object and
its determinant proof. In the general-star Hecke section, the additional
`Module.Finite ℚ A` instance supplies the topological-group instance needed
for `H = K ∩ g L g⁻¹`. `heckeLeft` and `heckeRight` are the restricted maps
on the existing arrows from `H` to `K` and `L`. Their class formulas and
the two `_representative` theorems identify both maps with the actual
Weil-compatible forgetting and right-translation maps.

`PositivePolarizedAction`, `PositiveObjectCondition`, `PositivePairAdditivity`
and `PositiveLevelData` specialize these actual inputs to the constructed
positive auxiliary star. `PositiveIsoClass`, `positiveClassOf`,
`positiveClassOf_eq_iff` and `positiveClassOf_surjective` specialize the
restricted classes and exact relation. `positiveIsoClassTower` is the actual
specialized functor. Its object and representative map formulas are
definitional. `positiveInclusionNatTrans` and
`positiveForgetDeterminantActionNatTrans` are its natural forgetful maps.
`positiveForgetLevel` and `positiveHeckeLeft/Right` are its inclusion and
Hecke maps, with actual representative formulas.
For both positive Hecke legs, the private `rationalFinite` proof derives
finite dimension from the actual totally real basis of `D` and transitivity
of finite dimension over `ℚ ⊆ E`. No extra finiteness hypothesis is supplied
to these canonical-positive wrappers.

## Remaining source obligations

This construction fixes the base, structure morphism and field-valued point.
It does not impose a prescribed relative dimension or identify the determinant
condition with all of Harris–Taylor's compatibility requirements.
Reindexing by the opposite original Harris similitude group requires the
separate published regular-source index bridge.
Canonical point independence, base-scheme pullback of these restricted
polarized classes, connected and locally noetherian source restrictions,
extension across disconnected schemes, level smallness, the full Harris PEL
functor, its precise representability theorem, actual scheme levels and
coefficient descent remain construction obligations. This focused
prerequisite asserts none of these conclusions.
