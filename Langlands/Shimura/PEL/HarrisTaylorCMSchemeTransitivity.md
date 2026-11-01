# Residual translation in original represented CM fibers

This module proves the existence part of geometric-fiber transitivity for the
original represented Harris–Taylor CM tower. Given two actual morphisms from the
spectrum of the same algebraically closed field to a fine level, with equal
composites to a coarse level, it produces an element of the original residual
quotient whose existing action sends the first morphism to the second. It then
chooses such an element and proves its exact action equation. The construction
is conditional on the specified representing witnesses and the two named
relative-dual assertions; it does not assert their applicable existence.

## Data, hypotheses and original objects

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.
The inherited arithmetic input is a totally real number field `E`, a CM number
field `F` quadratic over `E`, a central simple unitary datum
`D : CentralSimpleUnitaryData E F A n`, and an imaginary quadratic CM field `L`
with an algebra map to `F` and a complex embedding `τ₀`. The actual
`HarrisSignatureCharts` input `C` uses the constructed Harris CM section. The
algebra and scalar-tower instances are explicit. The inherited class functors
use the existing normalized Harris–Taylor reflex structure and positive
auxiliary involution, with the same polarization and Weil-pairing conventions.
This module does not introduce a second arithmetic datum or reflex structure.

The explicit named infrastructure premises are tensor pullback preservation,
composition, unit coherence, associativity, the left-unitor comparison and
symmetry; Picard-zero pullback stability, the Mumford-bundle assertion and
universal base change; dual-abelian base-change naturality and polarization
base-change stability; finite Weil-transition compatibility; the actual
rational/profinite-integer/adele comparison; and torsion finite etaleness.
The concrete Lean binders give the precise propositions used.

The unpointed test category is `AdmissibleCMBaseCategory`. Its objects are the
existing connected, locally Noetherian admissible schemes over `Spec F`.
The disconnected test category is `ComponentwiseAdmissibleCMBaseCategory`,
with the existing locally Noetherian componentwise-admissibility condition.
The functor `disconnectedClassTower` is the existing product over actual
connected-component schemes of the unpointed class tower. The classes and
all transition maps are unchanged. In particular, the rational-isogeny class
construction retains a representative satisfying the determinant and numerical
dimension conditions jointly; it does not assert dimension invariance under
every ambient rational isogeny.

For the scheme results, `R` is a family of the existing
`CMLevelRepresentation` witnesses at every `SmallCMLevel D`. Such a witness
contains an actual admissible scheme over `Spec F`, smoothness and an actual
projective embedding, and an isomorphism from lifted Yoneda on the specified
full test category to the original small-level class presheaf. The scheme
results here use the representing isomorphisms, not the projective or smooth
fields. The tower is exactly `representedCMSchemeTower ... R`, recovered
through those isomorphisms by the existing Yoneda construction.

Let `V ≤ U` be the explicit inclusion of the fine and coarse small-level
subgroups. Normality is only of `V.subgroup.subgroupOf U.subgroup` inside `U`.
Write `X_V` and `X_U` for the corresponding original representing schemes.
The projection is exactly `representedCMNormalProjection ... R U V hVU`,
the existing tower map at `smallCMInclusion D hVU`. The residual group is
`SmallCMResidualGroup D U V`, namely `U / V` with the denominator expressed
as that subgroup of `U`. Its action is the original
`representedCMNormalQuotientAction`. A representative `g` acts through
`smallCMNormalInverseArrow` with element `g⁻¹`, preserving the existing
inverse-right convention for a left categorical action on the original
opposite Harris group.

## Transfer on geometric field tests

The private lemma `exists_translate_of_naturalIso` transfers the following
property through an actual natural isomorphism of functors: any two values
at the fine object with equal images under a specified arrow are related by
one of the specified endomorphisms. Naturality first sends the coarse equality
to the other functor. The given existence theorem supplies an endomorphism
there. Naturality at that same endomorphism and injectivity of the fine
component return the equality in the original functor. No new maps are chosen.

`unpointed_identityPoint_exists_normalTranslate` applies this lemma to
`unpointedClassTowerEvaluationIso` at the actual identity point of `Spec Ω`,
where `Ω` is an algebraically closed field. The explicit connected-admissibility
witness supplies the finite-etale roots-of-unity, torsion-invertibility and
pair-additivity inputs. `HarrisGeometricPoint.finiteFibers` supplies finite
fibers for the identity geometric point. The existing
`classMap_exists_normalTranslate` then gives an element of the original
`U.subgroup` whose same normal-inverse transporter sends the first class to
the second. That preceding theorem derives the element from actual frame
orbits and the actual rational-isogeny relation, keeping both original joint
representatives; geometric transitivity is not an input here.

`disconnected_identityPoint_exists_normalTranslate` transfers this conclusion
through `disconnectedClassTowerConnectedIso`. The nonempty connected field
spectrum has an actual connected component, and the isomorphism is the existing
one induced by that component inclusion. Both connected and componentwise
admissibility witnesses are explicit at this stage. The same inclusion and
normal-inverse transporter are used throughout.

`cmGeometricTestBase_exists_normalTranslate` supplies the connected witness
for the existing `cmGeometricTestBase ... existence geometry p`, retaining the
actual scheme `Spec Ω` and its specified map `p` to `Spec F`.
`RelativeDualSchemeExistenceStatement` supplies an actual universal dual for
every relevant abelian scheme, and `RelativeDualSchemeGeometryStatement`
supplies smoothness, properness and geometric connectedness of those duals.
The existing `admissibleCMBase_iff_dualGeometry` combines these with the
local Noetherianity and connectedness of `Spec Ω`. These are substantive
named hypotheses; neither assumes a CM translation or a geometric cover.

## Actual represented morphisms and the choice

`representedCMGeometricHom_exists_normalTranslate` starts with actual morphisms
`x,y : cmGeometricTestBase ... p ⟶ (R V).base` whose postcomposites by the
original coarse map agree. Evaluating the fine representing isomorphism at
`ULift.up x` and `ULift.up y` gives their original class values. The existing
`representedCMBaseTower_map_classes` equation transfers the coarse equality
to exactly the disconnected inclusion map. The field-test theorem above
produces `g : U.obj.subgroup`. The existing
`representedCMNormalQuotientBaseAction_mk_classes` equation identifies its
normal-inverse class map with postcomposition by the actual residual action
at `QuotientGroup.mk g`. Injectivity of the same representing equivalence,
followed by injectivity of `ULift.up`, proves the actual Hom equality.
Thus the conclusion is equality of morphisms, not just class values.

`representedCMGeometricPoint_exists_normalTranslate` starts with actual
scheme morphisms `a,b : Spec Ω ⟶ X_V` and an equality of their composites
with the original projection. Set `p = a ≫ (R V).base.obj.hom`. The existing
over-`Spec F` equation for the tower and the assumed coarse equality show
that `b` has the same structural map `p`. Bundle the two morphisms in the
same admissible over-category, apply the preceding Hom theorem, and forget
only the full-subcategory and over-category wrappers. The result is

`∃ g : SmallCMResidualGroup D U V, a ≫ action.ρ g = b`.

`representedCMGeometricTranslation` applies `Classical.choose` to this proved
existence theorem. Its value belongs to the original residual quotient.
`representedCMGeometricTranslation_action` is the corresponding
`Classical.choose_spec` equality for the exact original scheme action.
There is no uniqueness claim, naturality claim for the choice, or chosen
scheme section over `X_U`.

`cmGeometricPoint_exists_normalTranslate`, `cmGeometricTranslation` and
`cmGeometricTranslation_action` substitute precisely
`chosenCMLevelRepresentation ... q` for `R`, where `q` has the existing
`CMRepresentabilityStatement` type. This is the identical family used to
define `cmSchemeTower ... q`; the coarse map is its map at
`smallCMInclusion D hVU`, and the action is `cmNormalQuotientAction ... q`.
No independent representing family is selected in this specialization.

## Original source and derived provenance

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura` with
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 90 specifies sufficiently small levels and the connected-component
product. Page 91 defines polarized CM quadruples with invariant compatible
adelic-frame orbits and their rational-isogeny equivalence, gives right
frame-composition transitions, and states smooth projective representability,
finite-etale forgetting and the normal-level Galois-cover assertion.

The present proof is an internal deduction from the original class-fiber
translation theorem and the constructed natural evaluation, component and
representing isomorphisms. It implements only the existence part of
geometric-fiber transitivity, conditional on those precise witnesses and
named inputs. The transfer proof described above is the implemented route;
it is not attributed to the book as its proof of the full cover theorem.
The supplied five-page Harris publication/errata list was previously read
in full; no entry in that supplied list corrects the cited passage.

Applicable representability under the exact division/global hypotheses and
comparison with the complete source moduli problem remain open. This module
also leaves uniqueness modulo `V`, freeness of the residual action,
etaleness of the original projection, invertibility of the exact residual
kernel comparison, canonical-model comparisons, uniformization and
coefficient descent open. No `Etale` or comparison-`IsIso` premise is used
to obtain this translation-existence conclusion, and no conclusion about
these remaining properties follows merely from the noncanonical choice.
