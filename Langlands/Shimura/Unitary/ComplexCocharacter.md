# Complex cocharacters of the constructed Harris group

Author: Worker 57.

This module constructs actual group-scheme morphisms from the complex
multiplicative group to the complex pullback of the rational Harris similitude
group. It first constructs the two factor cocharacters of the complex Deligne
group, then composes them with the complex pullback of the existing real map.
Point formulas hold on every complex test scheme.

## Internal provenance and hypotheses

This is an internal consequence of the published `DeligneSchemeSplitting` and
`HarrisDeligneGroupScheme` constructions. The former supplies the actual
complex Deligne group and its natural point equivalence with pairs of scalar
units. The latter supplies the corrected Harris and Kottwitz morphisms to the
real pullback of the given rational group. Group-valued Yoneda reconstruction,
the pullback point adjunction, and the original corepresented point comparison
provide the remaining steps. No new external existence theorem is asserted.
The inherited source conventions are documented in those imported modules.

The first construction uses the concrete fields `ℝ` and `ℂ`. Test schemes are
arbitrary objects over `Spec ℂ` in the small universe; there is no affineness or
reducedness assumption. The generic target construction takes a real group
scheme `G` and an actual morphism `h : DeligneTorus.groupScheme ⟶ G`.
The algebraic point specialization takes a real algebra `A`, an algebra
involution `σ`, a basis `b` indexed by a finite type, and a compatible complex
algebra homomorphism `h : ComplexHom σ`.

The Harris specialization has totally real and totally complex number fields
`E` and `K`, respectively, a quadratic extension `K/E`, and the central simple
unitary input `D : CentralSimpleUnitaryData E K A n`. The `E`, `K` and rational
algebra structures on `A` obey the three scalar towers `ℚ/E/A`, `ℚ/K/A` and
`E/K/A`. A chart input `C : HarrisSignatureCharts D.toSecondKindInvolution n Φ`
provides actual signature charts at the real places. These charts already
include the rank and distinguished-place conditions. The final constructor
instead accepts `HasHarrisSignature D.toSecondKindInvolution n` and
`IsCMSection E K Φ`, obtaining those charts by `ofSignature`. The rational
basis and group schemes are derived from `D`, not supplied as output data.

## The two factor cocharacters

`factorUnits first S` sends a scalar unit `u` to `(u, 1)` when `first = true`
and to `(1, u)` when `first = false`. It is a group homomorphism, and
`factorUnits_natural` proves compatibility with every ring homomorphism.

For each complex test scheme `T`, compose its `Gm`-point equivalence to the
units of `Γ(T.left, ⊤)` with `factorUnits`, and then with the inverse of
`complexSplitPointsEquiv T`. The private naturality lemma combines naturality
of the two published point equivalences with `factorUnits_natural`.
`factorCocharacter first` applies `GroupScheme.homOfPoints` to this family.
It is therefore an actual morphism of group schemes, including the group-law
compatibility, rather than only a prescription on complex-valued points.

`factorCocharacter_points` states the selected factor formula under
`complexSplitPointsEquiv`. `factorCocharacter_splitting` gives the same formula
after composing with the actual published isomorphism `complexSplitting`.
`factorCocharacter_quadratic` describes the corresponding unit in the
quadratic algebra by the inverse of `splitPointsEquiv`. The complex algebra
structure on global sections is the one induced by the test scheme's structure
map. `factorCocharacter_norm` proves that the quadratic norm of either selected
factor is the original scalar unit, by the product formula for the norm.

## Pullback of a real homomorphism

`complexMapOf h` is the image of `h` under pullback from `Spec ℝ` to `Spec ℂ`.
`cocharacterOf h first` is `factorCocharacter first` followed by this map.
`cocharacterOf_points` identifies its image under the pullback point adjunction
with the point of the real Deligne group followed by `h`. The proof uses the
published compatibility of that adjunction with group-scheme morphisms.
`cocharacterOf_comp` proves compatibility with a further morphism of real
target group schemes, by functoriality of pullback.

## Actual similitude points and multipliers

`complexTestAlgebra T` is the relative global-sections algebra of `T` regarded
as a real scheme via its structural map. `complexSimilitudePointsEquiv b σ T`
identifies points of the complex pullback of `σ.similitudeGroupScheme b` with
`(σ.baseChange (complexTestAlgebra T)).similitudes`. This combines the pullback
point adjunction with `Corepresented.pointsEquiv`.

In the namespace `AlgebraInvolution.ComplexHom`, `cocharacter_points` says that
this equivalence sends the point of `cocharacterOf (h.deligneGroupSchemeMap b)`
to `h.delignePoints` evaluated at the quadratic unit of the selected Deligne
factor. `inverseCocharacter_points` gives `h.delignePoints` evaluated at the
inverse of that quadratic unit for `h.inverseDeligneGroupSchemeMap b`.
Both proofs reduce the pullback composite, then apply
`Corepresented.groupSchemeMap_points`. Their scoped elaboration option allows
Lean to identify the bundled global-section presentations; it changes no
mathematical assumptions.

`cocharacter_multiplier` proves that the first map's multiplier is the scalar
unit represented by the original `Gm`-point. `inverseCocharacter_multiplier`
proves that the inverse-convention map's multiplier is its inverse. These use
the multiplier component of `delignePoints`, `factorCocharacter_norm`, and
preservation of inverses by the norm homomorphism.

## Harris and Kottwitz targets

`CentralSimpleUnitaryData.complexRationalGroupScheme` is the actual iterated
pullback of `D`'s rational group along `ℚ → ℝ → ℂ`. No identification with a
separately supplied complex group scheme is assumed.

`harrisCocharacter C first` applies `cocharacterOf` to `D.harrisDeligneMap C`.
`harrisCocharacter_comparison` proves that composing it with the complex
pullback of `D.realGroupSchemeIso.hom` recovers the cocharacter of
`D.realComplexHom C` in the actual real-algebra similitude model.

`kottwitzCocharacter C first` applies the same construction to
`D.kottwitzDeligneMap C`. Its comparison theorem recovers the inverse Deligne
map of `(D.realComplexHom C).conj`. Thus both conjugation and inversion are
retained, in the inherited order; Kottwitz's map is not identified with the
inverse of the unchanged Harris map. Both comparison proofs use
`cocharacterOf_comp` and the respective published real comparison.

`harrisCocharacterOfSignature hsig hΦ` constructs the first-factor Harris
cocharacter from signature and CM-section hypotheses. It uses `ofSignature`
and selects `first = true`.

## Remaining scope

The result constructs the actual cocharacters and their all-test-scheme point
and multiplier formulas. It does not yet split the complex target into its
matrix factors, calculate its representation weights, prove invariance under
changing charts, or identify the cocharacter conjugacy-class stabilizer with
the previously computed coordinate Hodge stabilizer. Smoothness, reductivity,
PEL representability, canonical models, scheme levels and coefficient descent
remain obligations of the host task.
