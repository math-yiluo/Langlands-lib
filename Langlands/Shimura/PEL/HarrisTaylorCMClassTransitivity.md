# Actual normal translation between CM classes with equal coarse image

This module constructs an element of the original coarse Harris subgroup
translating any specified pair of fine CM classes with equal coarse images.
It proves existence using the actual polarized rational-isogeny quotient
and retains the same determinant and numerical witnesses throughout.
The result is at a fixed base scheme and point, without a representability
or geometric-cover hypothesis.

## Original classes and parameters

The fields, central simple unitary datum `D` and signature charts `C` are
those of `HarrisTaylorCMPolarizedClasses`. Lean `L` is the displayed imaginary
quadratic CM field, `E` is totally real and `F` is CM quadratic over `E`.
The charts are on `harrisCMSection E (algebraMap L F) τ₀`. For the specified
map `p : S → Spec F`, the determinant uses the constructed normalized reflex
map `D.harrisTaylorReflexStructure C p`, with its existing conjugated sign.

The base `S` is quasi-separated, and `s : Spec Ω → S` is an actual point
for a field `Ω`, with finite fibers on the finite étale covers in the
existing API. Invertibility of every positive full-tower torsion order and
finite étaleness of the corresponding roots of unity remain explicit.
There is no connectedness, local Noetherianity or algebraic-closedness
hypothesis in this fixed-base result. Those hypotheses are needed in other
modules to extend classes to the varying-base moduli presheaf.

The inherited named inputs are pullback-tensor comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, Mumford-square and universal base change;
relative finite Weil transition; rational profinite-integer/finite-adele
comparison; torsion finite étaleness; and `PositivePairAdditivity` for this
base. The actual positive auxiliary involution, polarization, dual and
Poincaré geometry, and pairing-compatible adelic frames are unchanged.

`Classes V` in the implementation is the existing normalized specialization
of `HarrisNumericalWeilLevel.IsoClass` at the original index `V : HarrisLevel D`.
Its ambient equivalence is the actual equivariant rational-isogeny relation,
including an actual rational inverse and the rational-unit polarization
multiplier. The numerical subtype requires one representative satisfying
both the determinant condition and the numerical condition. The latter
includes geometric relative dimension and the central Lie trace formula.
The module never assumes that every representative in an ambient rational
isogeny class has that dimension.

Let `V ≤ U` be original Harris compact-open levels. The separate hypothesis
`hVU` supplies this inclusion, and
`(V.subgroup.subgroupOf U.subgroup).Normal` supplies normality inside `U`.
The original finite-adelic Harris group is the existing opposite group.
No smallness hypothesis or freeness conclusion is needed for existence of
a translation between two classes that already have fine-level lifts.

## Orbit calculation and original subgroup element

The accompanying internal module `OrbitFibers` proves that, for a commuting
left monodromy action and right group action, equal coarse orbits of two
fine orbits yield an actual element of the coarse subgroup translating one
to the other, provided the given conjugation condition makes fine
translation well-defined. It also proves the corresponding statement for
monodromy-invariant orbits by subtype equality.

The private `representativeOrbit_exists_normalTranslate` specializes the
right-orbit calculation to actual Weil-compatible frames on one positive
polarized object. The level functor `hodgeLevelFunctor D C` is induced by
the existing continuous group equivalence
`harrisFiniteAdelicScalarExtensionContinuousEquiv`. Membership in its
image subgroup is membership of the inverse image in the original
subgroup. Relative normality, via the existing normal transporter,
therefore gives the required conjugation condition for the image levels.

Equal coarse invariant orbits have equal underlying coarse right orbits.
The orbit theorem supplies an element `a` of the image coarse subgroup.
Its inverse image under that actual scalar-extension equivalence belongs
to the original `U.subgroup`. The witness returned here is the inverse
of that original element: the existing `normalInverseArrow g` has
transporter element `g⁻¹`, so it acts by the required right translation
by `a` after applying `hodgeLevelFunctor`. This is exactly the convention
used for the existing left normal-level action. No element is supplied
independently of the original group.

## Passing through the rational-isogeny quotient

`classMap_exists_normalTranslate` says that if the original inclusion map
sends `x, y : Classes V` to the same class at `U`, then there is
`g : U.subgroup` such that the original class map at
`CompactOpenLevel.normalInverseArrow U V hVU g` sends `x` to `y`.

The proof extracts actual representatives `(X, a)` and `(Y, b)` from the
two existing numerical image classes, together with each representative's
own determinant and numerical proofs. The original coarse class equality,
through `HarrisNumericalWeilLevel.classOf_eq_iff`, supplies a rational unit
`q`, an actual equivariant rational isomorphism `e`, its polarization
compatibility equation `he`, and the coarse transported-orbit equality.

The proof transports the fine orbit `a` from `X` to `Y` with the existing
`PolarizedWeilLevel.levelIso`. Naturality of this transport under the
inclusion shows that the transported fine orbit and `b` have equal coarse
images on `Y`. The representative orbit calculation gives an original
element `g` relating them. Naturality under the same original normal
transporter then supplies the orbit equation for the rational-isogeny
criterion at fine level. Applying that criterion with the same `q`, `e`
and `he` proves the desired class equality.

Both original determinant proofs and both original numerical proofs are
reused. The transporter changes only the level orbit of `X`, so its
determinant and numerical conditions stay on `X`; the target witnesses
stay on `Y`. No dimension-invariance assertion under arbitrary rational
isogenies is used.

`normalClassTranslation` chooses an element of the original `U.subgroup`
from this proved existence theorem by `Classical.choose`.
`classMap_normalClassTranslation` is its `choose_spec` equation for the
unchanged original inverse-right class map. There is no assumed
translation witness, uniqueness assertion or naturality assertion for
this choice.

## Source provenance and remaining geometry

The source is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF
pp.98–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage defines the product over connected components, polarized
equivalence classes with invariant pairing-compatible adelic frame orbits,
and the right action by frame composition. It states finite étale
forgetting and the normal `U/V` Galois-cover assertion. The proof here is
an internal deduction from the existing formalized classes and orbit
relation, providing the existence part of transitivity relevant to that
assertion. It is not the source's full Galois-cover theorem.

All five pages of the supplied author document
`Harris--Publication with errata--undated/Harris--Publication with errata.pdf`
were checked; no entry corrects this cited passage. This observation is
limited to the supplied list.

The module proves neither uniqueness modulo `V` nor rational-automorphism
rigidity. It does not prove nonemptiness of any class set, applicability
of representability, equivalence with the full source moduli problem,
étaleness of the original scheme projection, invertibility of the exact
residual kernel comparison, canonical-model comparison, uniformization
or coefficient descent. It constructs no global scheme section. Those
obligations remain separate from the fixed-base existence theorem.
