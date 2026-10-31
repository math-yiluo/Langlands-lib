# The Harris numerical Weil tower with normalized CM coefficients

Author: Worker 57.

This is an internal specialization of `HarrisNumericalWeilTower` using
the normalized comparison proved in `HarrisTaylorCMLieDeterminant`. It makes the existing
actual fixed-base level tower use one CM structure map for the actual
Lie determinant, its prescribed coefficient sections, and the numerical
central trace test. The reflex coefficients use the explicitly conjugated scalar map whose
actual central coefficient agrees with the Harris–Taylor arithmetic
formula. No independent arithmetic base map is supplied.

Fix the displayed totally real number field `E`, totally complex CM
quadratic extension `F/E`, rational scalar towers and actual datum
`D : CentralSimpleUnitaryData E F A n`. Fix an imaginary quadratic CM
number field `L` with `[Algebra L F]`, a complex embedding `τ₀`, and
actual charts `C` for
`harrisCMSection E (algebraMap L F) τ₀`.
The CM section therefore uses exactly the `L → F` map used by the
numerical trace formula. The existing charts retain their signature
and rank assumptions; no independent CM section or embedding is added.
This specialization does not itself prove a compositum or supply charts.

Fix an arbitrary `S : Scheme.{0}` and `p : S → Spec F`. The reflex
structure is constructed as `b := D.harrisTaylorReflexStructure C p`,
and `hΦ` is the existing proof that the displayed Harris section is a
CM section. There is no independent reflex structure map among the
parameters. The construction also applies in the exceptional case in
which the cocharacter reflex field is rational: no reflex-to-CM
equivalence or nonexceptional-rank hypothesis is imposed.

The normalized scalar map is explicitly

```text
harrisTaylorReflexToCM C
  = cmConjugation E F ∘ harrisReflexToCM C,
b = p ≫ Spec.map (harrisTaylorReflexToCM C).
```

The original `harrisReflexToCM` and its unconjugated structure map
retain their existing meanings. Under the distinguished complex
embedding the new scalar map sends a reflex element with complex
value `t` to `conj(t)`. The imported actual-module calculation in
`HarrisHodgeTraceNormalization` proves that the intrinsic trace of
left multiplication by a central `a : F` on the regular Kottwitz
Hodge module is

```text
distinguishedEmbedding
  (cmConjugation E F (HarrisTaylor.lieTraceValue L F n a)).
```

The imported `HarrisDeterminantCentralTrace` extracts that trace from
the actual binary Hodge determinant and its descended reflex
polynomial. Applying the new scalar map to that reflex coefficient
therefore gives exactly `lieTraceValue L F n a`. This arithmetic
comparison is proved from the actual module and determinant; the
formal transfer of a predicate alone does not supply it.

The geometric parameters are exactly the explicit tensor-pullback,
unit, associativity, symmetry, Picard-zero, Mumford-bundle and universal
base-change statements used by the existing actual polarization
construction. The level parameters are the relative finite Weil
transition statement, actual rational profinite-integer/finite-adele
comparison, a point `s : Spec Ω → S` over an arbitrary field, finiteness
of the indicated finite-etale fibres, torsion finite-etaleness,
invertibility of every positive integer in the actual global-section
ring, finiteness and etaleness of the displayed roots-of-unity group
schemes, and quasi-separatedness of `S`. Ordered-pair additivity for
the actual polarized actions remains an explicit hypothesis.
No theorem represented by one of these parameters is proved here.

Every positive polarized action uses the canonical
`auxiliaryStarRing D C`, the constructed positive auxiliary left
involution. The regular source form and level transport retain the same
whole `harrisHodgePELUnit C` witness. In particular this specialization
does not choose a new positive unit or a new star operation.

`ObjectCondition X` is a conjunction on one actual positive polarized
action `X`. Its first conjunct is
`D.HarrisTaylorCMRationalLieDeterminantCondition C p` on the actual abelian
scheme and rational algebra action of `X`. This is equality of the
complete actual multivariate Lie determinant polynomial and the
reflex polynomial mapped into `F` and then into actual section rings
through `p`, over every finite family and actual finite Lie chart.
Its second conjunct is `HarrisTaylor.NumericalCondition L p E` on the
same scheme and action. The latter requires the actual geometric
relative dimension `[E:ℚ] n²` and the exact all-chart central Lie trace
identity of the existing numerical construction. Rational Lie scalars
and arithmetic coefficient sections use the same `p`; no reducedness
or flatness of section rings is required.

`objectCondition_iff` proves that this conjunction is precisely the
old positive determinant condition at the constructed `b`, together
with the existing numerical predicate. Its proof applies
`harrisTaylorCMRationalLieDeterminantCondition_iff` to the first conjunct
and reflexivity to the second. This transfers the complete polynomial equality at the particular
normalized base. Rational base independence is used only to identify
rational scalars on the fixed actual action; it does not identify
different arithmetic coefficient maps.

`objectCondition_centralCoefficient` applies the first conjunct to
the binary family `(1, c)`, for an actual Harris-order element `c`
with `(c : A) = algebraMap F A a`. For every actual finite Lie chart
and every smaller open it proves that the coefficient of `X` after
evaluation at `(1, X)` in the actual rational Lie determinant equals
`HarrisTaylor.lieTraceSection L p n a V.left`. The proof supplies the
order family to `hx.1` and invokes the proved normalized local
coefficient theorem. The order-membership equality is an explicit
hypothesis; this local theorem does not assert the result for an
arbitrary scalar lacking such a chosen order representative.

The arithmetic value is the embedded conjugate of
`trace L F (n²*a)`, plus `n*a`, minus `complexConj F (n*a)`.
It is the formula of Harris–Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3),
printed p.90 / PDF p.98, registered source
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's imaginary quadratic `E` is `L` here, and its CM `F` is
our `F`; our `E` is the totally real field. The internal provenance
of this module consists of the proved normalized determinant
comparison, this actual coefficient consequence, and specialization
of the existing representative-image and level constructions.

`IsoClass U` is the existing numerical representative image at
`b := D.harrisTaylorReflexStructure C p`, for the compact-open level `U` of
the opposite original Harris finite-adelic group. This is an abbreviation
of that constructed subtype, rather than a new equivalence relation.
`classOf x hx` uses the proved comparison to split one proof of the
new conjunction into the two old proofs on the same actual
representative `x`. The representative retains the actual abelian
scheme, rational algebra action, geometric polarization and
monodromy-fixed compatible Weil-level orbit.

`classOf_surjective` proves that every such class has an actual
representative satisfying the new conjunction. It takes the existing
jointly satisfying representative and recombines its proofs through
`objectCondition_iff`. The numerical image therefore requires one
representative satisfying both conditions simultaneously. It does
not silently transfer geometric dimension to arbitrary representatives.
The theorem starts with an existing class and does not assert that
the class type is inhabited.

`classOf_eq_iff` preserves the existing exact relation: a rational unit
`q`, an actual two-sided equivariant rational isomorphism between the
action objects, the actual rational dual-pullback polarization
multiplier equation `Multiple`, and equality of the transported
compatible level orbits. The proof specializes the existing equality
criterion with the two pairs of proofs obtained from the new
conjunction. Neither an extra sign condition on the multiplier nor a
geometric-dimension invariance theorem is inserted.

`mapRepresentative` is the existing actual original-group transporter
map. It preserves the positive polarized object and changes its level
orbit. Consequently `objectCondition_mapRepresentative` is a
definitional equivalence on exactly the same object. `isoClassTower`
is the already constructed numerical functor at these parameters.
`classMap` is its actual map. Its representative formula is
definitional, while `classMap_id` and `classMap_comp` evaluate the
proved functor laws. Thus all identity and composition requirements
are provided by the existing construction.

`inclusionNatTrans` specializes the existing natural inclusion into
the polarized determinant tower at the constructed reflex base, and
`inclusion_injective` is subtype injectivity at each original level.
`forgetNumericalAction` and its representative formula retain the
actual numerical rational-action class after forgetting polarization
and levels. Its transition law and `forgetNumericalActionNatTrans`
reuse the proved constant-action natural transformation. These are
naturality statements along actual level arrows on the fixed base
scheme.

`forgetLevel` uses the actual original subgroup-inclusion arrow and
has the stated representative formula. `heckeLeft` and `heckeRight`
use the two actual arrows from the compact-open intersection
`U ∩ g V g⁻¹`: respectively the inclusion leg to `U` and the leg
with original-group element `g` to `V`, under the existing opposite
group convention. The two representative formulas follow by
definition. The needed finite rational module instance is derived
from `hodgeRationalPELConditions D C`, rather than added as new data.

`normalizedReflexSection_rank_three` additionally treats the
imaginary-quadratic case `L = F`. For actual charts `C₃` for the
self-field Harris section, `n = 3`, and
`complexConj F a = -a`, the actual reflex determinant for the family
`(1, algebraMap F A a)`, mapped into the section ring through
`D.harrisTaylorReflexStructure C₃ p`, has extracted coefficient
`(secHom p U).hom (-3*a)`. This holds on every open of every displayed
base scheme, without a nonempty-open or reducedness assumption.
The proof first applies the actual normalized-reflex-section formula,
then the actual central determinant's rank-three specialization.
The identity-extension trace makes the arithmetic expression
`conj(9*a) + 3*a - conj(3*a) = -3*a`. Thus at the allowed complex
specialization with `a` corresponding to `i`, the prescribed
coefficient is `-3i`, with the same sign as the numerical condition.
This theorem is conditional on the displayed datum, charts and
anti-invariance equation and asserts no compatible object's existence.

This unit constructs the specialized tower of actual fixed-base
classes. The geometric point and finite-etale hypotheses remain
displayed, and the predicates remain conditions on actual objects.
It proves neither equivalence with the full Lie-plus compatibility
condition nor geometric-dimension invariance on all representatives.
It does not prove actual Lie-sheaf base-change naturality, define a
functor on varying scheme bases, provide representability, or
construct scheme levels. Those requirements of the broader task
remain in force.
