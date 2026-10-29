# Exponent comparison for linked segment heads

Authors: Workers 485, 167 and 252. Worker 167 authored the support-containment
map, determinant-power norm calculation, and the twisted representative and
segment scalar calculation adapted here. Worker 252 authored the direct
positive-form scalar cancellation. Worker 485 adapted the segment calculation
to arbitrary exponent witnesses and proved the logarithmic comparison, strict
precedence inequality and two-clause assembly.

The closing theorem
`Langlands.Classification.linkedSegmentHeadExponentComparison.{uF,uV}` proves
exactly `Langlands.Classification.LinkedSegmentHeadExponentComparison.{uF,uV} F T`.
Its outer parameters are any prime `p` with `Fact p.Prime`, an explicit
`F : PadicField.{uF} p`, and an explicit `T : F.TopologicalData`. The universes
`uF` and `uV` are independent. The internal segment and representation carriers
are the saturated universe `max uF uV` specified by the statement.

For every pair of actual strong segment heads and every pair of supplied
`UnitaryExponentData` witnesses, the theorem proves both conclusions:

1. Linkage together with failure of forward precedence gives
   `v.exponent ≤ u.exponent`.
2. Forward precedence gives `u.exponent < v.exponent`.

The second clause uses the linkage already contained in `Precedes`.

## Scalar cancellation in the supplied form

The imported theorem `Langlands.unitaryExponentScalarNorm` proves the published
proposition `Langlands.UnitaryExponentScalarNorm`. Its proof is in
[UnitaryExponentScalarNormProof](UnitaryExponentScalarNormProof.md).
The argument works for any group and any nontrivial complex vector space,
without topology, dimension or a norm on that space. That imported proof runs
as follows.

Given scalar action `ρ g w = c • w` and an arbitrary exponent witness `u`,
choose a nonzero vector `w`. Put `x = ν(g) > 0` and
`k = x^(-u.exponent) c`. The negative real-power twist sends `w` to `k • w`.
Its invariance under the actual form `u.form` and sesquilinearity give

    conj(k) k inner(w,w) = inner(w,w).

Definiteness makes the diagonal term nonzero, so it cancels. Taking norms
gives `norm(k) = 1`. Positivity of the real-power factor and `Real.rpow_neg`
then give `norm(c) = x^u.exponent`. This proof uses the supplied arbitrary
form and introduces no hypothesis asserting a norm formula or another form.

## Scalar identity for each actual head

Choose an actual supercuspidal representative `A` of a segment's base class.
Its defining property supplies admissibility and irreducibility, so
`admissibleSchur_centralCharacter` gives a character on the actual center.
Compose it with `GeneralLinear.scalarToCenter` to obtain a scalar character
`ω` of the field units.

For a length-`m` segment based at the natural-number twist `a` of a common
rank-`r` datum, construct the corresponding actual twist of `A`. Its scalar
character is `ω` times the scalar restriction of the determinant-power
character. The published theorem
`Langlands.Classification.segmentConstituentCentralCharacter` computes the
scalar action on its increasing normalized induction and transfers it to the
quotient supplied by the strong-head hypothesis. Irreducibility of that head
supplies a nontrivial carrier. Apply `Langlands.unitaryExponentScalarNorm`
to its arbitrary witness `u`.

The shared `T.norm_determinantPowerCharacter_scalar` calculation in
[SupercuspidalTwist](SupercuspidalTwist.md) retains the rank and yields,
for every field unit `z`, with `t = |z|`,

    norm(ω(z))^m t^(r m (a + (m-1)/2)) = t^(r m u.exponent).

The induction and quotient here are precisely the published increasing-product
special quotient, with upper block parabolic, positive half-modulus covariance
and right translation. No positive form or unitary exponent is chosen for the
base cuspidal representation.

## Endpoints and the two comparisons

If `Δ.Precedes Γ`, its definition supplies a natural `k > 0` and
`Γ.base = Δ.base.twist k`. If `k + Γ.length ≤ Δ.length`, every member `i` of
`Γ` is member `k+i` of `Δ`. Thus `Γ.support ⊆ Δ.support`, contradicting the
noncontainment clause of linkage. Hence

    Δ.length < k + Γ.length.

This uses Worker 167's published
`Segment.support_subset_of_base_shift`, extracted unchanged into
[SegmentSupportContainment](SegmentSupportContainment.md). The support argument
needs no injectivity or nonperiodicity of the twist orbit and no separately
chosen interval coordinates.

Evaluate the two scalar identities at a uniformizer, using the same actual
base representative and scalar character, with shifts `0` and `k`. Its
normalized absolute value satisfies `0 < t < 1`. Taking logarithms cancels
the common scalar character, the positive lengths, the positive rank and the
nonzero `log(t)`. The resulting identity is

    v.exponent - u.exponent = k + (Γ.length - Δ.length)/2.

The endpoint bound and `k > 0` make this strictly positive. This proves the
precedence clause. For linked segments without forward precedence, the
published `IsLinked.precedes_or_precedes` gives reverse precedence. Applying
the strict result in reverse order implies the required weak inequality.

## Reused results, provenance and independence

The proof imports the exact linked-head statement,
`UnitaryExponentScalarNormProof`, `SegmentConstituentCentralCharacterProof`,
`SegmentLinkageOrientationProof`, `SegmentSupportContainment`,
`Smooth.Schur.Proof`, and `LocalField.Uniformizer`. The scalar-norm
statement `Langlands.UnitaryExponentScalarNorm` enters only through the import
of its proof module. Worker 264 authored the published segment scalar-action
proof. Workers 346 and 328 authored and prepared the published linkage
orientation proof.

This module contains no private scalar-norm proof. It calls the accepted
public theorem `Langlands.unitaryExponentScalarNorm` from
`UnitaryExponentScalarNormProof`. Worker 438 implemented that theorem from the
derivation by Worker 252 described above, and it is published in the Library.
No pending scalar-norm proof is an input.

This is an internal derivation from the existing segment relations, actual
representations and invariant positive forms. Convention passages read are
Rodier 1982, registered ID `rodier-1982-gln`, printed pp.210–212 (PDF pp.11–13),
and Henniart 2002, registered ID `henniart-2002-characterization`, §§2.5–2.8,
printed pp.594–596 (PDF pp.8–10). They motivate the segment, precedence and
increasing special quotient conventions; their classification conclusions are
not used. The published source-boundary note was consulted. The disputed
contragredient formula and the Jacquet exhaustion citation do not enter the
argument.

The complete project import closure of this module, 76 project modules counting
the module itself and including the scalar-norm proof and statement modules,
was checked against the task's excluded ordered conversion, square-integrable
and regular exhaustion, classification, tempered-block uniqueness, multisegment
exhaustion, ordered-head existence and quotient-coverage consumers. None occurs. The proof adds no analytic
square-integrability, admissibility, common-base, equal-rank, selected character
or classification premise. It proves no existence of exponent witnesses.
