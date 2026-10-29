# Discrete-series opposite Jacquet quotient criterion

`Langlands.glTemperedDiscreteSeriesJacquetQuotient` proves the unchanged
Library proposition
`Langlands.GLTemperedDiscreteSeriesJacquetQuotientStatement.{uF,uV,uW}` in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md).
The field universe `uF`, ambient carrier universe `uV` and discrete-series
carrier universe `uW` remain independent.

For every actual positive-rank standard block Levi `M = B.Levi F.Carrier`,
let `J` be the specified opposite normalized Jacquet representation of an
irreducible analytically tempered representation `π` of `GL_n(F)`. Let `σ`
be irreducible and analytically square integrable modulo the full center of
`M`. For every Borel Haar measure `μ` on `M / Z(M)` quantified by the target,
the theorem proves

```text
(∃ S : Subrepresentation J,
   ∃ q : S.toRepresentation.IntertwiningMap σ, Surjective q)
  ↔ (∃ q : J.IntertwiningMap σ, Surjective q).
```

Both sides use actual subrepresentations and intertwiners. The proof constructs
the quotient witness from the occurrence witness.

## The implemented reduction

The private `occurrence_of_surjection` lemma restricts a supplied surjective
intertwiner to the whole subrepresentation `⊤`. This proves the reverse
implication and also exhibits every actual quotient of `J` as a subquotient.
The private `inclusion` is the underlying subtype inclusion intertwiner.

For the forward implication, choose the actual unitary central-character
datum `cσ` supplied by `IsSquareIntegrableModCenter σ μ`. Admissibility of
`π` follows from `T.IsTempered π`. The imported theorem
`Parabolic.irreducibleOppositeJacquetFiniteLength` in
[IrreducibleOppositeJacquetFiniteLengthProof](../Parabolic/IrreducibleOppositeJacquetFiniteLengthProof.md)
therefore makes `J.asModule` finite length over `MonoidAlgebra ℂ M`.

Apply the algebraic constructor `quotientOfScalarCentralQuotients` in
[ScalarQuotientReduction](../ScalarQuotientReduction.md), with the scalar
function `z ↦ (cσ.character z : ℂ)` on the full center. Its finite-length
induction reduces the problem to actual quotients `q : J → τ` on which that
center acts by precisely this scalar function. These intermediate carriers
stay in `Type uV`; `σ` stays in `Type uW`.

For clarity, this constructor does not split a generalized central component.
If a finite-length quotient `τ` does not already have the prescribed scalar
action, a nonzero central defect
`D = τ(z) - (cσ.character z : ℂ) • id` is an intertwiner. Occurrence of `σ`
forces `D` to be nonsurjective. Its image and its cokernel have smaller
composition length, and both are actual quotients of `τ`, hence of `J`.
The occurrence dichotomy places `σ` in one of them. Strong induction and
composition of surjections reduce to the scalar case. The imported
constructor implements this algebraic argument.

To discharge its scalar-case rule, the proof takes any such `τ`, surjection
`q`, scalar-action witness `hτ` and occurrence of `σ` in `τ`. It constructs
`cτ : UnitaryCentralCharacter τ` with the character, open kernel and unitary
norm law of `cσ`, and with scalar action `hτ`. Thus
`cτ.character = cσ.character` is definitional equality. The quotient map
makes `τ` a subquotient of `J`. The imported theorem
`glTemperedOppositeJacquetScalarLayer` in
[TemperedOppositeJacquetScalarLayerProof](TemperedOppositeJacquetScalarLayerProof.md)
gives `IsTemperedModCenter τ μ` for the same `μ`.

The imported theorem `glTemperedDiscreteSeriesIsotypic` in
[TemperedDiscreteSeriesIsotypicProof](TemperedDiscreteSeriesIsotypicProof.md)
now supplies an actual endomorphism `P` of `τ`, its idempotence, the identity

```text
P.range = ⨆ f : σ.IntertwiningMap τ, f.range,
```

and the absence of a surjection onto `σ` from every subrepresentation of
`P.ker`. The algebraic constructor `quotientOfIsotypicRange` in
[IsotypicQuotient](../IsotypicQuotient.md) combines the range and kernel
properties with the occurrence witness to give an actual surjection `τ → σ`.
It finds a nonzero `σ → τ` map in the intrinsic isotypic range, splits that
injection inside the semisimple range, and composes with the range projection.
Only this range is shown semisimple. The finite-length reduction returns a
surjective intertwiner from the whole `J` to `σ`.

## Actual action, normalization and universes

The local abbreviation in the proof is
`J = (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ`.
Its carrier is exactly
`Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)`.
The `change` in the proof checks that its action reduces definitionally to
the action in the target: `Jacquet.normalizedActionOfModulus` on that actual
opposite subgroup and the embedded Levi, using the inverse of the full upper
modulus transported to the embedded Levi, then pulled back along
`B.leviEquiv F.Carrier`. Thus its normalizing factor is the positive upper
half-modulus, `δ_opposite^(-1/2) = δ_upper^(1/2)`.

The finite-length input constructs its comparison with the reversed upper
Jacquet module using block-reversal conjugation on actual coinvariants and
the proved inverse full-modulus identity. The scalar-layer input uses the
same actual opposite action. All these identifications are proved or
checked by reduction; no carrier or opposite-action comparison is a premise
of the closing theorem.

The scalar-layer theorem is applied at `.{uF,uV,uV}`, since `π` and the
intermediate quotients have carriers in `uV`. The projector is applied at
`.{uF,uV,uW}`. This instantiation leaves the three target universes
independent. The theorem has no extra finite-length or projector parameter.

## Analytic convention bridge and measure scope

The Library's square-integrability and temperedness predicates include
admissibility and an actual smooth unitary scalar central character.
Their analytic conditions concern all smooth coefficient norms on the full
central quotient: respectively `L²(μ)` and `L^(2+ε)(μ)` for every `ε > 0`.
The target's analytic hypotheses are used in that form.

The scalar-layer theorem derives upper exponent bounds from the given
analytic temperedness of `π`. It transfers refined exponents of the actual
opposite subquotient back to `π`, uses exact unitary scalar central action
on each outer block, and applies analytic exponent sufficiency to `τ`.
That proof supplies admissibility of `τ` as well. It allows arbitrary
scalar-central subquotients, including the quotients used here.

The projector theorem derives coefficientwise `L^r` bounds for `σ`, with
`1 < r < 2`, from strict Jacquet exponent bounds, chamber decay and Cartan
cell integration. Temperedness of `τ` gives the conjugate exponent
`r/(r-1) > 2`; Hölder then makes its coefficient pairing absolutely
integrable. In that pairing the kernel is
`g ↦ ℓ(σ(g⁻¹) w) · η(τ(g) v)`. Replacing `g` by `g z` for a full-central
element multiplies the factors by `χ(z)⁻¹` and `χ(z)`, since the two exact
characters agree. Their product is one, so the complex kernel descends to
`M / Z(M)`. The proved Haar invariances on that quotient support inversion
and translation in the pairing. Its positive nondegenerate Hom pairing
produces the projector and rules out the kernel subquotients.

Every application uses the original arbitrary Borel Haar measure `μ` on the
full central quotient. The proof neither chooses a normalization nor changes
that measure. The imported analytic results prove the required conclusions
for each such `μ`.

## Provenance and dependency route

The mathematical target is the normalized GL-block specialization of
Silberger, *Introduction to Harmonic Analysis on Reductive p-adic Groups*
(1979), Theorem 4.5.18(1)–(2), printed p.193 / PDF p.199, registered as
`silberger-1979-harmonic-analysis`. Its component extraction refers to the
proof of Theorem 3.3.1, printed pp.126–127 / PDF pp.132–133; the auxiliary
fixed-character representations there must be tempered. The statement
Markdown records the class-exponent translation and the analytic convention
bridge. The present proof is a derived composition of the published
finite-length, scalar-layer and projector results with two internal
algebraic constructors.

The analytic predecessors use Waldspurger, *La formule de Plancherel pour les
groupes p-adiques d'après Harish-Chandra* (2003), registered as
`waldspurger-2003-plancherel`: I.1(5), p.241, I.4.1, p.245, II.1.1, p.251,
III.1.1 and the proof of III.1.2, pp.263–264, and III.2/III.2.2,
pp.265–266. These provide the Cartan volume, Jacquet asymptotic, spherical
and exponent ingredients of the derived analytic arguments. The imported
proof Markdown describes their implemented routes. The source passages
were read independently; no relevant errata note was found in the local
collection.

The finite-length branch uses the upper Jacquet finite-length proof and a
constructed block reversal. The scalar-layer branch uses analytic exponent
necessity, exponent inheritance and analytic sufficiency. The projector
branch uses strict exponent/chamber estimates, Cartan cell integration,
coefficient pairings, weak intertwiners and an algebraic finite Hom-space
projector. The algebraic quotient constructors use finite composition length
and semisimplicity of the intrinsic isotypic sum. The image/supremum lemmas
located in `CompactCoefficient.IsotypicSemisimplicityProof` have purely
algebraic hypotheses; the compact-coefficient analytic projector is not
used.

These dependencies contain no consuming opposite Jacquet quotient, summand,
regular Langlands head or exhaustion, or square-integrable Langlands
classification proof. Some statement modules occur as sources of proposition
definitions and other interfaces; their unproved assertions are not proof
inputs. The target pair and all of its imports are unchanged.
