# Analytic tempered induction from the actual GL block Levi

Author: Worker 200.

`Langlands.glTemperedInduction` proves exactly
`Langlands.GLTemperedInductionStatement.{uF,uV}` from
`Langlands.Representation.Classification.TemperedInductionStatement`.
The theorem has independent field and carrier universes and no additional
parameters or hypotheses.

For every prime `p`, `F : PadicField.{uF} p`, supplied topological data `T`,
positive total rank `n`, and block shape `B`, let `M = B.Levi F.Carrier`.
Given any Borel measurable realization of `M / Z(M)`, one supplied Haar
measure `μ`, and an irreducible representation `σ` on an arbitrary complex
carrier `V : Type uV`, the hypothesis `IsTemperedModCenter σ μ` implies all
three conclusions:

- `IsUnitarizable σ`;
- `Representation.IsSemisimpleRepresentation
  (T.normalizedParabolicInduced B σ)`;
- `T.IsTempered (T.normalizedParabolicInduced B σ)`.

The middle conclusion means that every invariant subspace has an invariant
complement. The induction may be reducible. Its construction is the actual
upper parabolic function representation with positive half-modulus
covariance and right translation. All block shapes, including the one-block
case, and the original action and carrier are retained.

## Implemented proof

The proof installs the supplied field topology and the actual ambient
general linear topological group, then introduces the unchanged target.
Write `htemp` for its analytic hypothesis at the original `μ`.

First, `glLeviTemperedUnitarity.{uF,uV}` from
[LeviTemperedUnitarityProof](LeviTemperedUnitarityProof.md), by Workers 551
and 560, applies to exactly `hσ` and `htemp`. It gives an actual invariant
positive definite Hermitian form on the supplied carrier through
`IsUnitarizable σ`. That published proof derives the needed factorization
and analytic comparisons internally. No tensor presentation is a
hypothesis of the present theorem.

Second, `htemp.isAdmissible.1` supplies smoothness.
`glNormalizedParabolicInductionUnitarity.{uF,uV}` from
[../Induction/UnitaryProof](../Induction/UnitaryProof.md), by Worker 117,
uses this smoothness and the input form to prove unitarizability of the
actual induced action. Its published construction integrates the scalar
pairing over a compact picture and proves positivity and invariance under
the full ambient group. It imposes no topology or completeness assumption
on `V`.

Independently, `Parabolic.normalizedInductionAdmissibility` from
[../Parabolic/NormalizedAdmissibilityProof](../Parabolic/NormalizedAdmissibilityProof.md)
applies to `htemp.isAdmissible`. This establishes admissibility of the
induced representation before its temperedness conclusion is used.
The proof of this input uses Levi inflation, the smooth positive-half
modulus twist, compactness of the parabolic quotient and admissibility of
smooth induction.

Now `admissibleUnitarySemisimplicity` from
[../Unitary/AdmissibleSemisimplicityProof](../Unitary/AdmissibleSemisimplicityProof.md)
applies to induced admissibility and the induced positive form, using
`GeneralLinear.compactOpen_cofinal F T n`. It supplies the middle
conjunct. The general theorem obtains an invariant orthogonal complement
for every subrepresentation; admissibility and the smooth-dual
identification prove that this complement spans with the subrepresentation.
Its group universe is `uF`, while its carrier universe is `max uF uV`,
the universe of the actual induced function space.

Finally, `glTemperedInductionPreservation.{uF,uV}` from
[TemperedInductionPreservationProof](TemperedInductionPreservationProof.md),
by Worker 540, receives exactly the original irreducibility and analytic
hypotheses, including the same input `μ`. It supplies the final analytic
conjunct. The proof returns these three results as the required conjunction.

## Analytic scope and dependency boundary

The input quotient is by the full center of the actual product Levi.
The analytic preservation proof obtains refined upper Jacquet bounds
directly from smooth-dual coefficients at the supplied input measure,
passes them through the actual normalized geometric lemma, and applies
the ambient analytic exponent criterion at carrier universe `max uF uV`.
Its induced admissibility and scalar-character premises are proved
independently.

The ambient criterion's analytic sufficiency uses coefficient estimates,
Cartan cells and convergent lattice sums, with the actual one-block group
and full-center quotient transport. Thus the output retains every
ambient Borel Haar measure, every smooth-dual coefficient and every real
`ε > 0` in the original `T.IsTempered` predicate. The input unitarity
proof separately uses the published fixed-Haar extension and analytic
tensor comparison. These comparisons are proved Library inputs; the
present assembly leaves no analytic bridge or measure-invariance premise.

This module composes the named published theorems. It uses no downstream
tempered exhaustion, square-integrable block induction, tempered
unitarity-and-genericity aggregate, or regular Langlands classification
proof. The target statement and all imported Lean and Markdown pairs
are preserved.

## Original sources and provenance

The source for the first conjunct is A. J. Silberger, *Introduction to
Harmonic Analysis on Reductive p-adic Groups* (1979), Corollary 4.5.13,
printed p.190, applied to the actual block Levi. Lemma 4.5.15, printed
p.191, states complete reducibility and temperedness of the positive-half
normalized induction. The registered original is
`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The original pp.190–191 (one-based PDF pp.196–197) were read and visually
checked.

Silberger's proof uses the character criterion and continuity of constant
terms for temperedness. The implemented analytic preservation instead
uses the exponent route of J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques d'après Harish-Chandra* (2003), III.2.2–III.2.3,
printed pp.265–267. The registered original is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Those original passages were read.

Both sources formulate temperedness by weak coefficient bounds.
The implemented `L^(2+ε)` comparisons are the published analytic
necessity, sufficiency, Haar and tensor proofs identified above and
documented in the imported proof pairs. The source assertions alone
are not used as formal implications. This contribution's new proof is
the internal assembly of those results. No source-specific errata file
for either original was present in the supplied project or current
Library notes when checked on 2026-10-31.
