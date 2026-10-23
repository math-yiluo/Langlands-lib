# Jacquet stabilization and local coefficient existence

This module states the analytic obligations connecting the actual induced
Jacquet integrals to Shahidi's rational local coefficient. It also proves the
algebraic inverse-scalar step under explicit multiplicity-one and nonzero
pullback hypotheses. No analytic theorem is assumed or proved in this module.

## Original source and provenance

The source is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)* (1984), registered as
`shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

- Printed page 70 fixes the nontrivial unitary additive character with largest
  trivial fractional ideal equal to the ring of integers.
- Printed page 72 defines the intertwining integral (0.1), states its rational
  continuation, defines the source Whittaker functional (0.2), and states the
  inverse-coefficient relation (0.3). The display following (0.3) defines the
  target functional with the reversed tensor factors and inverse Weyl element.
- Printed page 73 explicitly records dependence of the coefficient on the
  measures. The following section introduces additional equal-rank,
  unitary/supercuspidal hypotheses for an intermediate comparison argument.
- Printed page 78, equation (1.1) and its following paragraph, interprets the
  Jacquet integral by stabilization over sufficiently large compact open
  subgroups after the specified inverse-Weyl right translation.
- Printed page 103, Theorem 5.1 and (5.2), identifies the coefficient, after
  suitable measure normalization, with the primed factor. It supplies an
  additional source for the rational coefficient existence assertion; the
  gamma comparison itself is a separate target.

The statement unit has **derived** provenance. It separates the stabilization,
Whittaker-line, and rational-existence inputs of the source's construction,
using the Library's actual induced representations and integral relations.
The source's assertion following (0.2) invokes its reference [19]; this module
does not claim to formalize that reference's proof. The induced
multiplicity-one statement isolates the structural uniqueness input rather
than invoking irreducible multiplicity one on an induced representation that
may be reducible. The page-78 stabilization discussion lies in the equal-rank
section; the all-rank target spells out the stable-integral interpretation of
the all-rank functional (0.2). No all-rank stabilization proof is claimed.

Rational existence with arbitrary Haar choices is the measure-dependent form
of the construction. Rescaling the intertwining, source-Jacquet, and
target-Jacquet measures by positive factors `a`, `b`, and `d` changes `C` to
`b / (a*d)` times `C`. Thus a rational coefficient remains rational; this
explains the universal measure quantifiers without asserting independence of
measures. This transfer and analytic existence remain obligations of the
statement, not proved lemmas here.

## Objects and common hypotheses

The namespace is `Langlands.PadicField.TopologicalData`. A parameter `T`
supplies topology and local-field structure for a finite extension `F` of
`Q_p`. All three analytic statements take natural numbers `m,n`; the factor
ranks are `m+1,n+1`, covering every positive pair. The universe of the field
and the common universe of the two complex representation carriers are
independent. No norm or topology is required on those carriers.

The statements install the topology and valuation from `T`. Statements using
integrals install the Borel measurable structure. The additive character is
a `UnitaryAdditiveCharacter`, which already includes continuity and
nontriviality, and satisfies `T.additiveConductor ψ = 0`. In the Library's
conductor convention this means the largest trivial fractional ideal is
`O_F`. The factor hypotheses are `Whittaker.IsGeneric ψ m π₁` and
`Whittaker.IsGeneric ψ n π₂`; these include irreducibility, admissibility,
and existence of a nonzero standard Whittaker functional.

The induced representations are exactly `T.shahidiSource` and
`T.shahidiTarget`, on `T.ShahidiSourceSpace` and `T.ShahidiTargetSpace`.
They use the published normalized induction of the factors twisted by
`|det|^(s/2)` and `|det|^(-s/2)`, with covariance exponents
`(s+n+1)/2` and `-(s+m+1)/2`. The documented twice-halved display issue on
printed pages 67 and 72 and its interpretation from page 84 are inherited
from `Induction`; this unit makes no new exponent convention.

The full-group Whittaker index is `m+1+n`, so the group rank is
`(m+1+n)+1 = (m+1)+(n+1)`. Both factor functionals use the standard `ψ`
character. The two Jacquet kernels use its conjugate, as in (0.2). This is
not a change to the separate JPSS convention pairing `ψ` and `ψ⁻¹` models.

## Analytic declarations

`ShahidiJacquetStabilizationStatement` quantifies over both Haar measures,
both generic factors, every pair of nonzero standard factor functionals,
and every complex `s`. Its conclusion asserts existence of a source linear
form and a target linear form. Each satisfies all three requirements:

- It has the published `IsSourceJacquetFunctional` or
  `IsTargetJacquetFunctional` graph, respectively.
- It belongs to the actual standard Whittaker-functional submodule of the
  corresponding induced representation.
- It is nonzero.

The source graph uses `pairFunctional ℓ₁ ℓ₂`, the block Weyl element, and
`rectangularMeasure νJ (n+1) (m+1)`. The target graph uses
`pairFunctional ℓ₂ ℓ₁`, the inverse Weyl element, and
`rectangularMeasure νJ' (m+1) (n+1)`. The two measures are independent here.
Each graph requires integrability and a fixed value on every compact open
additive subgroup beyond an actual threshold, for every section. It never
asserts absolute integrability over the entire noncompact radical.

`ShahidiInducedWhittakerMultiplicityOneStatement` says that, for either of
the same induced representations and every `s`, every standard Whittaker
functional is a complex scalar multiple of any specified nonzero one.
Existence is supplied by the separate stabilization statement, not built
into this conditional spanning assertion. Neither induced representation
is assumed irreducible.

`ShahidiLocalCoefficientExistenceStatement` quantifies over three additive
Haar measures `ν,νJ,νJ'` on `F` and asserts
`∃ C : RatFunc ℂ, T.IsShahidiLocalCoefficient ... C`, with the corresponding
rectangular product measures. The published relation requires the same
rational function for all nonzero choices of standard factor functionals.
For each such choice it supplies a right half-plane on which `C` has no
pole, the source functional has a nonzero value on some section, and the
actual integral relation holds on every induced section, with

`λ'_(−s)(A_s f) = C(q^(−s))⁻¹ λ_s(f)`.

In particular the evaluated coefficient is nonzero on that half-plane. No
coefficient is selected from this unproved existence assertion. Existing
`IsShahidiLocalCoefficient.unique` proves uniqueness when witnesses are
available. The half-plane need not be uniform across choices of factor
functionals, in agreement with the quantifier order of the published relation.

`ShahidiJacquetAndCoefficientStatement` is the conjunction of those three
Prop-valued statements. It assumes none of them. It is the entry target for
this focused item-3 statement unit.

## Implemented algebraic argument

`Langlands.Shahidi.existsUnique_inverseScalar_of_multiplicityOne` is a
proved lemma for an arbitrary group, subgroup character, actual source and
target representations, and an intertwiner `A`. It takes a nonzero
Whittaker functional `Λ` on the source and a Whittaker functional `Λ'` on the
target. Its explicit additional assumptions are that `Λ' ∘ A` is nonzero
and every source Whittaker functional is a multiple of `Λ`.

The proof uses the published `Whittaker.functionalsComap` to place
`Λ' ∘ A` in the source Whittaker space. The spanning hypothesis gives
`Λ' ∘ A = a • Λ`. Nonzero pullback forces `a ≠ 0`, so the coefficient is
`c = a⁻¹`. Injectivity of scalar multiplication on the nonzero form `Λ`,
followed by injectivity of inversion, proves uniqueness of `c`. The conclusion
is exactly `∃! c, c ≠ 0 ∧ Λ' ∘ A = c⁻¹ • Λ`.

This lemma does not infer nonzero pullback merely from `Λ' ≠ 0`, and it does
not infer rational dependence on `s` from a pointwise scalar. When applied
to Shahidi's operator, convergence on the whole source, the intertwining
property, nonzero pullback, and rational dependence are analytic obligations.
The last of the three statements includes the resulting existence assertion.

## Scope and remaining work

These targets cover finite extensions of `Q_p`; they do not supply the
positive-characteristic local-field specialization. The underlying general
Jacquet definitions remain available separately. No unitary or supercuspidal
restriction is introduced here. All analytic proofs remain open.

Arbitrary fixed measures are appropriate for coefficient existence. They do
not give the coupled normalization required by the gamma comparison. This
module does not assert Theorem 5.1, measure independence, self-duality of a
matrix measure, or a gamma/epsilon identification. The explicit geometric
measure coupling and its connection to the comparison witnesses belong to
the separate item-5 work.
