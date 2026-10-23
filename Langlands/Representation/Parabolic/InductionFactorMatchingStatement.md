# Normalized induction preserves Jordan–Hölder matching with finite-length outputs

Authors: Worker 122 and Worker 289. Worker 289 specified the formulation and
its role in the adjacent-block-swap argument.

This module names the actual induced object and its matching and finite-length
predicates, then defines the proposition
`Langlands.Parabolic.NormalizedInductionFactorMatchingTheorem.{uF, uV, uW}`.
It states a derived consequence of normalized parabolic induction exactness.
It contains no proof of this proposition.

## Exact statement

For every prime natural number `p`, every `F : PadicField.{uF} p`, every
compatible realization `T : F.TopologicalData`, every natural rank `n`, and
every `B : BlockShape n`, take smooth complex representations

- `σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`;
- `τ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier)`.

The topology is `T.topology`, with `T.generalLinearTopologicalGroup n`
installed as in the published induction construction. Set, for exposition,
`Iσ := T.normalizedParabolicInduced B σ.representation` and
`Iτ := T.normalizedParabolicInduced B τ.representation`. After unfolding the
named predicates below, the hypotheses are exactly:

1. `HaveSameJordanHolderFactors (Rep.of σ.representation) (Rep.of τ.representation)`.
2. `IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) Iσ.asModule`.
3. `IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) Iτ.asModule`.

The conclusion is
`HaveSameJordanHolderFactors (Rep.of Iσ) (Rep.of Iτ)`.

The Lean statement uses the following definitions to retain the actual
objects without repeatedly expanding their function carriers and module
instances in its elaborated proposition:

| Name in `Langlands.Parabolic` | Defining meaning |
| --- | --- |
| `normalizedInductionObject T B σ` | The actual `Rep.of Iσ`, with carrier universe `max uF uV`. |
| `NormalizedInductionSourceMatching T B σ τ` | `HaveSameJordanHolderFactors (Rep.of σ.representation) (Rep.of τ.representation)`. |
| `NormalizedInductionOutputFiniteLength T B σ` | `IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) (normalizedInductionObject T B σ).ρ.asModule`. |
| `NormalizedInductionOutputMatching T B σ τ` | `HaveSameJordanHolderFactors (normalizedInductionObject T B σ) (normalizedInductionObject T B τ)`. |

The three predicates are `Prop`-valued definitions. The object definition
constructs the published induction itself; it accepts no supplied replacement
object or comparison theorem. Unfolding these four definitions recovers the
displayed statement by definitional equality. They introduce no new
mathematical hypothesis, choice of composition series, or factor labels.
The final declaration quantifies over the data above and asserts source
matching, then the two output finite-length hypotheses, then output matching
as successive implications.

The first predicate is the published one from
`Langlands.Representation.Filtration.ObjectDefinitions`. It asserts the
existence of two actual finite composition series of a common length, a
permutation of their factor indices, and a `Representation.Equiv` for each
matched pair of actual graded quotients. Consequently both hypothesis and
conclusion preserve multiplicities. They do not merely compare sets of
irreducible subquotients.

The finite-length hypotheses concern the actual induced group-algebra
modules, not the Levi modules, dimensions over `ℂ`, or replacement objects.
The source matching already supplies finite composition series for the
Levi representations. No irreducibility, admissibility, cuspidality,
finite-dimensionality, nonzero-carrier, positive-rank, or extra exactness
hypothesis is imposed. Zero and reducible representations are included.
The field and two input-carrier universes are independent; the respective
induced function carriers lie in `Type (max uF uV)` and `Type (max uF uW)`.

## Actual induction and normalization

The module imports `Langlands.Representation.Induction.Parabolic`. Its
`T.normalizedParabolicInduced` inflates the given Levi representation along
`B.leviProjection F.Carrier`, twists by `T.parabolicHalfModulus B`, and uses
smooth induction on the actual covariant function space with right
translation. The character is the positive square root of the Library's
explicit block modulus. No new induction data or arbitrary representation
is substituted in this statement.

## Sources and derived provenance

Source: I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
Registered source ID: `bernstein-zelevinsky-1977-induced-i`.
Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Worker 122 read PDF pages 4–7 and 11, including the rendered pages 7 and 11,
on 2026-10-23 and verified this fingerprint. No corresponding project
`notes/errata/bernstein-zelevinsky-1977-induced-i.md` was present.

The relevant source locations are:

- §1.2, printed p.443 / PDF p.4: smooth complex representations and the
  multiplicity-sensitive `JH⁰` for finite-length representations.
- §1.8(a), printed p.444 / PDF p.5: normalized covariant functions and
  right translation; Proposition 1.9(a), (e), printed p.445 / PDF p.6:
  exactness and agreement of smooth and compact induction when the
  parabolic quotient is compact.
- §2.3(a), printed p.446 / PDF p.7: exactness of normalized parabolic
  induction; the following paragraph records compactness modulo the
  parabolic.
- §2.16(2), printed p.450 / PDF p.11: the elementary-map argument invokes
  induction in stages and exactness, §2.3(c), (a), to pass from the
  two-block case to matching factors in the ambient group.

This proposition is a derived formulation, not a verbatim theorem of BZ77.
It isolates the finite-series consequence of exactness used in that last
step. BZ77 uses a Haar-module normalization; the actual Library construction
uses its explicit block character. The construction's Markdown records
their separate comparison obligation. The algebraic argument here depends
on exactness of the actual normalized construction and on the stated output
finite length, so it does not assume that comparison as an extra hypothesis.

For the intended derivation, apply induction to the two composition series
supplied by the source matching. Exactness gives filtrations of the actual
outputs whose graded quotients are equivalent to the induced source
quotients. These induced quotients need not be simple. They have finite
length because they are subquotients of the finite-length outputs.
Functoriality carries each original factor equivalence to an equivalence
of the induced quotients. Transport their composition series and use
`Langlands.GradedJordanHolderRefinementStatement` to obtain the desired
matching. Repeated filtration steps and zero graded pieces are allowed.
This is a proof plan for a separate task; it is not implemented in this module.

## Finite-length boundary and downstream use

Exactness alone does not imply that a functor preserves finite length.
Both output finite-length hypotheses are therefore intentional. This
statement does not prove finite length of induction, nor does it assume
that induction preserves simplicity.

In the adjacent-block-swap application, the caller must supply the output
finite-length proofs using the separately stated
`Langlands.CuspidalSupport.CuspidalInductionLengthTheorem` and actual
induction-in-stages equivalences. This module supplies neither those proofs
nor the full cuspidal association theorem.
