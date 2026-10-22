# Frobenius correction and semisimplification statements

Worker 1 develops these proposition definitions for task
`c5aface6-9b98-4eed-a79b-51092cd9ef2d`. They are unreviewed development, not
theorems. Target proofs belong to separate tasks naming the published statement.

The file imports the actual `WeilDeligneRepresentation` from Worker 17,
including its finite-dimensional carrier, nilpotent monodromy and norm
covariance. It reuses the companion's actual morphisms, isomorphisms,
Frobenius-semisimplicity and topology predicates. It does not construct a
second parameter type.

## Hypotheses and conventions

The generic algebraic correction theorem assumes a surjective integer degree
map, finite image of the Weil action on its kernel, and a supplied norm character equal to
`q^(-degree)` for a natural `q > 1`. Geometric Frobenius has degree +1, so
its norm is `q^-1`. Nilpotence and covariance are inherited from the actual
pair. Finite inertia is an explicitly stated algebraic hypothesis, not a
replacement for usual complex continuity or open inertia kernel. The last two
targets preserve these separate companion predicates. The continuity target
also requires continuous degree.

`monodromyExponential A a` is the actual finite polynomial
`sum_(0 <= j < dim A) a^j/j! N^j`. Because N is nilpotent on a finite-dimensional
space, this is the nilpotent exponential in the sources. The zero-dimensional
case is allowed. No completion, norm selection, or convergence axiom is used.

`IsCorrectionAt` requires an actual unipotent automorphism centralizing N and
the entire Weil image, whose removal makes the chosen Frobenius semisimple.
`IsCorrection` includes Tate's stronger formulation with every exponential
parameter and every element outside inertia. These are candidate predicates;
their existence and uniqueness are conclusions of proposition definitions.

`IsSemisimplificationOn` keeps the original carrier and N. Its uniqueness
claim is equality of actual Weil actions. `IsSemisimplificationAlong` records
a specified linear identification with a new carrier and exactly transports N
and the corrected action. `IsSemisimplification` existentially quantifies that
identification. Uniqueness across different carriers is genuine WD
isomorphism, not equality of carrier types.

The corrected action is `r(g) u^(-degree(g))`. Idempotence uses the companion's
Frobenius-semisimplicity predicate, which permits N to be nonzero. The
semisimplicity comparison concerns only the underlying Weil representation.
Ordinary WD semisimplicity is a separate target family.

## Declaration-level source map

| Declaration | Source correspondence or explicit derivation |
| --- | --- |
| `NormCompatible` | Deligne 8.5 and Tate 4.1.3: geometric degree and normalized norm. Surjectivity remains a separate hypothesis. |
| `monodromyExponential` | Finite nilpotent exponential in Deligne 8.5 and Tate 4.1.3. |
| `IsCorrectionAt` | Deligne 8.5 first paragraph: unipotent part of Frobenius, commuting with N and the full Weil image. |
| `IsCorrection` | Tate 4.1.3's unique unipotent correction with all nonzero degrees and all exponential parameters. |
| `IsSemisimplificationOn`, `IsSemisimplificationAlong`, `IsSemisimplification` | Deligne (8.5.1), 8.6(i), Tate 4.1.3; explicit fixed-carrier and transported versions of the same construction. |
| `CorrectionExistence` | Deligne 8.5 and Tate 4.1.3, with actual existential uniqueness. |
| `ChoiceIndependence` | Deligne 8.5 identifies the unipotent part for every nonzero degree; Tate 4.1.3 gives the choice-free characterization. |
| `SameCarrierExistence`, `PairExistence` | Deligne 8.5–8.6; existence of the representation law and actual WD output are conclusions. |
| `PairUniqueness` | Derived from uniqueness of correction and conjugation by the specified linear carrier identifications. |
| `Idempotence` | Derived from the fixed-point criterion of Deligne 8.6(ii) and Tate 4.1.3. |
| `WeilSemisimplicityComparison` | Tate 4.1.3 explicitly compares Frobenius semisimplicity with ordinary semisimplicity of the underlying Weil representation. |
| `CorrectionNaturality`, `MorphismCompatibility`, `IsomorphismCompatibility` | Derived naturality of the multiplicative Jordan decomposition in Deligne 8.5. Every original morphism is retained; fullness is not asserted. |
| `Invariants` | N is unchanged in Deligne 8.6(i); all its power kernels/images transport exactly. Inertia is unchanged and determinants are unchanged because the correcting factor is unipotent. These are linear-algebra consequences of the formula. |
| `NonzeroMonodromyScaling` | Deligne 8.4.3, with the necessary nonzero-scalar condition made explicit. No classification hypothesis is assumed. |
| `AlgebraicFamily` | Conjunction of all algebraic assertion families above; no extra hypothesis. |
| `ParameterPreservation` | Same inertia action under the carrier identification, hence the same inertia kernel. Tate 4.1.2 supplies the parameter condition. |
| `ContinuityPreservation` | Derived from continuous degree, the corrected formula, and continuity of linear maps and composition in the usual finite-dimensional complex topology. It is not an assertion that arbitrary finite image implies continuity. |
| `Statement` | Whole target combining the algebraic family with both separate topology-preservation targets. |

## Original sources

Worker 1 read the originals and checked the displayed formulas visually.

- Deligne, *Les constantes des equations fonctionnelles des fonctions L* (1973),
  registered ID `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  Retained file:
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
  Exact locators: 8.4.1 and 8.4.3, internal/PDF pages 68–69; 8.5, equation
  (8.5.1), and 8.6, internal/PDF page 70. The image on PDF69 reads Del-69.
  The scaling sentence in 8.4.3 must exclude zero: invertible conjugation
  cannot kill nonzero monodromy.
- Tate, *Number theoretic background* (1979), registered ID
  `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Retained file:
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
  Exact locators: 4.1.2–4.1.5, printed page 20 / PDF29, and 4.1.6,
  printed pages 20–21 / PDF29–30. The minus sign in `u^(-v(w))` was
  visually checked. Arithmetic local-factor identities are not asserted here.

## Exact development dependencies and remaining acceptance

The pair core was first consumed from Worker 17's shared draft
revision 1, content key
`dd4dcdc52a3c88f855a849a0bf58df89f6e38fc3843c3c26121d0543df2c3372`,
task `503968de-16f8-4f63-ba13-b5e167e11dce`.
The four imported Lean files remain unchanged and remain Worker 17's work:

- `Langlands/Weil/Representation/Basic.lean`:
  `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b`.
- `Langlands/Weil/Representation/Predicates.lean`:
  `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148`.
- `Langlands/WeilDeligne/Basic.lean`:
  `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf`.
- `Langlands/WeilDeligne/Parameters.lean`:
  `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c`.

All four dependency pairs are verified in the current Library at commit
`459d17160ca3aef5c5b4e8ba056125e56d9479a0`, with the unchanged Lean hashes
above. The WD core received independent semantic approval from Reviewer 177
and was published at commit `e4e22245747ec04edd4445d4557b746f8f53de29`.
The imports and their final paired Markdown now match the published Library;
no companion source is included as new authored content.
Prepared environment: artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1,
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The successful development check `ba853502-bb09-4536-9861-6930aed48645`
compiled all four dependencies and this module with no errors or warnings.
It inspected `Langlands.WeilDeligneRepresentation.Frobenius.Statement`,
confirmed `statement_returns_prop: true`, and returned whole-target SHA-256
`731f7a26070579da9f17239888902f37ca4951b2d58dfd5fa756ce8c90acb841`.
Its independent universes are `uG`, `uV`, `uW`, and `uX`.
This is development evidence, not semantic acceptance or a theorem proof.
Independent statement review and current Library publication remain required.
