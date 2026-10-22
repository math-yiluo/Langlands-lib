# Actual relative idele-class cohomology

This module constructs ordinary relative group cohomology with the genuine
idele-class coefficients and compares its degree-two classes with the
published `RelativeIdeleCocycle`. All declarations are in
`Langlands.ClassField.Global` or its `RelativeIdeleCocycle` namespace.

## Fields, coefficients and arithmetic action

The field parameters are `K : Type u` and `E : Type v`, in independent
universes, with `[Field K] [Field E] [NumberField E] [Algebra K E]`.
The acting group is `E ≃ₐ[K] E` and the multiplicative coefficient carrier
is exactly `NumberField.IdeleClassGroup (𝓞 E) E`. The module installs the
published `relativeIdeleClassAction K E` locally. It does not accept an
unrelated action as an instance parameter.

`relativeIdeleClassRepresentation` specializes
`NormalizedTwoCocycle.coefficientRepresentation` to these carriers. Its
underlying additive group is `Additive (IdeleClassGroup (𝓞 E) E)` and its
scalar ring is `NormalizedTwoCocycle.CoefficientScalars.{v}`, the explicit
universe lift of `ℤ`. The generic `coefficientScalarsEquiv` identifies this
ring with the ordinary integers. Only the scalar universe is lifted.

`relativeIdeleClassRepresentation_apply` proves that the representation's
action is precisely `relativeIdeleClassAut K E`. The theorem with suffix
`_apply_mk` identifies the value on the quotient class of an idele `a` with
the quotient class of `ideleEquiv σ.toRingEquiv a`. Both identities are
proved by reflexivity from the actual published transport and action.

`relativeIdeleClassCohomology K E n` is Mathlib's
`groupCohomology (relativeIdeleClassRepresentation K E) n`, as a module over
the lifted integers. These constructions work for any extension with the
listed assumptions, and hence for finite Galois extensions of number
fields. The finite-dimensionality, normality and separability assumptions
are unnecessary for this purely algebraic construction. No topology is
used in these cohomology groups. The discrete topology used by the
published extension construction is a separate explicit choice.

## Cocycle comparison

`relativeIdeleClass_differential₁₂` and
`relativeIdeleClass_differential₂₃` identify Mathlib's additive differentials
with the formulas

- `(σ • b(τ)) / b(στ) * b(σ)`;
- `(σ • f(τ,υ)) / f(στ,υ) * f(σ,τυ) / f(σ,τ)`.

The Lean conclusions write the action as `relativeIdeleClassAut K E`
explicitly, and both equalities hold definitionally. This fixes the sign
and action conventions for the comparison.

Within `RelativeIdeleCocycle`, `toCocycle₂` is the actual additive cocycle
and `cohomologyClass` is its image under `H2π` in
`relativeIdeleClassCohomology K E 2`. `toCocycle₂_apply` states the pointwise
conversion. `normalizedRepresentative` specializes the generic subtraction
of the boundary of the constant one-cochain `f(1,1)`.
`normalizedRepresentative_apply` states its value as the multiplicative
value of `f(σ,τ)` divided by the arithmetic action of `σ` on the value
of `f(1,1)`. `cohomologyClass_normalizedRepresentative` proves that the
class is unchanged. `cohomologyClass_surjective` therefore supplies a
normalized multiplicative idele-class cocycle representing every actual
second cohomology class. Its proof is the generic proof via Mathlib's
`H2_induction_on` and the explicit normalization calculation.

`cohomologyClass_eq_of_cochain` specializes the generic range-witness proof:
if `c(σ,τ)*b(στ)=b(σ)*(σ • b(τ))*d(σ,τ)`, then `c` and `d` have equal
classes. This applies in particular to normalized cochains; a separate
normalization assumption is not needed for the class equality.
`cohomologyClass_eq_of_mapData` gives the same equality for the existing
identity-component `NormalizedTwoCocycle.MapData`. These are direct uses
of the generic intrinsic proofs, with no new extension-map construction.

## Provenance and arithmetic boundary

This is a derived specialization of
`Langlands.GroupTheory.CocycleCohomology` and the published actual arithmetic
action in `Langlands.ClassField.Global.Cocycle`. The cocycle and coboundary
conventions are from Artin and Tate, *Class Field Theory* (2009), Chapter
XIII section 1, printed pp.127–129 (PDF pp.136–138), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The proofs use Mathlib's actual cochain and cohomology objects, as explained
in the generic module's paired Markdown.

No class is selected or called fundamental. The global invariant,
arithmetic H¹ vanishing, fundamental-class existence and normalization,
transition compatibility, and reciprocity remain later obligations.
The distinct arithmetic role of a fundamental class is explained in
Artin–Tate, Chapter XV, printed pp.167–169 (PDF pp.176–178). This module
supplies only the coefficient and representative interface for that work.
