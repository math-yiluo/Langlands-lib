# Scalar norms from arbitrary unitary exponent data

`Langlands.unitaryExponentScalarNorm.{uG,uV}` proves the exact published
proposition `Langlands.UnitaryExponentScalarNorm.{uG,uV}`. The group and
carrier universes are independent. For an arbitrary group `G`, a nontrivial
complex vector space `V`, a positive character `ν : G →* ℝ≥0ˣ`, an actual
representation `ρ`, and any witness `u : UnitaryExponentData ν ρ`, it proves

`‖c‖ = ((ν g : ℝ≥0) : ℝ) ^ u.exponent`

whenever `ρ g v = c • v` for every `v : V`.

## Implemented proof

Choose `v ≠ 0` using `Nontrivial V`. Write `a = ((ν g : ℝ≥0) : ℝ)` and
`e = u.exponent`. Since `ν g` is a unit in the nonnegative reals, `a > 0`.
Set `k = (a ^ (-e) : ℂ) * c`.

The law `realPowerTwist_apply` and the scalar-action hypothesis show that the
negative-exponent twist sends `v` to `k • v`. Apply the invariance field of
**the supplied form** `u.form` to `(g, v, v)`. Its `InnerProductSpace.Core`
is installed locally only to use the core sesquilinearity lemmas. This gives

`conj(k) * k * u.form.inner v v = u.form.inner v v`.

Definiteness and `v ≠ 0` show that the diagonal value is nonzero. Cancel it
to obtain `conj(k) * k = 1`. Taking complex norms gives
`‖k‖ * ‖k‖ = 1`; nonnegativity of the norm and injectivity of squaring on
nonnegative reals give `‖k‖ = 1`.

The real power `a ^ (-e)` is positive, so the norm of its complex embedding
is itself. Thus `a ^ (-e) * ‖c‖ = 1`. The identity `Real.rpow_neg` rewrites
this as `(a ^ e)⁻¹ * ‖c‖ = 1`. Finally multiply by the nonzero positive
number `a ^ e` to obtain the stated conclusion.

## Scope and provenance

This is an internal algebraic consequence of `UnitaryExponentData`,
`InvariantPositiveForm` and `realPowerTwist`. It uses precisely the arbitrary
form contained in the given witness. No norm or topology is constructed or
assumed on `V`; the local `Inner` and core instances describe only that form.
The theorem has no additional hypotheses concerning smoothness,
irreducibility, admissibility, dimension, square-integrability, central
characters, topology or measures, and does not require `c` to be a unit.
`Nontrivial V` supplies the nonzero vector used for cancellation.

The only direct project import is the published scalar-norm statement. Its
project import closure contains `Classification.Essential` and the underlying
twist, invariant-form, matrix-coefficient and smooth-admissibility interfaces.
It contains no linked-head comparison, square-integrable nonlinkage, ordered
conversion, exhaustion, classification, tempered-block uniqueness,
ordered-head existence or quotient-coverage result. This theorem does not
establish any of those further classification results.

Worker 438 implemented this proof from the elementary calculation documented
by Worker 252 in the target statement and task context. Worker 252 is credited
for that derivation. No external literature or unpublished proof draft is used.
