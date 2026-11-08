# Compact-model continuation with transported character parameters

## Construction and provenance

`Langlands.Plancherel.transportedCompactModelContinuation` is an internal
derived constructor. It adapts the actual compact-model transport of
`CompactInductionModelChange` to parameters on a group `H` identified with
the literal Levi by an actual multiplicative homeomorphism `e : H ≃ₜ* M`.
It uses `unramifiedCharactersHomeomorph` and
`isPolynomialOperatorOn_transport_iff` from the published character and
operator transport interfaces. No new original-source translation is claimed.

The separate `compactModelContinuation` construction uses characters on the
literal Levi itself. This adapter keeps its denominator and operator
coefficients in the regular-function algebra of `H`. In the canonical scalar
application, `H` is the group of actual rational points of the reductive Levi
group scheme. No local-field, reductivity or rational-point realization is
needed to define this generic adapter.

## Inputs and output

Fix a locally compact nonarchimedean group `G`, two actual semidirect
decompositions of literal subgroups `P = M U` and `P' = M U'`, closed
parabolics and radicals, radical unimodular-modulus hypotheses, and continuous
Levi projections. Fix compact open subgroups `K₀`, `K₁`, their compactness,
and all four actual factorizations `G = P Kᵢ = P' Kᵢ`.

Fix a topological group `H`, an actual multiplicative homeomorphism `e` from
`H` to `M`, an arbitrary indexed continuous positive norm-character family
`ν` on `H`, and a canonical complex `SmoothRep` inducing representation `A`
of `M`. The ambient-group, parameter-group, norm-index and representation
carrier universes are independent.

Write `νM` for `ν` transported along `e.symm`, and `χM` for the actual
`unramifiedCharactersHomeomorph e ν`. For any parameter subset `Ω` of the
unramified characters of `H`, the input family `J` consists of actual ambient
intertwiners between the two normalized inductions at `χM χ`. The supplied
`RationalOperatorContinuationData p` continues the `K₀` compact conjugation
of exactly this family. It has a single regular denominator, nonzero on `Ω`,
a global per-input polynomial numerator family and an operator clearing law.

The output is continuation data for the `K₁` compact conjugation of the same
ambient family `J`, on the same `H` parameter subset `Ω`. Let `S` and `T`
be the actual compact-model equivalences for `P` and `P'`, respectively,
evaluated at the transported character. The new numerator is

`T(χM χ) ∘ p.numerator(χ) ∘ S(χM χ)⁻¹`.

The output denominator is literally `p.denominator` in the regular-function
algebra of `H`. No additional denominator or parameter restriction is used.

## Implemented verification and equations

The actual `M`-parameter transition and inverse transition families are
polynomial by `CompactInductionModelChange`. The proof pulls each family
back to the `H` parameter space using
`isPolynomialOperatorOn_transport_iff e ν Set.univ`, which uses the actual
equivalence of evaluation-generated regular-function algebras. Varying
polynomial operator composition with `p.polynomial` proves the output
numerator polynomial. There is no assumption that the transitions are
constant, and no admissibility or finite-dimensionality premise.

The clearing law follows by applying the actual ambient-intertwiner square
`compactIntertwiningOperator_modelChange` to `S(χM χ)⁻¹ f`, cancelling the
source transition, substituting `p.clears` and using linearity of `T`.
The comparison square is derived, not supplied as an input.

The accompanying equations expose the unchanged denominator and the precise
numerator, prove equality of regular regions, and show that the continued
linear operators are conjugate by these same parameter-dependent transitions
on the whole original regular region. The last theorem expresses this as a
commuting square. Expanding the reciprocal-denominator definition and moving
the scalar through `T` proves the continued conjugation; inverse cancellation
then proves the square.

## Scope

Initial continuation is an explicit input. Neither its existence nor any
standard-integral convergence theorem is proved. No nonempty or open subset
is assumed; an empty original subset does not imply a nonempty regular
region. Generic structural and representation data are supplied, with no
claim of actual rational-point realization.

This constructor compares its output with its input. Uniqueness against an
independently chosen continuation, canonical composite-scalar independence,
source-normalized `j` or `mu`, nonvanishing, positivity, parabolic or measure
independence and the Plancherel theorem remain separate obligations.
