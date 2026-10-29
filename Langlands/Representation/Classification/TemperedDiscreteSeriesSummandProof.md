# Discrete-series summands of irreducible tempered GL representations

Author: Worker 388.

`Langlands.glTemperedDiscreteSeriesSummand` proves exactly the closed
proposition `Langlands.GLTemperedDiscreteSeriesSummandStatement.{uF, uV, uW}`
from `TemperedSupportStatement`. It retains every quantified premise of
that proposition: a supplied finite p-adic field and topological data,
positive rank, an actual block shape, an irreducible analytically tempered
representation `π`, and an irreducible analytically square-integrable
representation `σ` of the actual full product Levi. The given Borel Haar
measure on the quotient by the full Levi center is arbitrary. The field,
original carrier and Levi carrier universes `uF`, `uV` and `uW` are
independent. There is no additional hypothesis on the theorem.

For the forward implication, the hypothesis gives an actual invariant
subrepresentation of the opposite normalized Jacquet representation with
a surjective intertwiner to `σ`. The published
`glTemperedDiscreteSeriesJacquetQuotient` promotes this subquotient to a
surjective intertwiner from the whole Jacquet representation. Tempered
admissibility supplies smoothness of `π`, so
`OppositeSupport.quotient_iff_embedding` turns that quotient into an actual
injective intertwiner `jopposite` from `π` into opposite normalized
induction. The published `glTemperedDiscreteSeriesOppositeToUpper` gives
an actual injective intertwiner `jupper` into upper normalized induction
of the same original `σ`.

The published `isSemisimple_bothInduced_of_squareIntegrable` supplies
algebraic semisimplicity of both actual inductions for the same specified
measure and representation. Its proof constructs an invariant positive
Hermitian form on the original Levi carrier by the coefficient integral,
applies normalized induction unitarity and admissibility, and transports
semisimplicity along the actual block reversal for the opposite induction.
Applying `semisimpleRetraction` to each injective intertwiner constructs
actual intertwiners `rupper` and `ropposite`. Their defining properties are
exactly `rupper.comp jupper = id` and `ropposite.comp jopposite = id`.
Together with both semisimplicity statements these are all four clauses of
the required conclusion.

For the reverse implication, applying `ropposite` to equality of two
images under `jopposite`, then using the given composite-to-identity
equation, proves injectivity of `jopposite`. The published
`OppositeSupport.occurs_of_embedding` supplies the required actual
subquotient. That adapter evaluates on the opposite Jacquet quotient to
obtain a surjective intertwiner to `σ` and regards it as a quotient of the
full invariant subrepresentation. The reverse implication requires only
the opposite splitting among the four supplied clauses.

The target's local Jacquet action is definitionally
`OppositeSupport.jacquetAction T B π`: the action on actual opposite
unipotent coinvariants with inverse full upper modulus, transported from
the embedded Levi to the product Levi. Its normalization multiplier is
therefore the positive upper half modulus. Upper normalized induction has
positive upper-half covariance; opposite induction has inverse upper-half
covariance. Both use right translation. All quotient, subgroup and
function-space constructions remain those fixed by the statement, and
both final inductions use the original given `σ`.

The proof is an internal composition of the published quotient criterion,
opposite reciprocity, same-sigma comparison and square-integrable induced
semisimplicity. It introduces no new analytic assertion or source bridge.
The target corresponds to Silberger 1979, Theorem 4.5.18, printed p.193
(PDF p.199), registered as `silberger-1979-harmonic-analysis`. The
implemented route uses the actual adjointness and scalar-layer proofs
behind the named Library inputs; it does not claim to transcribe the
book's proof. It assumes no full tempered-induction proposition, regular
Langlands head theorem, regular or tempered exhaustion, or
square-integrable Langlands classification. None of those proof modules
is needed in its import closure.
