# Derivative vanishing outside multiples of the cuspidal rank

Internal consequence of the published nondivisible-block Jacquet vanishing
and actual positive two-block Jacquet-to-derivative comparison. The predicate
`NondivisibleProperDerivativeVanishing T r π` says that, for every supplied
nontrivial unitary additive character and every order `0 < k < n`, the
actual order-`k` derivative of `π` has a zero carrier whenever `r` does not
divide `k`. Zero carriers are expressed by `Subsingleton`. Field and carrier
universes remain independent; the actual representation carriers lie in
`Type (max uF uV)`, as in the host repeated cuspidal triple target.

For every actual subquotient of a normalized product of actual
supercuspidal factors, the module proves this predicate for any common
divisor of the inducing block ranks. The total inducing rank is positive;
no uniformity, irreducibility, admissibility, finite length or relation
between the supercuspidal factors is needed for this conclusion.

The proof identifies the derivative, after rank transport, with the partial
derivative of the normalized two-block Jacquet module. The latter partial
derivative is an actual quotient of a zero carrier. The inverse-equipped
comparison transfers the zero carrier to the rank-cast derivative, and
equality elimination removes the rank cast. Writing `n = a + k`, with
`a > 0`, the second Jacquet block has size `k`. The existing divisibility
theorem makes that Jacquet module zero when `r` does not divide `k`.
This proves the implication from `NondivisibleJacquetVanishing` and gives
the actual cuspidal-product result by the published subquotient
Jacquet-vanishing theorem.

The segment quotient and head specializations use only the actual quotient
map from the increasing segment induction. For a length-two head, the only
positive multiple of its rank strictly below its degree is its rank itself.
Thus every other proper positive derivative vanishes. The derivative of
order equal to the rank, the top derivative, their dimensions and the local
rank-three irreducibility calculation remain separate obligations.

The provenance is internal. The two direct imports are
`Classification.UniformJacquetVanishing` and
`Derivative.PartialDerivativeJacquetComparisonProof`. The former proves
its vanishing through the actual geometric lemma, quasicuspidality of
the external tensor, the finite block-size divisibility obstruction,
and exactness on actual Jacquet subquotients. The latter comparison is
an actual natural isomorphism constructed from quotient presentations,
with the supplied topology and determinant normalizations. The new
proof needs only that isomorphism and the surjective actual partial
quotient map.

At Library base `0acb0c6492f21de608601e6283ccd1944725452a`, the recursive
closure contains 361 existing project modules. Its classification branch
consists of `ConstituentRelations`, `SegmentEdgeFactorHypotheses`,
`SegmentEdgeJacquetStatement`, `SegmentQuotientJacquetSingleBlock`,
`Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`,
`SupercuspidalTwist`, `TwoSupercuspidalProductStructureStatement` and
`UniformJacquetVanishing`. The conditional edge and two-supercuspidal
formulas are proposition definitions, not mathematical inputs to this
proof. The one-block segment Jacquet module supplies only elementary
whole-group transport, not a general segment Jacquet formula.

The implemented dependencies use neither global support decomposition
nor general ordered quotient coverage, multisegment classification,
analytic segment classification, special-head exhaustion, ordered
special-head existence, tempered block uniqueness, square-integrable
Langlands classification, square-integrable exhaustion or regular
exhaustion. No proof successor of those conclusions occurs in the
project closure. This unit also uses no derivative Leibniz formula,
two-supercuspidal adjacent reducibility theorem, special-head existence
theorem or general segment derivative formula. Given segment quotient
and head relations provide actual quotient maps; the proof does not
infer their existence.
