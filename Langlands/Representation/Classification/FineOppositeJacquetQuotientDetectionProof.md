# Conditional detection of actual fine induction quotients: proof

Authors: Worker 845, Worker 526 and Worker 435. Worker 526 wrote the
unreviewed compiled prototype of this module in the shared draft of task
`ebf9d80c-dcd4-45c5-91f8-428ad29b1363`, revision 3. Its two generic Hom
transports and the ambient composition adapt Worker 435's shared
`RelativeCosocleAssembly` draft, revision 3. Worker 845 put the prototype
theorem into the exact closed form of the target, removed two unneeded
options and wrote this Markdown.

`Langlands.fineOppositeJacquetQuotientDetection` has exactly the type
`Langlands.FineOppositeJacquetQuotientDetectionStatement.{uF, uV, uW, uZ}`,
the published proposition in
`Langlands.Representation.Classification.FineOppositeJacquetQuotientDetectionStatement`.
The universes of the field (`uF`), the fine carrier (`uV`), the coarse target
(`uW`) and the ambient target (`uZ`) stay independent, and the theorem's level
parameters are in that order. The statement pair and every pair it imports
are unchanged.

## The two explicit premises

The target is an implication. Its first two hypotheses are
`Parabolic.StandardSecondAdjointnessClause.{uF, uV, uZ}` and
`Parabolic.RefinedSecondAdjointnessClause.{uF, uV, uW}`. The proof takes them
as the hypotheses `hstandard` and `hrefined` and uses only the Hom
equivalence family in each. The naturality parts are discarded. This module
does not prove either clause, and the theorem asserts its conclusion only
under them.

The Library now has a separate published proof of both clauses,
`Langlands.Parabolic.normalizedSecondAdjointness` in
`Parabolic.SecondAdjointnessProof`. This module neither imports nor uses it;
the premises stay part of the proved implication.

## Implemented proof

After introducing the two premises, `p`, the prime instance, `F` and `T`, the
proof installs `T.topology` and then introduces the rank `n`, `0 < n`, `B`,
`S`, the fine representation `ω` with its irreducibility and Levi-cuspidality
hypotheses, and the real vectors `v` and `t`.

The published `Langlands.fineTwistIrreducibleAdmissible`, from
`Classification.FineTwistRegularityProof`, applies to the same data. It proves
that `τ := RelativeJacquetMultiplicity.fineTwist T B S ω v t` is irreducible
and admissible. It also proves that the flattened real twist
`T.leviRealPowerTwist (B.flatten S) (fun k => -v k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ`
is Levi-cuspidal, so admissible. These give the inducing admissibility
hypotheses needed by the two clauses for every real `v` and `t`. No other
property of `ω`, `v` or `t` is used.

The two criteria then come from two private lemmas, followed by a common
last step.

### Inner criterion

`innerDetection` applies `hrefined` at `p`, `F`, `T`, the positive rank,
`B` and `S`. For admissible `τ` and the supplied admissible `π`, this gives a
complex-linear equivalence

`Hom(innerInduced T B S τ, π) ≃ Hom(τ, T.normalizedRefinedOppositeJacquet B S π)`.

Here `innerInduced T B S τ` is by definition
`T.normalizedRefinedInduced B S τ.ρ`. So the clause applies with no
transport.

### Ambient criterion

`ambientDetection` applies `hstandard` at the flattened shape `B.flatten S`.
Write `α` for the flattened real twist above, as a bundled representation.
For admissible `α` and the supplied admissible `J`, the clause gives

`Hom(fineAmbientInduced T B S ω v t, J) ≃ Hom(α, CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) J)`.

`RelativeRecovery.fineAmbientInduced T B S ω v t` is by definition the
normalized upper induction of `α` along `B.flatten S`. The published
`Langlands.Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uZ}`, from
`Parabolic.FlattenedOppositeJacquetComparisonProof`, supplies its second
component: a representation equivalence `φ` from the composed quotient
`T.normalizedComposedOppositeJacquet B S J.ρ`, pulled back along
`flattenedLeviEquiv F.Carrier B S`, to that flattened opposite Jacquet
module. The proof then composes two private linear equivalences:

1. `homPostcompEquiv`, postcomposition with `φ.symm`. It identifies the Hom
   above with the Hom from `α` into the pulled-back composed quotient.
2. `homChangeGroup`, change of group along
   `e := flattenedLeviEquiv F.Carrier B S`. It sends an intertwiner from `α`
   to `σ ∘ e` to the same linear map, viewed as an intertwiner from `α ∘ e⁻¹`
   to `σ`. Since `fineTwist T B S ω v t` is the pullback of `α` along
   `e.symm`, this is the Hom from `τ` into
   `T.normalizedComposedOppositeJacquet B S J.ρ`.

This target is the composed opposite Jacquet module of `J` itself. It is not
the Jacquet module of an induced representation.

### Common last step

`exists_nonzero_iff_of_equiv` uses that a linear equivalence and its inverse
send nonzero vectors to nonzero vectors. So each Hom equivalence above turns
a nonzero intertwiner on one side into one on the other.

`nonzero_iff_surjective` then uses irreducibility of the target. Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` makes a nonzero
intertwiner onto an irreducible representation surjective. Conversely, the
carrier of an irreducible representation is nontrivial, by
`IsSimpleModule.nontrivial` for its module over the group algebra. A
surjection onto it is therefore nonzero. Combining the two steps gives each
equivalence of the conclusion, and the theorem returns them as a conjunction.

## Constructions retained

All carriers and functors are the existing actual constructions:

* the fine source is the existing fine twist, with negative fine exponents and
  positive restricted coarse exponents, pulled back along the constructed
  `flattenedLeviEquiv`;
* both inductions are the existing normalized inductions, with positive-half
  upper modulus covariance;
* both opposite Jacquet modules are the existing coinvariant quotients, with
  inverse-half opposite modulus normalization.

The proof chooses Hom equivalences only inside its own argument. The
statement itself fixes no Hom equivalence, quotient map or substitute
representation.

## Scope and imports

The theorem is an internal algebraic consequence of the two explicit
premises and of published transport and regularity theorems. It is not
transcribed from the original literature; the literature provenance of the
assumed clauses (Casselman 2019, Chapter III) is recorded with
`Parabolic.SecondAdjointnessStatement`. The theorem does not supply
analytic arbitrary-tempered quotient reflection, occurrence continuation, an
equality or positivity of Hom dimensions, Jacquet semisimplicity, or an
identification of Hom spaces with Jordan–Hölder multiplicities. It does not
prove the parent J-specific comparison
`Langlands.GLRelativeCosocleHomComparisonStatement`. It assumes no support,
chamber, unitarity, finite-length or finite-dimensionality condition. The
carriers may be infinite dimensional.

The direct project imports are the target statement,
`Classification.FineTwistRegularityProof` and
`Parabolic.FlattenedOppositeJacquetComparisonProof`. Their transitive project
closure has 127 modules. It contains `Parabolic.SecondAdjointnessStatement`,
which only defines the two premises, but not `Parabolic.SecondAdjointnessProof`.

Lean reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.
