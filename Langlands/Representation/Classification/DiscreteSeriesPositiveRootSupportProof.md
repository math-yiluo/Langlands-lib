# Positive-root unitary cuspidal support of product-Levi discrete series

Author: Worker 510.

`Langlands.glDiscreteSeriesPositiveRootSupport` proves the unchanged
`Langlands.GLDiscreteSeriesPositiveRootSupportStatement.{uF,uV}` from
[`DiscreteSeriesPositiveRootSupportStatement`](DiscreteSeriesPositiveRootSupportStatement.md).
The field and original representation universes remain independent.
For the supplied topology, positive rank and ordered block shape `D`, its
only representation assumptions are irreducibility and the published
analytic `IsLeviSquareIntegrable T D σ`.

The proof constructs an actual refinement `R`, an irreducible cuspidal
unitarizable representation `ω` on the flattened Levi, a parameter `t`
satisfying the exact `IsPositiveRootParameter D R t`, and an actual
surjective intertwiner from `innerInduced T D R (fineTwist T D R ω t 0)`
to the original representation `σ`. It makes no properness assumption on
the refinement.

## Admissibility and the actual upper quotient

The private helper `squareIntegrable_admissible` installs the Borel
measurable structure on the quotient of `D.Levi F.Carrier` by its full
center. The published `glBlockCentralQuotientTopology` supplies an actual
Haar measure there. Specializing the all-Borel-Haar square-integrability
hypothesis to this measure gives admissibility of `σ`. Thus the
quantification is used with an existing measure rather than treated as
vacuous. Irreducibility also gives `Nontrivial σ.V`.

The published `CuspidalSupport.leviCuspidalQuotientTheorem` then supplies
`R`, an irreducible cuspidal datum `τ` on `(D.flatten R).Levi F.Carrier`,
and an actual surjective intertwiner

```
q : innerInduced T D R (fineTwist T D R τ 0 0) → σ.
```

Here arrows denote the representation intertwining maps used in Lean.
This is the proved upper quotient theorem, with its normalized
smooth-dual, induction-duality, bidual and universe transports already
established in
[`LeviCuspidalQuotientProof`](../CuspidalSupport/LeviCuspidalQuotientProof.md).
No embedding is relabeled as a quotient in this proof.

## Unitarization and cancellation on the same carrier

The published `leviCuspidalRealUnitarization` chooses a real vector `t`
such that

```
ω = Rep.of (T.leviRealPowerTwist (D.flatten R) t τ.ρ)
```

is unitarizable. Its conclusion is the published `IsUnitarizable`
predicate, namely existence of an invariant positive definite Hermitian
form. Twist invariance gives irreducibility and cuspidality of `ω`.

The private helper `fineTwist_unitarizing_cancel` proves equality of the
actual bundled representations

```
fineTwist T D R ω t 0 = fineTwist T D R τ 0 0.
```

It unfolds the fine twist, simplifies its coarse zero parameter, and
uses `leviRealPowerTwist_neg_cancel` and `leviRealPowerTwist_zero`.
The exponent `-t` cancels the unitarizing twist `+t` before the same
pullback along `flattenedLeviEquiv.symm`. Both twists use the original
carrier of `τ`. Rewriting this equality reuses `q` and its surjectivity;
the target remains the given `σ`.

## Scalar character, opposite occurrence and strict cone

`fineTwistIrreducibleAdmissible` gives admissibility of the fine inducing
representation. The published `unitaryFineTwistScalarCharacter`
constructs an open-kernel scalar character `χ` for its entire carrier
along the fixed flattened scalar map. Its real part is

```
x(k) = -((D.flatten R).size k : ℝ) * t(k).
```

Apply `refinedQuotientOppositeCharacter` to this character and the actual
surjection. Source and target admissibility and target nontriviality
have all been established. The result gives common-power occurrence of
the same `χ` in the actual normalized refined opposite Jacquet quotient
of `σ`, along the same scalar map.

The published `refinedOppositeSquareIntegrableCone` applies to this
occurrence and the original analytic square-integrability hypothesis.
For each original block it gives `IsPositiveRootCone` for the negative
real part, hence for the vector `size*t`. In particular it includes the
zero total in each original block and strict positivity of all proper
prefix sums. Its proved analytic and opposite/upper transports and
separate full-center tests are used through that theorem; no critical
exponent, central-direction condition or strict cone is assumed here.

Finally `positiveRootParameterCone` converts these blockwise scalar
cones to `IsPositiveRootParameter D R t`.
`D.flatten_size_flattenBlockEquiv R` identifies the flattened sizes with
the original ordered refinement sizes. This is the specified expansion
with a strictly positive coefficient on every adjacent scalar root and
reciprocal fine sizes. It preserves the separate size-weighted zero
sums. For an unrefined block, the proper prefix conditions are empty and
the zero total forces its parameter to be zero, agreeing with the empty
root sum.

## Normalizations, universes and provenance

The final fine source uses exponent `-t`, coarse parameter zero, the
constructed flattened-Levi pullback, positive-half-modulus covariance,
and the existing right-translation action. The inducing datum and
induced source have carrier universe `max uF uV`; the surjection targets
the original carrier in `uV`. The unitarizing twist changes neither that
inducing carrier nor the target.

This is a derived assembly of the named published Library results.
The original source motivation and normalization are recorded in the
paired statement Markdown: Silberger 1978, printed pp.96 and 99, and
Silberger 1979, section 2.4, printed pp.90–92, and Theorem 4.4.4,
printed pp.177–180. Worker 510 previously read these original passages
and their formula images and checked the retained errata locations.
The upper quotient and the modulo-full-center strict opposite cone are
the explicit derived comparisons used here; this file does not claim
that the printed opposite embedding alone supplies either comparison.

The proof imports the published quotient, unitarization, regularity,
scalar-character, opposite-occurrence, strict-cone and numerical-cone
proofs. Proposition definitions supply only their stated predicates.
It uses no tensor presentation, selected support, desired map as an
extra premise, downstream head, joint-support or classification
theorem, or unrestricted form of Silberger's Lemma 5.3. Its two private
helpers prove only admissibility and cancellation; the final theorem
has exactly the closed target type.
