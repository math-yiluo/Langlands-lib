# Reduction of gamma stability to adjacent ranks

Module `Langlands.Representation.RankinSelberg.HighlyRamified.RankReduction`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It formalizes
Jacquet and Shalika 1985, §4.3 (printed page 327, "Reduction to the case
t = r − 1"). There, candidates `π_i` have rank `r` and the test `σ` has rank `t`.
If `t < r − 1`, the test `σ` is replaced by the generic constituent of an
induced representation `Ind(σ, η_1, …, η_(r−1−t))` with characters `η_j`. For
`t ≥ r`, the candidates are replaced by inductions
`Ind(π_i, μ_1, …, μ_(t+1−r))` with the same characters for both. Multiplicativity of gamma factors (Jacquet,
Piatetski-Shapiro and Shalika 1983, Theorem (3.1)) then splits off the factors
of the characters. Those factors are the same for both candidates. The case of
tests of rank one is used to compare them when the test is induced.

The Lean proof follows the same route with these changes:

- It adds one character `μ_z` at a time, so it is an induction on the rank.
- It does not take a generic constituent. It chooses `z` so that the induced
  representation itself is generic, in the Library's sense
  (`Whittaker.IsGeneric`, which includes irreducibility). Such a `z` exists
  because, for generic `A`, `A × μ_z` is generic for all but finitely many `z`.
  This is the hypothesis `PairInductionGenericity`. The present module does not
  prove it. It is proved as `pairInductionGenericity` in module
  `HighlyRamified.PairInductionGenericity`.
- It works with the uniqueness form `HighlyRamified.PairStability r t` (module
  `HighlyRamifiedGammaAssembly`). Here candidates have rank `r + 1` and the test
  has rank `t + 1`, so the adjacent case is `PairStability (n + 1) n`.

## Definitions

- `pairSizes n = ![n, 0]`: the exponents of the block sizes `(n + 1, 1)`, with
  `pairSizes_sum n : ∑ i, (pairSizes n i + 1) = n + 1 + 1`.
- `pairFamily F A B`: the two-block family with block `0` equal to the smooth
  representation `A` of `GL_(n+1)(F)` and block `1` equal to `B` of `GL_1(F)`.
- `pairInduced F A B`: the representation `A × B` of `GL_(n+2)(F)`. It is the
  Library's normalized induction `F.canonicalNormalizedProductInduced` from the
  standard upper parabolic of block shape `succBlockShape (pairSizes n) _`,
  in the canonical topology. It is the induction used by
  `gammaMultiplicativity`.
- `unramifiedRankOne F z`: the smooth character `x ↦ z ^ ord(x)` of `GL_1(F)`
  on `ULift ℂ`. It is `rankOneExtensionCharacter` of the continuous unramified
  character `F.canonicalTopologicalData.unramifiedCharacterContinuous z`.
- `PairInductionGenericity.{uF, uX}`: for every p-adic field `F` with its
  canonical topology, unitary additive character `ψ`, `n`, and smooth
  representation `A` of `GL_(n+1)(F)` on a space in universe `uX` that is
  generic for `ψ`, the set of `z : ℂˣ` for which `pairInduced F A (μ_z)` is not
  generic for `ψ` is finite. This is a hypothesis of the reduction. It is
  stated here and not proved here.

## Helper lemmas

- `infinite_units_complex`: `ℂˣ` is infinite, through the injective map
  `n ↦ n + 1`. So a finite exceptional set of `z` can be avoided.
- `finrank_ulift_complex`: `ULift ℂ` has dimension one over `ℂ`.
- `hasScalarCharacter_unramifiedRankOne F z`: the scalar `c` acts on `μ_z` by
  `μ_z(det(c · 1))`. Proof: by definition (`rfl`).
- `isGeneric_unramifiedRankOne F ψ z`: `μ_z` is generic. The proof of
  `isIrreducible_of_finrank_eq_one` (from
  `UnlinkedSegmentSocleProductIrreducibleProof`) is placed in the context:
  a one-dimensional representation is irreducible. `rankOneExtensionCharacter_isOfWhittakerType`
  gives admissibility and a Whittaker functional, and `Whittaker.isGeneric_rankOne`
  concludes.
- `gammaFactor_ne_zero_of_isGeneric`: if `π` and `σ` are generic, any gamma
  factor `G` of `(π, σ)` (`IsPadicSymmetricGammaFactor`, with the measure of a
  self-dual Haar measure `ν`) is nonzero. By `genericSymmetricGammaFactor_eq`,
  `G` is the value of a unit of `RationalFunctions`.

## The two induction steps

The section `Canonical` gives `F.Carrier` the local instance
`F.canonicalNormedField`, as in `HighlyRamifiedGammaAssembly`.

- `pairStability_of_succ_test` (test rank): from
  `PairStability.{uF, uV, max uF uX} r (t + 1)`,
  `PairStability.{uF, uV, uX} r 0` and `PairInductionGenericity.{uF, uX}`, it
  proves `PairStability.{uF, uV, uX} r t`. Proof: for a generic test `σ` of
  `GL_(t+1)(F)`, choose `z` with `σ' = σ × μ_z` generic. Its space lies in
  universe `max uF uX`. Take `A = max A₁ A₂` of the two bounds, for `σ'` and for
  `μ_z`. For `χ` of conductor exponent at least `A`, apply
  `gammaMultiplicativity` to `π_i ⊗ (χ ∘ det)` and the blocks `(σ, μ_z)`. This
  gives `H_i` with `H_i 0` a gamma factor of `(π_i ⊗ (χ ∘ det), σ)`, `H_i 1` one
  of `(π_i ⊗ (χ ∘ det), μ_z)` and `H_i 0 · H_i 1` one of
  `(π_i ⊗ (χ ∘ det), σ')`. The bound for `σ'` gives
  `H_1 0 · H_1 1 = H_2 0 · H_2 1`. The rank-one bound gives `H_1 1 = H_2 1`.
  This factor is nonzero (`gammaFactor_ne_zero_of_isGeneric`) and is cancelled.
  `IsPadicSymmetricGammaFactor.unique` identifies `H_i 0` with the given
  factors `G_i`.
- `pairStability_of_succ_candidate` (candidate rank): from
  `PairStability.{uF, max uF uX, uW} (r + 1) t` and
  `PairInductionGenericity.{uF, uX}`, it proves `PairStability.{uF, uX, uW} r t`.
  Proof: choose one `z` outside both finite exceptional sets, so that both
  `π_i × μ_z` are generic. They have the same central character
  `ω · (μ_z ∘ det ∘ scalar)` by `hasScalarCharacter_normalizedProductInduced`,
  with the block characters `![ω, μ_z ∘ det ∘ scalar]`. Take the bound `A` for
  the pair `π_i × μ_z` against `σ`. For `χ`, apply `gammaMultiplicativity` to
  `σ` and the twisted blocks `(π_i ⊗ (χ ∘ det), μ_z ⊗ (χ ∘ det))`.
  `normalizedProductDeterminantTwistEquiv` identifies the induction of the
  twisted blocks with `(π_i × μ_z) ⊗ (χ ∘ det)`
  (`IsPadicSymmetricGammaFactor.congr_equiv`). `Padic.isPadicSymmetricGammaFactor_comm`
  swaps the two arguments of each gamma factor. The bound gives
  `H_1 0 · H_1 1 = H_2 0 · H_2 1`. The factors `H_i 1` of
  `(σ, μ_z ⊗ (χ ∘ det))` are equal by uniqueness and nonzero, and are
  cancelled.

## Main theorems

- `pairStability_of_adjacent_of_rankOne`: suppose the adjacent case
  `∀ n, PairStability (n + 1) n` holds at universes `(uV, uW)`,
  `(max uF uV, uW)` and `(uV, max uF uW)`, and the rank-one case
  `∀ r, PairStability r 0` holds at `(uV, uW)` and `(uV, max uF uW)`. Suppose
  `PairInductionGenericity` holds at `uV`, `max uF uV`, `uW` and `max uF uW`.
  Then `PairStability.{uF, uV, uW} r t` holds for all `r, t`. Proof:
  - If `r ≤ t`: induction on `d` gives `PairStability.{uF, max uF uV, uW} r t`
    whenever `r + d = t + 1`. The base case is the adjacent case, and the step is
    `pairStability_of_succ_candidate` at `uX = max uF uV`. Lean identifies the
    universe levels `max uF (max uF uV)` and `max uF uV`. One more
    `pairStability_of_succ_candidate` at `uX = uV` concludes.
  - If `r = t + 1`: the adjacent case.
  - If `r > t + 1`: induction on `d` gives `PairStability.{uF, uV, max uF uW} r t`
    whenever `t + 1 + d = r`. The base case is the adjacent case, and the step is
    `pairStability_of_succ_test` at `uX = max uF uW`, which uses the rank-one
    case. One more `pairStability_of_succ_test` at `uX = uW` concludes.
- `highlyRamifiedGammaStability_of_adjacent_of_rankOne`: under the same
  hypotheses, `HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` holds, through
  `highlyRamifiedGammaStability_of_pairStability`.
