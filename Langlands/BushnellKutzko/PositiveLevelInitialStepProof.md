# The positive-level initial step of BK93 (8.1.5) (proof)

Module `Langlands.BushnellKutzko.PositiveLevelInitialStepProof`, namespace
`Langlands.BushnellKutzko`. It proves the Library proposition
`PositiveLevelInitialStepStatement.{uF, uπ, uρ}` of
`Langlands.BushnellKutzko.SplitTypeExistenceSteps`, with all three universes arbitrary:

- `positiveLevelInitialStep : PositiveLevelInitialStepStatement.{uF, uπ, uρ}`.

The proof adds no hypotheses. Its only axioms are `propext`, `Classical.choice` and
`Quot.sound`. The representation-theoretic input is in
[SmoothStratumContainment](SmoothStratumContainment.md).

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
proof of (8.1.5), printed p. 268 (PDF p. 280). The source proof runs as follows:

- `π` contains a fundamental stratum `[𝔄, n, n-1, b]` with `n ≥ 1`, as in Bushnell (1987),
  Theorem 2.
- If the stratum is split, one may take `gcd(n, e(𝔄)) = 1`, and then `π` contains a split type
  of level `(x, x)` with `x = n/e(𝔄)`.
- Otherwise the stratum is nonsplit, and by (2.3.4) one may assume it is simple.

The Lean proof follows this route. It takes the stratum at a minimal normalized level, and it
gets coprimality by passing to a coarser lattice chain, not by Kutzko's argument. In the nonsplit
case it shows directly that `ψ_c` is a simple character, as BK93 (3.2.1)–(3.2.2) and the end of
the paragraph on p. 268 indicate.

Notation as in [SplitTypeExistenceSteps](SplitTypeExistenceSteps.md): `N = n`, `π` is an
irreducible smooth complex representation of `GL_N(F)`, units of `End_F(F^N)` act through the
inverse of `Matrix.GeneralLinearGroup.toLin` (`toG` in the Lean file), and
`ψ_b = elementCharacter (traceCharacter ψF) b`.

## 1. Simple characters of terminal defining sequences

- `Stratum.terminalDefiningSequence S hS h` is the defining sequence of length one, `(S)`, of a
  simple stratum `S` whose critical exponent is `-S.n` or `⊥`. This is the case of BK93 (2.4.2)
  in which no further approximation is needed. Its `tail` is empty
  (`Stratum.terminalDefiningSequence_tail`).
- `Stratum.criticalExponent_eq_of_isSimple`. A simple stratum with `S.r = S.n - 1` has critical
  exponent `-S.n` or `⊥`. Simplicity gives `k₀ < -(S.n - 1)`. The lower bound `-S.n ≤ k₀` is
  `neg_n_le_criticalExponent` applied to the Library theorem `minimalCriticalExponent`.
- `mem_simpleCharacters_of_tail_eq_nil`. For the empty tail, membership of a character `θ` of
  `H^{m+1}(β, 𝔄)` in `C(𝔄, m, β)` (`simpleCharacters`) unfolds to two conditions. The first is
  that `θ` agrees with `ψ_β` on `H^{m+1}(β, 𝔄) ∩ U^{⌊n/2⌋+1}(𝔄)`. The second is
  `factorsThroughCentralizerDet β θ`: `E = F[β]` is a field, and the restriction of `θ` to
  `H^{m+1}(β, 𝔄) ∩ B_β^×` factors through the `E`-determinant. These are the two conditions of
  BK93 (3.2.1)(a)–(b), printed p. 98.
- `factorsThroughCentralizerDet_elementCharacterHom`. Let `S` be pure, `E = F[β]`, `n < 2k`, and
  `H ≤ U^k(𝔄)`. Then the character `ψ_β` of `H` (`elementCharacterHom`) factors through the
  `E`-determinant on `H ∩ B_β^×`, which is BK93 (3.2.1)(b).
  - Proof. By `factorsThroughCentralizerDet_iff`, it suffices to show `ψ_β(x) = 1` for each
    `x ∈ H ∩ B_β^×` with `det_E x = 1`.
  - Set up `E` as a local field with the relative lattice chain `C`, as in
    `SimpleCharacterCentralizerDeterminant`. Then `x ∈ C.unitFiltration k`
    (`mem_unitFiltration_restrictScalars_iff`).
  - `elementCharacter_eq_relativeDet_of_highDepth` gives
    `ψ_β(x) = ψF(tr_{E/F}(β (det_E x - 1)))`, which is `ψF(0) = 1`.

## 2. The split branch

`exists_containsType_diagonalPositiveSplitType`. Let `S = [𝔄, n, n-1, b]` be split with `n > 0`
and `gcd(n, e(𝔄)) = 1`. Let a vector `v ≠ 0` satisfy `π(u) v = ψ_b(u) v` for
`u ∈ U^n(𝔄)`. Then `π` contains a pair `(K, ρ)` in `GL_N(F)` whose transport to `Aut_F(F^N)` is
`IsDiagonalPositiveSplitType ψF (n/e(𝔄))`.

- `K` is the preimage of `U^n(𝔄)` under `toLin`.
- `ρ` is the character `ψ_b ∘ toLin` (`filtrationTraceCharacter`) acting by scalars on
  `ULift ℂ` in the universe `uρ` (`liftedCharacterRepresentation`).
- `ρ` is smooth. The preimage of `U^{n+1}(𝔄)` is open in `K`: it is the preimage of the open set
  `isOpen_unitFiltration` under the homeomorphism `generalLinearToLinContinuous`. On it `ψ_b` is
  trivial (`filtrationTraceCharacter_eq_one`).
- `z ↦ z · v` is a nonzero intertwiner from `ρ` to `π|K`, so `ContainsType π ρ` holds.
- The transport of `K` is `U^n(𝔄)` (`Subgroup.map_comap_eq_self_of_surjective`). The transported
  representation is isomorphic to `characterRepresentation` of `filtrationTraceCharacter` via
  `ULift.moduleEquiv`. The witness of `IsDiagonalPositiveSplitType` is `S` itself.

## 3. The nonsplit branch

`exists_containsSimpleCharacter_of_isNonsplit`. Let `S = [𝔄, n, n-1, b]` be nonsplit with
`n > 0`, and let `v ≠ 0` satisfy `π(u) v = ψ_b(u) v` for `u ∈ U^n(𝔄)`. Then
`ContainsSimpleCharacter ψF π T` for some stratum `T`.

- `PureApproximation.nonsplitRefinement` (BK93 (2.3.4)) gives a simple stratum
  `T = [𝔅, n', n'-1, c]` with `b + 𝔓^{1-n}(𝔄) ⊆ c + 𝔓^{1-n'}(𝔅)` and `n e(𝔅) = n' e(𝔄)`. In
  particular `n' > 0`, `b - c ∈ 𝔓^{1-n'}(𝔅)`, and `𝔓^{1-n}(𝔄) ⊆ 𝔓^{1-n'}(𝔅)`.
- Duality (`LatticeChain.endFiltration_one_sub_le`) gives `𝔓^{n'}(𝔅) ⊆ 𝔓^n(𝔄)`. Hence
  `U^{n'}(𝔅) ⊆ U^n(𝔄)` (`unitFiltration_le_of_endFiltration_le`).
- Take the terminal defining sequence of `T` (§1). Then `H^{n'}(c, 𝔅) = U^{n'}(𝔅)`
  (`simpleHGroup_eq_unitFiltration_at_high_index`).
- Let `θ` be `ψ_c` on this group (`elementCharacterHom`). By §1, `θ ∈ C(𝔅, n'-1, c)`.
  BK93 (3.2.2)(i) says the same: this set is `{ψ_c}`.
- On `U^{n'}(𝔅)`, `ψ_{b-c}` is trivial (`elementCharacter_eq_one_of_depth`, since
  `(1 - n') + n' ≥ 1`), so `ψ_b = ψ_c` there. The vector `v` therefore satisfies
  `π(u) v = θ(u) v`, which is `ContainsAutCharacter π θ`.

## 4. The main theorem

`positiveLevelInitialStep`. Let `π` be irreducible with no nonzero `U^1(𝔄)`-fixed vector for any
lattice chain.

1. `π` has a nonzero vector: as a module over the group algebra it is simple
   (`Representation.irreducible_iff_isSimpleModule_asModule`), hence nontrivial.
2. Write `N = n' + 1`. A nonzero vector `w` is fixed by an open subgroup `K0`
   (`π.isSmooth`). `K0` contains a principal congruence subgroup
   (`Conductor.exists_pos_principalLevelOpenSubgroup_subset`) of some level `k ≥ 1`, which
   contains `U^k(𝔄)` of the standard lattice chain (`unitSubgroup_stdChain_le`,
   `LatticeChain.standard`). So `w` is fixed by `U^{l+1}(𝔄)` with `l = k - 1`.
3. `exists_minimal_fixed_level` gives `𝓛`, `m ≥ 1` with `gcd(m, e(𝓛)) = 1`, and a vector fixed
   by `U^{m+1}(𝔄(𝓛))`, with `m / e(𝓛)` minimal.
4. `LatticeChain.exists_traceCharacter_eigenvector` gives `b ∈ 𝔓^{-m}(𝓛)` and `v ≠ 0` on which
   `U^m(𝔄(𝓛))` acts by `ψ_b`.
5. `LatticeChain.not_isNilpotent_add_of_minimal` shows that `S = [𝓛, m, m-1, b]` is fundamental.
6. If `S` is split, §2 gives the first alternative. Otherwise `S` is nonsplit
   (`Stratum.isNonsplit_of_not_isSplit`), and §3 gives the second.
