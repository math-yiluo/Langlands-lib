# Proof of standard-cocharacter existence and the dynamic comparison

Author: Worker 21.

`Langlands.GroupScheme.standardCocharacter` proves the published proposition
`Langlands.GroupScheme.StandardCocharacterStatement.{u}` from
[`StandardCocharacterStatement`](StandardCocharacterStatement.md) exactly, at
an arbitrary universe `u`. The theorem has no hypotheses. Fix any field
`k : Type u`, any connected reductive group scheme `G` over `Spec k`, any
maximal split torus inclusion `i : T.toGrp ⟶ G` and any generic cocharacter
`ν`. Write `Δ = simpleRelativeRoots i ν`. For every subset `J ⊆ Δ` the theorem
gives two things:

- a cocharacter `zeta` with `IsStandardCocharacter i ν J zeta`, that is, zero
  pairing on `J` and positive pairing on `Δ \ J`;
- for every such `zeta`, equality of `standardParabolic i ν J`,
  `standardLevi i ν J` and `standardUnipotent i ν J` with
  `Dynamic.parabolic`, `Dynamic.centralizer` and `Dynamic.unipotent` of
  `CommGroupScheme.groupHom zeta ≫ i`.

These are equalities of `SubgroupFunctor G`, so they hold on every test scheme.
The scope is the target's own: any characteristic, possibly imperfect fields,
nonsplit groups, possibly nonreduced relative roots, the empty set `J` and
every other subset of `Δ`, and an empty `Δ`.

## Implemented proof

The proof composes four published results. It adds no premise.

1. `rootRankOneFactorization : RootRankOneFactorizationStatement.{u}`
   (module `Rational.RootRankOneFactorizationProof`) is unconditional. It
   applies `rootRankOneFactorization_of_componentReductivity` to the
   unconditional `RelativeRoot.kernelCentralizerComponentReductive`. For every
   connected reductive group over any field, every maximal split torus and
   every relative root `a`, it gives `RelativeRoot.HasRankOneFactorization i`.
   In particular, each nonidentity rational point `u` of the root subgroup of
   `a` has an opposite factor pair `(u′, u′′)`, and `u′ * u * u′′` normalizes
   the torus.
2. `relativeRootReflectionExistence_of_rootRankOneFactorization` (module
   `Rational.RootGeneratedCentralizerReduction`) turns these opposite factor
   pairs into `RelativeRootReflectionExistenceStatement.{u}`. It builds the
   integral reflection data `RelativeRootReflectionData.ofOppositeFactorPairs`.
   For each relative root this gives an integral coroot with self-pairing two,
   and a rational normalizing representative that acts on the whole character
   lattice by the reflection formula. The representatives centralize the full
   scheme-theoretic character kernels.
3. `relativeRootSignsDetermineDynamic :
   RelativeRootSignsDetermineDynamicStatement.{u}` (module
   `Rational.RelativeRootSignsProof`) is unconditional. Two cocharacters with
   the same nonnegative, zero and positive signs on every relative root have
   the same dynamic parabolic, centralizer and unipotent subgroup functors.
4. `standardCocharacterStatement_of_reflections_of_signs` (module
   `Rational.ReflectionStandardCocharacter`) derives
   `StandardCocharacterStatement.{u}` from the two statements in steps 2 and 3.

Inside step 4, for fixed `k`, `G`, `i` and `ν`:

- **Existence.** The reflection data and the published finiteness of the
  relative roots give a finite crystallographic root pairing
  (`RelativeRootReflectionData.rootPairing`), whose roots are the rationalized
  relative roots. Each simple relative root lies in the indecomposable base of
  this pairing for the functional given by `ν`. Mathlib's
  `RootPairing.linearIndepOn_root_baseOf` then makes the rationalized simple
  roots linearly independent over `ℚ`.
  `exists_standardCocharacter_of_linearIndependent` then uses splitness of the
  torus to realize a positive integral multiple of the functional that is `0`
  on `J` and `1` on `Δ \ J`. This multiple is a cocharacter.
- **Comparison.** The reflection formula applied to a root itself gives
  negation closure of the relative roots. With genericity of `ν` and
  positive-root induction (`PositiveRootInduction`), this shows that any two
  standard cocharacters for the same `J` have the same signs on every relative
  root. By step 3 their three dynamic subgroup functors coincide.
  `StandardCocharacterDynamicComparison.standard_eq_dynamic` then identifies
  each choice-free intersection with the dynamic subgroup of any single
  standard cocharacter.

Affineness and smoothness of `G` come from `IsConnectedReductive`. The
monomorphism and splitness of the torus come from `IsMaximalSplitTorus`.

## Structural prerequisites actually used

Every structural input is a published, unconditional theorem:
`RelativeRoot.kernelCentralizerComponentReductive` (inside step 1),
`rootRankOneFactorization`, `relativeRootSignsDetermineDynamic`, and the
published finiteness of relative roots for a split torus in a smooth group.
No unproved proposition enters as a hypothesis. In particular, the proof
assumes none of `RelativeRootSystemStatement`, `RationalBruhatStatement`,
`ParabolicDynamicStatement`, `SmoothMaximalSplitTorusConjugacyStatement` or
`MinimalPseudoParabolicConjugacyStatement`. Step 4 does not need the
reflection representatives to generate the relative Weyl group or that group
to act faithfully. Lean reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The theorem is an internal composition of published Library results. The
target's Markdown cites Borel–Tits 1965, §4.2 (printed pp.85–86), §5.12
(p.99) and §3.13 (pp.78–80), and Renard 2026 V.4.2 (printed p.118). The
implemented route differs from those sources: it reaches root-system
independence through rank-one opposite factor pairs (Kaletha–Prasad 2.11.17,
Conrad–Gabber–Prasad C.2.24, as formalized in the cited modules), not through
the Borel–Tits root-system theorem.
