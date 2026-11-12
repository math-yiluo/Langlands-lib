# Proof of the relative root system

Author: Worker 23. Worker 15 pointed out the composition used here.

Module `Langlands.GroupScheme.Rational.RelativeRootSystemProof`.

## Result

`Langlands.GroupScheme.relativeRootSystem` has type exactly
`RelativeRootSystemStatement.{u}`, the published proposition of
`Langlands.GroupScheme.Rational.Statement`, at an arbitrary universe `u`. So for
every field `k : Type u`, every `G` with `IsConnectedReductive G` and every
`i : T.toGrp ⟶ G` with `IsMaximalSplitTorus i`, it proves
`HasRelativeRootSystem i`. Concretely, there are a finite type `J` and a root
pairing `P : RootPairing J ℚ V (Module.Dual ℚ V)` on `V = relativeRootSpan i`
with these properties:

- `P` is a root system and is crystallographic;
- its pairing is the evaluation pairing `Module.Dual.eval ℚ V`;
- its roots are exactly the images `1 ⊗ α` of the actual relative roots;
- the image of its Weyl group in `V ≃ₗ[ℚ] V` equals the range of
  `relativeWeylAction i`;
- the action of the actual quotient `N(k)/Z(k)` on `V`, `relativeWeylAction i`,
  is injective.

The root system may be nonreduced. Anisotropic groups, whose root set is empty,
are included. No splitness, quasi-splitness, perfectness or characteristic
hypothesis is added, and no root-system, reflection, Bruhat or faithfulness
premise is assumed.

## Implemented proof

The proof is one application:

`relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization`.

Both ingredients are published Library theorems. `rootRankOneFactorization`
(module `Rational.RootRankOneFactorizationProof`) proves
`RootRankOneFactorizationStatement.{u}` unconditionally.
`relativeRootSystemStatement_of_rootRankOneFactorizationStatement` (module
`Rational.RootSystemFromFactorPairs`) derives `RelativeRootSystemStatement.{u}`
from it. The mathematics behind each step is as follows.

### 1. Rank-one factorization

For every relative root `a` and every nonidentity rational point `u` of the root
subgroup `RelativeRoot.subgroup i a`, `rootRankOneFactorization` gives an
opposite factor pair. These are rational points `u′, u′′` of
`RelativeRoot.subgroup i (-a)` with `u′ * u * u′′ ∈ normalizerPoints i`. It also
gives uniqueness and further properties not needed here. Its proof applies
`rootRankOneFactorization_of_componentReductivity` (module
`Rational.RankOneParabolicCovering`) to the published unconditional
`RelativeRoot.kernelCentralizerComponentReductive`:

- `RelativeRoot.kernelCentralizerStructure` represents the centralizer of the
  full scheme-theoretic kernel of `a`, including a possibly nonsmooth kernel,
  by a smooth closed subgroup `C`.
  `kernelCentralizerComponentReductive` proves, after base change to an
  algebraic closure, that the identity component of `C` is connected
  reductive.
- Inside this component, the relative-rank-one covering theorem
  `RelativeRoot.exists_parabolic_mul_normalizer_mul_parabolic` writes every
  rational point as `p * n * r`. Here `p, r` lie in `P(k)` for a dynamic
  parabolic `P`, and `n` normalizes the torus. The proof forms the proper flag
  quotient `G/P`. It lifts rational points of `G/P` to rational points of `G`:
  for finite fields through the torsor-point theorem, and for infinite fields
  through the opposite cell and the published density of rational points of
  connected reductive groups. It takes the limit of a `𝔾ₘ`-orbit in the
  proper quotient, replaces the fixed limit coset by a rational normalizer
  point, and uses the Bruhat-cell limit theorem.
- From this covering, opposite factor pairs exist in the component and are
  transported back to `G`. `hasRankOneFactorization_of_hasOppositeFactorPairs`
  derives the full rank-one statement.

### 2. Integral reflections

From the existence part of step 1, `relativeRootSystemStatement_of_rootRankOneFactorizationStatement`
obtains `RelativeRoot.HasOppositeFactorPairs i`. Then
`RelativeRootReflectionData.ofOppositeFactorPairs` (module
`Rational.RootGeneratedWeylRepresentatives`) does the following for each actual
root `a`:

- it takes a nonidentity rational point `x` of the root subgroup, which exists
  unconditionally, and an opposite pair for it;
- the normalizing point `n_a = u′ * x * u′′` negates `a` and centralizes the
  full scheme-theoretic kernel of `a` on all tests;
- full-kernel centralization gives an actual integral cocharacter `a∨` with
  `latticePairing T a a∨ = 2` and
  `weylAction i n_a χ = χ - latticePairing T χ a∨ • a` for every character
  `χ`. This step is in `Rational.RootKernelReflection`, by the descent in
  `RootKernelDivisibility` and the coroot extraction in `IntegralCoroot`.

### 3. Generation and faithfulness

The pointwise theorem `RelativeRoot.hasRelativeRootSystem_of_hasOppositeFactorPairs`
continues as follows:

- It chooses a generic cocharacter `ν`, by `IsSplitTorus.exists_genericCocharacter`;
  this works also when there are no roots.
- It uses root finiteness, by `IsSplitTorus.finite_relativeRoots`.
- It proves that the positive-root stabilizer of `ν` in `N(k)/Z(k)` is trivial,
  by `hasTrivialPositiveRootStabilizer` in `Rational.PositiveRootStabilizerAveraging`.
  The stabilizer is finite, since the published relative Weyl group is finite.
  So the sum of the `ν`-translates under the stabilizer is a generic
  cocharacter fixed by the stabilizer. A fixed rational normalizer point lies
  in the dynamic centralizer of that cocharacter. By the published
  generic-centralizer theorem this is the centralizer of the whole torus, so
  the point lies in `Z(k)`.
- Finally `RelativeRootReflectionData.hasRelativeRootSystem_of_positive_stabilizer`
  (module `Rational.RelativeWeylChamberGeneration`, with the assembly in
  `Rational.RootReflectionAssembly`) does three things. It builds the
  evaluation root pairing from the integral reflections. It proves by chamber
  alignment that the reflection classes generate the whole quotient
  `N(k)/Z(k)`. It deduces faithfulness on `V` from the trivial stabilizer.
  This gives every clause of `HasRelativeRootSystem i`. For an empty root set,
  the stabilizer condition says that `N(k)/Z(k)` is trivial, and the
  construction still applies.

## The Milne errata and the source route

The statement follows Milne 25.16–25.17 and Borel–Tits 5.1–5.8. The official
Milne errata entry for p.549 says that the proofs of the root-system
assertion in Borel–Tits (1965), Borel (1991) and Springer (1998) are
incomplete. It directs readers to Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), C.2.15 (registered as
`conrad-gabber-prasad-2015-pseudo-reductive`). This proof does not cite or
follow those incomplete classical arguments. Its integrality step follows the
CGP route:

- the reflection representative of each root is a rational point normalizing
  the torus and centralizing the full, possibly nonsmooth, kernel of the root,
  as in the discussion after CGP Lemma C.2.14;
- the integral coroot and the reflection formula on the whole character
  lattice come from that full-kernel centralization, as in the proof of CGP
  Theorem C.2.15, Step 2.

Centralizing only the reduced kernel would not give integrality for divisible
roots. The existence of these representatives is proved by the rank-one
covering in step 1. That covering is an internal argument in the descended
relative-rank-one group: proper flag quotient, rational lifting and orbit
limits. It does not use a general rational Bruhat decomposition or a Tits
system. Generation and faithfulness come from the averaging argument and the
generic-centralizer theorem, not from a classical Bruhat argument.
