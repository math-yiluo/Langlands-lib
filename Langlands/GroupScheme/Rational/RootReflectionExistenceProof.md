# Proof of intrinsic integral relative-root reflection existence

Author: Worker 3922.

`relativeRootReflectionExistence` proves the published proposition
`RelativeRootReflectionExistenceStatement.{u}` exactly, at arbitrary universe
`u`. It adds no hypothesis. Fix any field `k`, any connected reductive group
`G` over `k`, and any actual maximal split torus `i : T.toGrp → G`. The
theorem gives `RelativeRootReflectionData i`. For every actual relative root
`a`, this data consists of an actual integral cocharacter `a∨`, a rational
point `nₐ` of `normalizerPoints i`, the equality `latticePairing T a a∨ = 2`
and the reflection formula on the whole character lattice. Each `nₐ` lies in
`RelativeRoot.kernelCentralizer i a` at `Spec k`, so it centralizes the full
scheme-theoretic kernel of `a` on all tests. Divisible roots are included,
and so is the case with no roots.

## Implemented proof

The proof composes two theorems that are already published:

1. `rootRankOneFactorization : RootRankOneFactorizationStatement.{u}` (module
   `Rational.RootRankOneFactorizationProof`). This theorem is unconditional.
   It applies `rootRankOneFactorization_of_componentReductivity` to the
   unconditional `RelativeRoot.kernelCentralizerComponentReductive`, which
   proves that the identity component of every full-kernel centralizer is
   connected reductive. For each relative root `a` and each nonidentity
   rational point `x` of `RelativeRoot.subgroup i a`, it gives a unique
   opposite factor pair `(u′, u′′)` with `u′ * x * u′′` normalizing `i`.
2. `relativeRootReflectionExistence_of_rootRankOneFactorization` (module
   `Rational.RootGeneratedCentralizerReduction`). This theorem keeps only the
   existence part of that factorization, which is
   `RelativeRoot.HasOppositeFactorPairs i`. It then builds the data with
   `RelativeRootReflectionData.ofOppositeFactorPairs`. For each root, that
   construction picks a nonidentity rational root point `x`
   (`RelativeRoot.exists_rootPoint_actual`) and an opposite pair for it. It
   takes `nₐ = u′ * x * u′′`. The published lemmas then show that `nₐ` sends
   `a` to `-a` and lies in the full-kernel centralizer.
   `RelativeRootReflectionData.ofKernelCentralizingRepresentatives` turns such
   a representative into the integral coroot. It uses the integral divisibility
   of `weylAction i nₐ - 1` by `a`, which comes from full-kernel centralization
   (module `Rational.RootKernelDivisibility`). The kernel-centralizer clause of
   the target is the third component of
   `RelativeRoot.rootGeneratedRepresentative_spec`.

The proof uses no supplied root-system data, reflection data, root negation,
Bruhat decomposition or rank-one hypothesis. The rank-one input is the proved
theorem `rootRankOneFactorization`, not a premise.

## Relation to the source

The statement's source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Lemma C.2.14 with the discussion after it, and Theorem
C.2.15, Step 2. There the representative is a rational point of the connected
centralizer of the full kernel that inverts the rank-one quotient, and
`t ↦ t/rₐ(t)` factors through `a`. The Lean route gets its representative
differently, as the product of an opposite-root triple. This is the
Kaletha–Prasad 2.11.17 / CGP C.2.24 factorization, which the published
rank-one proof establishes inside the identity component of that same
full-kernel centralizer. The coroot extraction then follows Step 2: the
integral difference with `a` gives the cocharacter, the self-pairing and the
whole-lattice formula.

This proof does not assert generation of the rational normalizer quotient by
these representatives, faithfulness on the root span, or compatibility
between the choices for different roots.
