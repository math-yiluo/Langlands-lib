# Rational Corollary 1.10(b) from the rank-one and induced-Weyl targets

Author: Worker 3942.

This module proves that three separately published representation-theoretic
targets together imply the exact Corollary 1.10(b) target
`RationalCorollary110bStatement.{u, v}` of
[RationalCorollaryTargets](RationalCorollaryTargets.md). The three inputs are

- `RationalRankOneSelfAssociationStatement.{u, v}` (reducible maximal-Levi
  cuspidal induction forces self-association),
- `RationalRankOneJacquetModulesStatement.{u, v}` (the two constituents, their
  short exact sequence and their actual Jacquet modules), both from
  [RationalCorollaryTargets](RationalCorollaryTargets.md), and
- `RationalInducedK0WeylConjugacyStatement.{u, v}` from
  [RationalInducedWeylConjugacyTarget](RationalInducedWeylConjugacyTarget.md)
  (normalized induction is invariant under actual Weyl conjugation on exact K0).

The module proves an implication only. None of the three inputs is proved
here, so the Corollary 1.10(b) target itself is not proved by this module. The
separately named length-two target `RationalRankOneLengthTwoStatement` is not an
input: the Jacquet-modules target already produces the two constituents and
their short exact sequence.

## The proposition `RationalCorollary110bFromRankOneInputsStatement`

It is the closed proposition

```
RationalRankOneSelfAssociationStatement.{u, v} →
  RationalRankOneJacquetModulesStatement.{u, v} →
  RationalInducedK0WeylConjugacyStatement.{u, v} →
  RationalCorollary110bStatement.{u, v}
```

with independent universe parameters `u` and `v`. All four propositions are the
published ones, used unchanged and at the same universes, so the conclusion is
the whole unapplied Corollary 1.10(b) target. Its scope is the target's: every
nonarchimedean local field `k : Type u`, including positive characteristic,
every connected reductive group scheme over `Spec k`, split, quasisplit or
neither, with an actual maximal split torus, the canonical evaluation topology
`pointTopology`, the literal labels `SimpleRoot i ν`, the actual standard
parabolic, Levi and unipotent families, the actual normalized functors and
representation carriers in universe `max (u + 1) v`. No premise is added to
the target. For an empty simple-root type there is no maximal standard subset,
and the target's conclusion is vacuous; the proof needs no case distinction.

The proposition is derived (internal) rather than a statement from the
literature. It records the shape of the proof of Aubert 1995, Corollaire
1.10(b), printed p.2183: length two and the Jacquet modules of the two
constituents (cited there to Casselman §7.1), vanishing of the other proper
Jacquet modules, and the formula (1.2), which yields
`(-1)^|J| D_G(ρ±) = -ρ± + i_J(σ) = ρ∓`. The equality
`i_J(Ad(w)σ) = i_J(σ)` in K0, used implicitly there for the minus constituent,
is the third input.

## The proof `rationalCorollary110bFromRankOneInputs`

Introduce the three inputs and all binders of the Corollary 1.10(b) target.

1. **Induced Weyl conjugacy in class form.** The published
   `rationalInducedClassWeylConjugacy_of_inducedK0WeylConjugacy`
   ([InducedWeylClassComparison](InducedWeylClassComparison.md)) converts the
   K0-map input into the equality of classes of normalized inductions of a
   finite-length representation and its actual conjugate, for every normalizer
   point and Levi transport witness. Its premises `hStandard`, `hU`, `hP`,
   `hproj`, `hUc`, `hiFl`, `hrFl` are among the corollary's own premises.

2. **Coxeter data from the corollary's premises.** The two rank-one targets
   take, beyond the shared geometric premises, a finite relative Weyl group, the
   point normalizer and centralizer comparisons `hN`, `hZ`, a Coxeter matrix and
   an `ActualCoxeterSystem`, and the five premises `RootLengthComparison`,
   `PositiveSimpleReflectionComparison`, `actualLeviWeylIdentification`,
   `minimalityLengthCriterion` and `associatedSubsetLaws`. The corollary target
   has none of these, so the proof constructs all of them:
   - `rationalWeylComparison` ([RationalWeylComparisonProof](RationalWeylComparisonProof.md))
     gives `hN` and `hZ` for the given field, group and torus;
   - `rootSpanPointCoxeterData`
     ([RationalRootSpanCoxeterComparisons](RationalRootSpanCoxeterComparisons.md))
     builds, from `hG`, `hi`, `hRoots` and `hν`, the finite Weyl group, the
     matrix, the actual point Coxeter system, its `RootLengthComparison` and its
     `actualLeviWeylIdentification`; a `Fintype (Weyl i)` instance is obtained
     from the finiteness;
   - `positiveSimpleReflectionComparison_of_rootLength`
     ([RationalSuppliedCoxeterComparisons](RationalSuppliedCoxeterComparisons.md))
     gives `PositiveSimpleReflectionComparison` for the same system from its
     root-length comparison, `hRoots`, `hν` and splitness of the torus;
   - the intrinsic finite-Coxeter proofs `minimalityLengthCriterion_proof`
     ([RelativeWeylMinimalityProof](../../../Group/RelativeWeylMinimalityProof.md))
     and `associatedSubsetLaws_proof`
     ([RelativeWeylAssociatedSubsetProof](../../../Group/RelativeWeylAssociatedSubsetProof.md))
     give the last two premises.

   The two rank-one inputs are then applied to this data. The Coxeter system is
   the actual point system attached to the actual simple roots, so
   `longestRep` has the meaning fixed by the targets.

3. **Top term.** The published `alternatingTerm_univ_eq_id`
   ([RationalEndpoint](RationalEndpoint.md)) states that the full-subset
   induction-Jacquet term of the actual alternating operator is the identity on
   all of exact finite-length K0. It is evaluated at both constituents below.

4. **The datum.** Fix a maximal standard `J`, a finite-length irreducible `σ`
   of `levi i ν J` satisfying `IsCorollaryLeviCuspidal`, and reducibility of its
   actual normalized induction. Choose a normalizer point `n` whose class modulo
   the full centralizer is `longestRep c.system J` (quotient surjectivity). The
   second component of the self-association input, applied to `n`, gives the
   actual self-normalization witness
   `∀ x, x ∈ levi i ν J ↔ n * x * n⁻¹ ∈ levi i ν J`.

5. **Constituents.** The Jacquet-modules input at `n` and this witness gives
   finite-length `ρplus`, `ρminus`, the actual short exact sequence
   `HasTwoConstituents` (in either order, with no splitting assumed) and the
   `RankOneJacquetPattern`: `r_J ρplus ≅ σ`, `r_J ρminus ≅ Ad(n⁻¹)σ` with the
   pullback `x ↦ σ(n x n⁻¹)`, and zero Jacquet modules for both at every other
   proper standard subset. The sequence is the first required conclusion.

6. **Signed exchanges.** The published `constituentExchange_of_jacquet_pattern`
   ([CorollaryExchangeAssembly](CorollaryExchangeAssembly.md)), applied with the
   subgroup `torusPoints i`, the sequence, the pattern, the class form of
   induced Weyl conjugacy from step 1 and the two top-term equalities from step
   3, proves both `(-1)^|J| D_G[ρplus] = [ρminus]` and
   `(-1)^|J| D_G[ρminus] = [ρplus]` in the exact finite-length Grothendieck
   group, that is `ConstituentExchange`.

All terms of the alternating operator are accounted for: the top term by step
3, the term at `J` by the Jacquet isomorphisms and induced Weyl conjugacy, and
all other proper terms by the zero Jacquet modules.

## Dependencies and transitive uses

The direct dependencies are the four target propositions above and
`rationalInducedClassWeylConjugacy_of_inducedK0WeylConjugacy`,
`rationalWeylComparison`, `rootSpanPointCoxeterData`,
`positiveSimpleReflectionComparison_of_rootLength`,
`minimalityLengthCriterion_proof`, `associatedSubsetLaws_proof`,
`alternatingTerm_univ_eq_id` and `constituentExchange_of_jacquet_pattern`. The
paired explanations of these published declarations state that they use no
Langlands classification, character independence, geometric lemma, adjointness
or cuspidal-support theorem; this module adds none. Any such use needed to prove
the three inputs belongs to those separate proof obligations. Aubert's
Proposition 3.2 is not used. The only axioms are `propext`, `Classical.choice`
and `Quot.sound`.

The source is Aubert, Trans. Amer. Math. Soc. 347 (1995), Corollaire 1.10(b)
and its proof, printed p.2183 (registered `aubert-1995-duality`), read
directly. It motivates this derived assembly and is not used as proof evidence
for the three inputs.
