# Proof: reducedness of the roots of a split maximal torus

Authors: Worker 1422, reusing the rank-one argument of Worker 317 (see below).

`Langlands.GroupScheme.rootReducedness` proves exactly the published statement
`Langlands.GroupScheme.RootReducednessStatement.{u}`
(`Langlands/GroupScheme/Reductive/RootReducednessStatement.lean`) at an arbitrary
universe `u`. This is Milne, *Algebraic Groups* (2017), Theorem 21.11(b). Let `k` be any
field, `G` a connected reductive group scheme over `Spec k`, and `i : T ⟶ G` a split
maximal torus. Then any two roots `α, β ∈ roots i` that are linearly dependent over `ℤ`
in the character lattice satisfy `α = β ∨ α = -β`. The theorem has no hypotheses. Every
statement-valued input of the route is discharged by a published Library proof. The field and
its characteristic are arbitrary. The roots are the actual `roots i`, the nonzero characters
with a nonzero weight space in the Lie algebra. The target statement and every file it
imports are unchanged.

## Route

The final theorem is

```
rootReducedness_of_rankOne RootReducedness.rankOneRootReducedness dynamicCentralizerReductive
```

The published reduction `rootReducedness_of_rankOne`
(`Reductive/RootReducednessReduction`) derives `RootReducednessStatement` from two
inputs. The first is `RankOneRootReducednessStatement`: the case where any two roots
are `ℤ`-dependent. The second is `DynamicCentralizerReductiveStatement`. It works by
passing to the dynamic centralizer of a generic cocharacter in the kernel of `α`, which
plays the role of Milne's `G_α = C_G(T_α)`. The second input is the published theorem
`dynamicCentralizerReductive` (`Dynamic/CentralizerReductiveProof`). This module proves
the first input as `RootReducedness.rankOneRootReducedness`, in three steps.

### 1. Negation over an algebraically closed field

`RootReducedness.neg_mem_roots_of_rankOne_algClosed`: let `k` be algebraically closed,
`G` connected reductive with split maximal torus `i`, and suppose any two roots are
`ℤ`-dependent. Then `α ∈ roots i` implies `-α ∈ roots i`. The proof combines published
results only:

* `exists_proper_isBorelPair_of_relativeRoot` (`Absolute/RootedProperBorel`) gives a
  Borel subgroup `b : B ⟶ G` containing the torus through `t : T ⟶ B` with
  `t ≫ b = i`, because `G` has a root.
* `solvableMaximalTorusConjugacy` (`Rational/SolvableMaximalTorusConjugacyProof`)
  makes the maximal tori of the solvable group `B` conjugate.
* `IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint`
  (`Absolute/PrescribedBorelQuotient`) gives a proper quotient `G → G/B` with its fibre
  description. Its input is the published proof `solvableProperFixedPoint`.
* `nonidentityNormalizerOfRootedSolvableQuotient`
  (`Dynamic/RootedSolvableQuotientNormalizerProof`) produces a rational point `n` of
  the normalizer of `i` whose class in the relative Weyl group `N(k)/Z(k)` is not the
  identity.
* `IsConnectedReductive.weylAction_eq_neg_of_rankOne`
  (`Rational/RankOneCocharacterSymmetrization`) shows that such a class acts on every
  root by `α ↦ -α` when all roots are pairwise dependent.
* `weylAction_mapsTo_relativeRoots` (`Rational/RelativeRoots`) shows that the Weyl action
  of `n` maps roots to roots. Hence `-α = weylAction i n α` is a root.

This matches the semisimple-rank-one argument in the proof of Milne, Theorem 20.16,
(a)⇒(b) (printed p. 412, PDF p. 428). There the Weyl group acts faithfully, and the
only nontrivial automorphism of the rank-one part is inversion.

### 2. Negation over an arbitrary field

`RootReducedness.neg_mem_roots_of_rankOne` has the same statement over any field `k`.
Base change along `toAlgebraicClosure k` reduces it to step 1. The base change setup is
the same as in the published `rankOnePositiveRootUniqueness_of_algClosed`
(`Reductive/RankOnePositiveRootBaseChange`):

* `IsConnectedReductive.baseChange_toAlgebraicClosure`: the base-changed group is
  connected reductive.
* `maximalTorusBaseChange` (`Torus/MaximalBaseChangeProof`): the base-changed torus is
  maximal.
* `IsSplitTorus.baseChange`: the base-changed torus is split.
* `roots_pairwise_dependent_baseChange_iff`: pairwise dependence of the roots is
  preserved.
* `mem_roots_baseChange_iff` (`Torus/RootSupportBaseChange`): the pullback of a
  character is a root after base change exactly when the character is a root before it.
  This is applied to `α` and to `-α`. The pullback is additive (`map_neg`), so it sends
  `-α` to the negative of the pullback of `α`.

### 3. The rank-one case

`RootReducedness.rankOneRootReducedness : RankOneRootReducednessStatement.{u}`. Let
`α, β` be roots. Choose `ν = hT.positiveCocharacter hα.1` with `⟨α, ν⟩ > 0`. Since
`β ≠ 0` is `ℤ`-dependent with `α`, the pairing `⟨β, ν⟩` is nonzero
(`IsSplitTorus.latticePairing_ne_zero_of_not_linearIndependent`). Both of these come
from `Reductive/RankOneRootReducednessAssembly`. There are two cases:

* if `⟨β, ν⟩ > 0`, uniqueness of the root positive on `ν` gives `α = β`;
* if `⟨β, ν⟩ < 0`, then `-β` is a root by step 2 and `⟨-β, ν⟩ > 0`, so uniqueness
  gives `α = -β`.

Uniqueness here is `RankOnePositiveRootUniquenessStatement`. It is obtained inside the
proof as

```
rankOnePositiveRootUniqueness_of_projectiveBorelInputs
  (algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
    solvableTorusQuotient)
```

These are the published theorems in `Reductive/RankOneProjectiveBorelAssembly`,
`Absolute/MaximalTorusCentralizerFromQuotient`, `Dynamic/CentralizerReductiveProof` and
`Absolute/SolvableTorusQuotientProof`. The case split is Worker 317's proof of the
published conditional theorem `rankOneRootReducedness_of_negation_of_positiveRootUniqueness`,
reused unchanged except for one step. That theorem takes the general
`RelativeRootNegationStatement` as a premise. Its proof is not in the Library, so here
the negation step uses the rank-one result of step 2 instead.

## Provenance

This module is an internal composition of published Library theorems. The paired target
statement records the source (Milne, Theorem 21.11(b)). The implemented route does not
follow Milne's proof, which uses the homomorphism `SL₂ → G_α` of 20.32. It instead uses:

* the published dynamic-centralizer reduction;
* the Weyl-group negation above;
* the published projective Borel argument for uniqueness of the positive root.

The negation step goes through rank-one Weyl classes. It does not use any result that depends
on `RootDatumExistenceStatement`, which itself depends on this target. `rootReducedness`
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
