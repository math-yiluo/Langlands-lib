# Parabolic subgroups are self-normalizing on all tests: proof

Author: Worker 4037. The composite term below was first recorded, with a
development compilation, by Worker 15 of the previous project instance in the
public note `notes/group-schemes/composable-targets-2026-11-08.md`.

`Langlands.GroupScheme.parabolicSelfNormalizer` proves exactly the published
proposition `Langlands.GroupScheme.ParabolicSelfNormalizerStatement.{u}` of
`Langlands.GroupScheme.Rational.ParabolicNormalizerStatement`, at an arbitrary
universe `u` and with no added premise.

Write `S = Spec (CommRingCat.of k)`. Take any field `k : Type u`, any group
scheme `G` over `S` with `IsConnectedReductive G`, any group scheme `P` over
`S`, and any homomorphism `j : P ⟶ G` with `IsParabolicSubgroup j`. The
theorem gives

```lean
(SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j
```

This is an equality of subgroup functors on every test `T : Over S`, including
non-affine and nonreduced tests. The field may have any characteristic and need
not be perfect or algebraically closed. `G` need not be split, and no maximal
torus, Borel subgroup, root system or Bruhat decomposition is supplied. The
improper parabolic `P = G` and the Borel subgroups are included. The axiom
report lists only `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The proof applies one published conditional theorem to four published
unconditional theorems:

```lean
parabolicSelfNormalizerStatement_of_rational_descent borelConjugacy borelNormalizer
  parabolicDynamic dynamicConnected
```

The four inputs are proofs, not hypotheses:

- `borelConjugacy : BorelConjugacyStatement.{u}` (module
  `Absolute.BorelConjugacyProof`). Over an algebraically closed field, every
  smooth connected affine group has a Borel subgroup, and any two Borel
  embeddings are conjugate by a rational point.
- `borelNormalizer : BorelNormalizerStatement.{u}` (module
  `Absolute.BorelNormalizerProof`). Over an algebraically closed field, the
  normalizer in `G(k)` of the group of rational points of a Borel subgroup is
  that group.
- `parabolicDynamic : ParabolicDynamicStatement.{u}` (module
  `Absolute.ParabolicDynamicProof`). Over every field, a closed subgroup of a
  connected reductive group is parabolic exactly when its range is
  `Dynamic.parabolic χ` for some cocharacter `χ` defined over `k`.
- `dynamicConnected : DynamicConnectedStatement.{u}` (module
  `Dynamic.ConnectedProof`). For a smooth affine group over a field and a
  cocharacter, every representative of the dynamic unipotent is connected; if
  the group is connected, so is every representative of the dynamic parabolic
  and of the dynamic centralizer. The proof uses the parabolic case.

The conditional theorem `parabolicSelfNormalizerStatement_of_rational_descent`
(module `Rational.ParabolicNormalizerDescent`) uses these inputs as follows.

1. `parabolicDynamic` gives a cocharacter `χ` over `k` with
   `range j = Dynamic.parabolic χ`.
2. Base change to `AlgebraicClosure k` identifies the base-changed inclusion
   with the dynamic parabolic of the base-changed cocharacter. The base-changed
   ambient group is smooth, affine and connected. `dynamicConnected` makes the
   base-changed parabolic connected. The definition of `IsParabolicSubgroup j`
   supplies a Borel subgroup over the algebraic closure that factors through
   the base-changed inclusion.
3. Over the algebraic closure, `borelConjugacy` and `borelNormalizer` put every
   rational normalizer point in the parabolic. The published separation theorem
   `Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_normalizer` shows that the
   opposite dynamic unipotent meets the all-test normalizer only in the
   identity. The published `oppositeCellStatement` makes multiplication from
   the opposite unipotent times the parabolic an open immersion.
   `SubgroupFunctor.normalizer_eq_of_rational_points_and_open_cell` then proves
   equality of the full subgroup functors over the algebraic closure.
4. `Spec (AlgebraicClosure k) → Spec k` is surjective, flat and quasi-compact.
   `SubgroupFunctor.normalizer_eq_of_baseChange_eq` descends the all-test
   equality to the original field.

## Provenance

The result is Brian Conrad, *Reductive group schemes* (2014), Corollary 5.2.8
(pp. 155–156), specialized to a field base; the statement Markdown records the
translation of parabolicity. Like Conrad, the Lean proof reduces to the
algebraic closure and uses classical pointwise self-normalization there. In
place of his representability and Lie-algebra smoothness argument for the
normalizer, it uses the opposite open cell, the all-test separation of the
opposite unipotent and fpqc descent, from the published Library modules named
above.
