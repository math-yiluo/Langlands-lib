# Proof: subgroups containing a Borel subgroup are connected and self-normalizing

Worker 3566.

This module proves
[`BorelContainingSubgroupSelfNormalizerStatement`](BorelContainingSubgroupSelfNormalizerStatement.md)
(Milne, Theorem 17.48 and Corollary 17.49, over any field) as

```lean
theorem borelContainingSubgroupSelfNormalizer :
    BorelContainingSubgroupSelfNormalizerStatement.{u}
```

The statement module is imported unchanged, and the universe parameter `u` is preserved. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

All four are in namespace `Langlands.GroupScheme`. The first is in the nested namespace
`SubgroupFunctor`.

- `SubgroupFunctor.normalizer_range_le_comap_normalizer_of_fpqc_square`. Let `S` be a scheme,
  and let `i : P ⟶ G`, `q : G ⟶ Q`, `p : P ⟶ I`, `j : I ⟶ Q` be morphisms of group schemes
  over `S`. Suppose `i ≫ q = p ≫ j`, the underlying morphism of schemes of `p` is flat,
  surjective and quasi-compact, and the underlying morphism of `j` in `Over S` is a
  monomorphism. Then
  `(range i).normalizer ≤ ((range j).normalizer).comap q`. In words: a point of `G` that
  normalizes `range i` maps under `q` to a point of `Q` that normalizes `range j`, on every
  test scheme.
- `normalizer_eq_of_isParabolicSubgroup_of_isAlgClosed`. Let `k` be an algebraically closed
  field, `G` a smooth, affine, connected group scheme over `Spec k`, and `i : P ⟶ G` with
  `IsParabolicSubgroup i`. Then `(range i).normalizer = range i`. `G` is not assumed reductive.
- `isParabolicSubgroup_of_geometricBorel_factor`. Let `k` be a field. If `i : P ⟶ G` is a
  closed subgroup, `P` is smooth, `j : B ⟶ G` is a geometric Borel subgroup, and
  `f : B ⟶ P` satisfies `f ≫ i = j`, then `IsParabolicSubgroup i`.
- `borelContainingSubgroupSelfNormalizer`: the target statement.

## Proof

Let `k`, `G`, `P`, `B`, `i`, `j`, `f` be as in the statement.

**Step 1: `P` is parabolic.** `IsParabolicSubgroup i`
([`Absolute.Borel`](Borel.md)) requires a closed subgroup `i`, a smooth `P`, and a Borel
subgroup of `G_{k̄}` that factors through the base change `i_{k̄}`, where `k̄` is
`AlgebraicClosure k`. Take the base change `j_{k̄}`. It is Borel by the second component of
`IsGeometricBorelSubgroup j`. Since base change is a functor, `f_{k̄} ≫ i_{k̄} = j_{k̄}`. This
is `isParabolicSubgroup_of_geometricBorel_factor`.

**Step 2: connectedness.** `IsParabolicSubgroup.connectedSpace`
([`Rational.ParabolicConnectedConjugacy`](../Rational/ParabolicConnectedConjugacy.md)) gives
`ConnectedSpace P.X.left` for a parabolic subgroup of a smooth, affine, connected group.

**Step 3: reduction to `k̄`.** Let `b : Spec k̄ ⟶ Spec k` be `toAlgebraicClosure k`. Over
`k̄`:

- `G_{k̄}` is smooth and affine, because its structure morphism is a base change of
  `G.X.hom`.
- `G_{k̄}` is connected, by `connectedSpace_baseChange_of_smooth_affine`
  ([`GeometricConnectedness`](../GeometricConnectedness.md)).
- `i_{k̄}` is parabolic, by `IsParabolicSubgroup.baseChange_toAlgebraicClosure`
  ([`Absolute.AlgebraicClosureBaseChange`](AlgebraicClosureBaseChange.md)).

The algebraically closed case below therefore gives
`(range i_{k̄}).normalizer = range i_{k̄}`. The morphism `b` is surjective, flat and
quasi-compact by `fieldExtension_fpqc` ([`BaseChangeReflection`](../BaseChangeReflection.md)).
`i` is a monomorphism in `Over (Spec k)` because it is a closed subgroup. Rewrite
`range i_{k̄}` as `(range i).baseChange b` with `SubgroupFunctor.range_baseChangeHom`
([`SubgroupBaseChange`](../SubgroupBaseChange.md)). Then
`SubgroupFunctor.normalizer_eq_of_baseChange_eq`
([`SubgroupFunctor.NormalizerBaseChange`](../SubgroupFunctor/NormalizerBaseChange.md)) gives
`(range i).normalizer = range i`.

**Step 4: the algebraically closed case**
(`normalizer_eq_of_isParabolicSubgroup_of_isAlgClosed`). Let `k` be algebraically closed and
`i : P ⟶ G` parabolic.

1. `unipotentRadicalExistence` ([`Reductive.UnipotentRadicalExistenceProof`](../Reductive/UnipotentRadicalExistenceProof.md))
   gives a unipotent radical `r : U ⟶ G`. `unipotentRadicalQuotient`
   ([`Reductive.UnipotentRadicalQuotientProof`](../Reductive/UnipotentRadicalQuotientProof.md))
   gives `q : G ⟶ Q` that is an fppf quotient by `range r`, with `Q` pseudo-reductive.
2. Over an algebraically closed field `Q` is connected reductive, by
   `IsPseudoReductive.isConnectedReductive_of_isAlgClosed`
   ([`Reductive.AlgebraicallyClosedPseudoReductive`](../Reductive/AlgebraicallyClosedPseudoReductive.md)).
   In particular `Q` is affine.
3. `U` is smooth, connected, unipotent and a closed subgroup, because `r` is a unipotent radical.
   So `HasSmoothConnectedUnipotentKernel.of_representative`
   ([`Reductive.UnipotentKernelQuotient`](../Reductive/UnipotentKernelQuotient.md)) shows that
   the kernel of `q` is smooth, connected and unipotent.
4. The first part of `unipotentQuotientParabolicCorrespondence`
   ([`Absolute.UnipotentQuotientParabolics`](UnipotentQuotientParabolics.md)) gives a parabolic
   subgroup `j : I ⟶ Q` and a morphism `p : P ⟶ I` with these properties: `i ≫ q = p ≫ j`;
   `p` is flat, surjective and quasi-compact; and `(range j).comap q = range i`.
5. `parabolicSelfNormalizer`
   ([`Rational.ParabolicNormalizerProof`](../Rational/ParabolicNormalizerProof.md)) applies to
   the connected reductive group `Q` and gives `(range j).normalizer = range j`.
6. `j` is a monomorphism because it is a closed subgroup. The square lemma below then gives

   ```text
   (range i).normalizer ≤ ((range j).normalizer).comap q
                        = (range j).comap q
                        = range i.
   ```

   The reverse inclusion is `SubgroupFunctor.le_normalizer`
   ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)).

**Step 5: the square lemma**
(`SubgroupFunctor.normalizer_range_le_comap_normalizer_of_fpqc_square`). This proof is modeled
on `isNormal_range_of_fpqc_square`
([`SubgroupFunctor.QuotientNormality`](../SubgroupFunctor/QuotientNormality.md)).

Let `g` be a point of `G` over `U` that normalizes `range i`. Let `a : V ⟶ U` and `y : V ⟶ I`
be given. Write `g' = a ≫ g ≫ q`. We must show that the conjugates `g' (y ≫ j) g'⁻¹` and
`g'⁻¹ (y ≫ j) g'` lie in `range j`.

`p` is flat, surjective and quasi-compact, and `j` is a monomorphism, so
`SubgroupFunctor.mem_range_of_local_quotient_lift` (same module) applies. It suffices to treat
every `b : W ⟶ V` and `z : W ⟶ P` with `b ≫ y = z ≫ p`.

1. `z ≫ i` lies in `range i`, so the hypothesis on `g` (with base change `b ≫ a`) gives `w`
   with `w ≫ i` equal to the corresponding conjugate of `z ≫ i`.
2. Then `w ≫ p` is the required preimage. Indeed,
   `(w ≫ p) ≫ j = (w ≫ i) ≫ q`, and `q` is a group homomorphism, so this equals `b` composed
   with the conjugate of `y ≫ j` by `g'`.
3. The computation uses `MonObj.mul_comp`, `MonObj.comp_mul`, `GrpObj.inv_comp`,
   `GrpObj.comp_inv`, the square `i ≫ q = p ≫ j` and `b ≫ y = z ≫ p`.

The two conjugation directions are handled by the same argument.

## Relation to the source

Milne's proof of Corollary 17.49 (p.367) first reduces to `k` algebraically closed. It then
uses that `P` contains a Cartan subgroup, so `N_G(P)` is smooth (Proposition 17.47), and
concludes with conjugacy of Borel subgroups in `P°` and Theorem 17.48. The Lean proof takes a
different route for the algebraically closed case. It does not use Proposition 17.47, Cartan
subgroups or Lie algebras. Instead it passes to the reductive quotient `G/R_u(G)`, where the
Library already has the self-normalizing property of parabolic subgroups
(`parabolicSelfNormalizer`). It then pulls that equality back along `q` with the
parabolic correspondence and the square lemma. The descent from `k̄` to `k` is the same in
both proofs.
