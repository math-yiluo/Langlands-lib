# The Lie algebras of a parabolic, its Levi subgroup and its unipotent radical as weight spaces: proof

Module `Langlands.GroupScheme.Rational.LeviCocharacterLieWeights`, namespace
`Langlands.GroupScheme`. The theorem

```lean
theorem leviCocharacterLieWeights : LeviCocharacterLieWeightsStatement.{u}
```

proves the statement of `Langlands.GroupScheme.Rational.LeviCocharacterLieWeightsStatement`.
Lean reports the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Helper

`SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear`: if a subgroup functor `F` of `G` is represented by `j : H ⟶ G`,
a vector `X` of `lieKernel G k` lies in the image of `Lie.targetMapLinear j k` exactly when its
dual-number point `X.val` lies in `F`. The points equivalence for the represented subgroup gives a lift of the dual-number point, and monicity identifies its reduction with the identity.

## Proof

1. The Library's `parabolicDynamic` (Milne, Theorem 25.1) gives a cocharacter `χ` of `G` with
   range of `q` equal to `Dynamic.parabolic χ`; since `q` is a closed immersion it is a
   monomorphism, so `q` represents `P_G(χ)`.
2. `IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic` replaces `χ` by a
   central cocharacter `ψ` of `M'` with `q` representing `P_G(ψ ≫ l' ≫ q)`.
3. `IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic` identifies
   `Dynamic.centralizer (ψ ≫ l' ≫ q)` with the range of `l' ≫ q`, and
   `Dynamic.range_comp_radical_eq_unipotent_of_reductive` identifies
   `Dynamic.unipotent (ψ ≫ l' ≫ q)` with the range of `iV ≫ q`. Both composites are
   monomorphisms (composites of closed immersions), so they represent these subgroup functors.
4. The Library's `dynamicRingLie` (Conrad–Gabber–Prasad, Proposition 2.1.8 (1)) characterizes the
   dual-number points of the centralizer, the parabolic and the unipotent subgroup among the
   vectors of `lieKernel G k` by the weight-zero space, the nonnegative weight spaces and the
   positive weight spaces. Combined with the helper this gives items 3, 5 and 4.
