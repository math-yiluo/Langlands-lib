# Intrinsic positive roots lie in the nonnegative restricted-root cone

Fix a field `k`, an affine group scheme `G` locally of finite type over `k`, and
a verified parabolic root presentation `r` of the actual maps `p : P → G`,
`l : M → P` and `a : A → M`. Renard's cone `r.nonnegCone` is the set of
nonnegative real combinations of the restricted simple roots, inside the real
character space `ℝ ⊗ X*(A)`. This internal supporting module shows that the cone
contains every positive root of the split component.

## Restricted positive roots

`one_tmul_restrict_mem_nonnegCone` takes a positive ambient relative root `α`
of the presentation torus and proves `1 ⊗ (r.data.f ≫ α) ∈ r.nonnegCone`, where
`r.data.f` is the presentation's map from `A` to the torus. The proof is an
induction on positive roots (`positiveRelativeRoots_induction`):

- a simple root in the selected set `r.data.J` restricts to zero on `A`
  (`selectedRoot_restrict_eq_zero`), and zero lies in the cone;
- a simple root outside `r.data.J` restricts to a restricted simple root
  (`mem_restrictedRoots`), which lies in the cone by definition;
- restriction is additive, and the cone is closed under addition
  (`add_mem_nonnegCone`).

## Intrinsic positive roots

`one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots` assumes that the ambient
relative roots `relativeRoots r.data.i` are closed under negation. It proves that
`1 ⊗ β ∈ r.nonnegCone` for every intrinsic positive root `β` of `A`. The proof
lifts `β` to a positive ambient root (`exists_positiveRoot_restrict`, which uses
the negation hypothesis) and applies the first theorem.

## Provenance and scope

This is derived content for the proof of Renard VII.2.2
(`LeviInductionNormalizedTemperedStatement`). Renard compares exponents with the
cone through the set `W_{L,M}`; this route instead compares nonzero weights on
unipotent radicals, and it needs the fact proved here: every intrinsic positive
root of a split component lies in the cone of the presentation. The negation
hypothesis stays explicit. It holds when the ambient relative roots form a root
system, for example through `RelativeRootReflectionExistenceStatement`. The
module proves neither that hypothesis nor any converse inclusion.
