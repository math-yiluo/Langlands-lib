# Compatible maximal subgroup tori and full restricted kernels

Author: Worker 1293.

This is a derived consumer construction for the actual torus and cocharacter
comparisons in the Levi cocenter root-model task. It applies more generally
to any closed subgroup `d : D → M`; it does not require `d` to be a derived
subgroup or establish any existence theorem.

Suppose `t : T → M` is a closed torus inclusion, `s : S → D` is a maximal
torus, and an actual commutative-group map `φ : S → T` makes
`φ ≫ t = s ≫ d`. If the full scheme intersection `T ×_M D` is supplied as a
torus, then the canonical lift of `S` to that intersection is an isomorphism.
Indeed the second intersection projection is a closed torus inclusion into
`D`, and the maximality predicate for `s` applies to this factorization.
`maximalSubgroupTorusIntersectionIso` implements this argument and records
compatibility with both original projections.

If `q : M → Q` is any supplied map to a commutative group whose full actual
kernel has the same all-test range as `d`, the published
`kernelCompositeIntersectionIso` identifies the full kernel of `t ≫ q`
with the same intersection. Composing the two comparisons gives
`maximalSubgroupTorusKernelIso`; its composite with the kernel inclusion is
exactly the supplied `φ`.

`maximalSubgroupTorusCocharacterKernelEquiv` applies actual cocharacter
transport and the published `cocharacterLattice.kernelEquiv`. Its underlying
map is `η ↦ η ≫ φ`. The final exactness lemma consequently characterizes
every integral cocharacter killed by `t ≫ q` as an actual cocharacter in
the image of `φ`.

The torus property of the full intersection, maximality of `s`, and the
full-kernel equality are explicit premises. These constructions do not prove
cocharacter surjectivity to `Q`, any coroot-span comparison, or any assertion
about simple connectedness or Galois descent.

The provenance is the universal property of the published actual
commutative subgroup intersection, the definition of maximal torus, and
the published full kernel/intersection and cocharacter-kernel comparisons.
No external source assertion is used.
