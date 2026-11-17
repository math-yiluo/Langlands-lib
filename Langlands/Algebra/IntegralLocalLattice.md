# Finite freeness from local integral lattices

Author: Worker 210.

This internal algebraic reduction is designed for the integral Hom groups in Task 7305. It is derived from the local-lattice step in the corrected proof of Milne, *Abelian Varieties* (1986 article, author revision 2 January 2022), Theorem 12.5, pp.21–22, registered as `milne-abelian-varieties-1986-author-2022`. The full registered errata snapshot was read and confirms that the proof correction is incorporated. The module uses a different algebraic finish: finite reduction modulo two bounds independent families, avoiding the source's prime-adic coefficient approximation. It asserts no geometric input for abelian schemes.

`FiniteFreeStatement` says that an abelian group `M` with an injective integer-linear map `f` into a rational vector space `V` is finite free if `M/2M` is finite and every inverse image of a finite-dimensional rational subspace of `V` is a finitely generated integer submodule. Both universes are arbitrary and independent. The integer module is the canonical one on an additive commutative group. `ModN M 2` is Mathlib's quotient by the range of multiplication by two.

The implemented proof first constructs `modTwoMap` from the mod-two quotient of the inverse image `N` of any rational subspace to `M/2M`. This map is injective: if `x` in `N` equals twice `y` in `M`, then the rational subspace contains `f(y)` because it contains twice `f(y)`. Thus `y` already lies in `N`.

For any finite family whose image in `V` is rationally independent, take the inverse image of its rational span. The local hypothesis makes this inverse image finite, and injection into a rational vector space makes it torsion-free. The structure theorem over the principal ideal domain of integers gives freeness. The independent family has at most its rank many elements, while the mod-two quotient has cardinality two raised to that rank and injects into `M/2M`. In particular, the family size is bounded by the fixed finite cardinality of `M/2M`.

Finally choose an independent subfamily of the image of `f` spanning its rational span. Every finite subfamily satisfies this bound, so the whole independent family is finite. Its span is finite-dimensional, and its inverse image is all of `M`. The local hypothesis therefore gives finite generation of `M`, and torsion-freeness gives freeness. This is a purely algebraic theorem; finite-dimensionality of the ambient space and a globally finitely generated lattice are conclusions or unnecessary assumptions, not supplied premises.
