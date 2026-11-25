# Full-kernel comparisons from central actual root-datum maps

This internal construction is derived from the ordered root-product comparison,
the generic-cocharacter kernel factorization, and centrality of a split-torus
kernel annihilating every root. It introduces no external mathematical input.

Work over an arbitrary field with connected reductive affine source and target,
specified split maximal tori, finite reduced actual root data `P` and `Q`, and
a supplied root-datum isogeny `f : RootDatumIsogeny p Q P`. Its weight map is
assumed to be the actual pullback of a specified torus map `t`. If all factors
of `f` are one, the defining root equation becomes exact:
the pullback of `Q.root (f.indexEquiv.symm r)` is `P.root r`.

Supply source root parametrizations `u r : Ga → G` and assume their actual
composites with the ambient map represent the matching target root subgroups.
The ordered-product comparison then gives trivial full dynamic unipotent
kernels for every integral cocharacter. Choose a generic cocharacter of the
source torus and apply this at the cocharacter and its negative. The published
comparison of negation with the opposite cocharacter gives both opposite
unipotent kernel conditions.

For a finite ambient map to the affine target, these conditions construct
`kernelTorusFactorOfCentralRootDatumIsogeny`, an actual group-scheme map from
the entire ambient kernel to the source torus. Its composite with the torus
inclusion is exactly the ambient kernel inclusion.

If the specified torus square commutes, this factorization lands in the actual
kernel of the torus map. Exact root pullback shows that every source root
annihilates that restricted kernel. The split-torus kernel centrality theorem
and precomposition by the kernel comparison therefore prove centrality of
the full ambient kernel.

Finally, if the ambient map is an isogeny (finite, flat, and surjective), the
central kernel gives a central isogeny. The target is locally of finite type
over a field and hence locally Noetherian; finiteness of the map therefore
implies local finite presentation.

Assume also that the torus map is an isogeny and that, whenever `f` is central,
each source root has some parametrization with the stated matching target
representation. Choosing these parametrizations gives the reverse centrality
implication. The previously established forward implication for central
ambient isogenies proves
`IsCentralIsogeny q ↔ f.IsCentral`. Applying the self-centralizing maximal-torus
criterion and the actual character-lattice criterion then proves
`IsIso q ↔ f.IsCentral ∧ Function.Bijective f.weightMap`.
Bijectivity concerns the entire character lattice, including central torus
directions; centrality remains an explicit conjunct.

The root representatives and representation of their actual composites are
explicit hypotheses. This module does not derive them from factor-one geometry,
construct the root-datum isogeny, or prove the full comparison statement.
All kernels retain their possibly nonsmooth scheme structure, and the
unipotent argument applies to every test scheme.
