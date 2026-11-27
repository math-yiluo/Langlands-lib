# Dual lattices for an intersection with a subspace

Let `X` and `Y` be locally compact second countable topological abelian groups with compact open exhaustions, Borel σ-algebras and self-dual bicharacters `eX` and `eY`. Suppose `p : X → Y` is a continuous additive map and `i : Y → X` is an additive map such that `eY(p x,y) = eX(x,i y)`. For compact open subgroups `L` of `X` and `M` of `Y`, `ProjectedAnnihilatorStatement` identifies the annihilator in `Y` of `i⁻¹(L) ∩ M` with `p(L*) + M*`, where the stars are annihilators in the indicated groups.

The sum `p(L*) + M*` is compact as a sum of compact sets and open because it contains the open subgroup `M*`. A vector annihilates this sum exactly when it annihilates both summands. By adjointness and the double-annihilator identities for `L` and `M`, this means that its image under `i` lies in `L` and that the vector itself lies in `M`. Applying the double-annihilator identity in `Y` to the sum proves the result.

This is the dual-lattice computation in Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.6, proof of Lemma 9, printed p. 158. There `i` includes the fixed algebra and `p` projects onto it along the orthogonal complement, so the ambient annihilator formula becomes the stated sum upon projection.
