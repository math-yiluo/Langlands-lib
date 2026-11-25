# Splitting a vector extension over an affine étale group

Module
`Langlands.GroupScheme.Trigonalizable.EtaleVectorExtension`.

`EtaleExtensionSplit.exists_section_of_vector_kernel` takes a smooth
surjective homomorphism `f : G ⟶ H` of affine group schemes over `k`
with vector kernel. It assumes that `H` is étale and that, for a separably
closed Galois extension `L/k` with `CharP L p` and `1 < p`, the order of
`H(L)` is prime to `p`. It produces a homomorphism of group schemes
`s : H ⟶ G` with `s ≫ f = 𝟙 H`.

1. The full vector kernel is smooth and split unipotent. The published
   `splitUnipotentAffineTorsorStatement`, used through
   `HomogeneousQuotient.fppf_section_of_split_unipotent_torsors`, gives a
   scheme section `s₀` over the affine base `H`. Postcomposition with `s₀`
   gives a set section of `G(L) → H(L)` that commutes with scalar
   conjugation.
2. `kernelPointsEquiv` identifies the kernel on `L`-points with the
   points of the full kernel scheme. The vector group coordinates identify
   these points with tuples in the additive group of the global sections
   of `Spec L`. This group is abelian and killed by `p`, since those global
   sections identify with `L`. Using the finite point type of `H` and
   the prime-to-`p` hypothesis, [factor-set averaging](FiniteGroupAveraging.md)
   gives a homomorphic section on points with the same equivariance. No
   linearity of the conjugation action on the vector kernel is assumed.
3. [Finite étale morphism descent](FiniteEtaleMorphisms.md) gives a
   `k`-scheme map from the equivariant point section. The section identity,
   preservation of the unit, and preservation of multiplication are
   checked on geometric points with sources `H`, `Spec k`, and
   `H ×ₖ H`, respectively. The last source is affine and étale by base
   change and composition. `Grp.homMk''` then gives the required
   homomorphism of group schemes.

This is the internal vector-kernel step of
[the étale splitting proof](EtaleExtensionSplitProof.md). The use of a
scheme section followed by averaging corresponds to the roles of
Lemmes 5.2.1 c) and 5.2.4 in SGA 3 XVII (locators and edition in the
[statement's source discussion](EtaleExtensionSplitStatement.md)). The
implementation uses vector kernels and Galois descent of a corrected
point map rather than the unrestricted cohomological argument.
