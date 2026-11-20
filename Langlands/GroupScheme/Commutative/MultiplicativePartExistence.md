# The multiplicative part of a commutative affine algebraic group

This internal derived unit proves the existence half of Milne 2017,
Theorem 16.13(a). It does not prove the characteristic clause. Let `k` be a
field and `G` a commutative group scheme over `Spec k` that is affine and
locally of finite type. The theorem
`CommutativeDecomposition.exists_multiplicativePart` produces:

- a closed subgroup `s : S ⟶ G` of multiplicative type that contains every
  closed subgroup of multiplicative type;
- an fppf quotient `q : G ⟶ Q` by the range of `s`, in the sense of
  `RelativeRoot.IsFppfQuotient`;
- a proof that `Q` is unipotent, affine and locally of finite type.

The subgroup `S` is the scheme-theoretic kernel of a homomorphism `f₀`. The
quotient `Q` is the image of `f₀` from the Library's `affineHomImage`.

## Route

The route follows Milne's description of `G_s` as the smallest kernel of a
homomorphism to a unipotent group. Minimality comes from a Noetherian
argument rather than from a dimension count.

1. **Minimal kernel** (`exists_minimal_unipotent_kernel`). Consider the
   homomorphisms `f : G ⟶ U` with `U` affine, locally of finite type and
   unipotent. Their kernels give coordinate ideals
   `BorelExistence.coordinateKernel (kernelι f)` in the Noetherian ring
   `Γ(G, ⊤)`. Choose `f₀` whose ideal is maximal. For any other such `g`,
   `lift f₀ g : G ⟶ U₀ ⊗ V` has a unipotent target
   (`SubgroupProductOrbit.isUnipotent_tensor`). Its kernel lies in
   `kernel f₀`, so its coordinate ideal is at least as large.
   Maximality makes the two ideals equal.
   `BorelExistence.isIso_of_coordinateKernel_eq` then makes the comparison
   map an isomorphism. Hence `kernel f₀ ≤ kernel g`.
2. **The kernel is of multiplicative type**
   (`isMultiplicativeType_kernel_of_minimal`). We use criterion (b) of the
   Library's `multiplicativeTypeCharacterization` (Milne 12.18): a
   commutative group with no nonzero homomorphism to `𝔾ₐ` is of
   multiplicative type. Let `g : kernel f₀ ⟶ 𝔾ₐ`, and let `N = kernel g`,
   embedded in `G` by `n`. Then `n` is a closed subgroup, normal because `G`
   is commutative. `affineNormalSubgroupQuotient` gives an affine fppf
   quotient `qN : G ⟶ QN`. To see that `QN` is unipotent, take a
   representation `ρ` of `QN` and pull it back to `G`:
   - on `kernel f₀` the pullback kills `N`, so it descends through the image
     `J ⊆ 𝔾ₐ` of `g` (`FppfHomDescent.hom`); `J` is unipotent as a closed
     subgroup of `𝔾ₐ` (`unipotentClosedSubgroup`, `VectorGroup.isUnipotent`),
     giving a nonzero fixed vector on `kernel f₀`;
   - `exists_fixedVector_of_kernel_of_quotient`, applied to the image
     quotient `q₀` of `f₀`, which is unipotent, gives a nonzero fixed vector
     of the pullback. This is a per-representation copy of the Library's
     `isUnipotent_of_kernel_of_quotient`;
   - `MatrixRepresentation.isFixedVector_restrict_iff` moves the vector back
     to `ρ`, since `qN` is flat and surjective, hence an epimorphism.

   Minimality of `f₀` now gives `kernel f₀ ≤ N`. Thus `kernelι g` has a
   section, and `g = 0`.
3. **Largest** (`range_le_kernel_of_isMultiplicativeType`). A homomorphism
   from a group of multiplicative type to an affine unipotent group is zero
   (`IsMultiplicativeType.hom_eq_zero_of_isUnipotent`, Milne 14.18). So every
   subgroup of multiplicative type lies in `kernel f₀`.
4. **Quotient**. `affineHomImage` factors `f₀` as an fppf quotient `q₀`
   with kernel `kernel f₀`, followed by a closed immersion into `U₀`. The
   image is unipotent by `unipotentClosedSubgroup`.

## Supporting lemmas

The module also contains small general lemmas:

- `isFixedVector_restrict_of_range_le`: fixed vectors of a restriction depend
  only on the range of the restricting map.
- `isFixedVector_restrict`: restriction preserves fixed vectors.
- `isAffineHom_of_isClosedSubgroup` and
  `locallyOfFiniteType_of_isClosedSubgroup`: closed subgroups inherit
  affineness and local finite type.
- `isAffineHom_tensor` and `locallyOfFiniteType_tensor`: binary products
  inherit the same two properties.
- Instances making `𝔾ₐ` affine and locally of finite type.
- Kernel lemmas: `comp_eq_zero_of_range_le`,
  `range_kernelι_le_of_comp_eq_zero`, `range_isNormal_of_comm`,
  `eq_zero_of_hom_eq_one`.

## Provenance

The statement is Milne, *Algebraic Groups* (2017), Theorem 16.13(a),
without the characteristic clause. The proof is internal. It is assembled
from published Library results: 12.18, 14.18, image factorization, quotients
by normal subgroups, fppf descent of homomorphisms, and the coordinate-ideal
Noetherian argument. Milne's own proof is not used.
