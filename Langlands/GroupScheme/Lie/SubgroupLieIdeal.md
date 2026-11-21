# Tangent Lie subalgebras of subgroups and Lie ideals of normal subgroups

This module equips the published tangent submodule `SubgroupFunctor.lie F A`
(`SubgroupTangent.lean`) with the actual tangent Lie bracket constructed in
`AffineBracket.lean`. It has two parts.

## Lie subalgebras of represented subgroups

Let `R` be a commutative ring, let `G` and `H` be group schemes over `Spec R`
with affine structure maps, and let `F` be a subgroup functor of `G` represented
by `i : H ⟶ G` (`F.IsRepresentedBy i`: the underlying morphism is a monomorphism
and the range of `i` is `F`). Let `A` be an `R`-algebra.

- `lie_lie_mem`: if `x` and `y` lie in `F.lie A`, so does their bracket `⁅x, y⁆`
  in `Additive (lieKernel G A)`.
- `lieSubalgebra F A i hrep`: the Lie subalgebra of the actual tangent Lie
  algebra of `G` over `A` whose underlying submodule is `F.lie A`
  (`lieSubalgebra_toSubmodule`, `mem_lieSubalgebra`). The carrier does not depend
  on the representing map `i`.
- `lieSubalgebra_eq_range`: this subalgebra is the range of the Lie algebra
  homomorphism `Lie.targetMapLieHom i A` induced by `i`.

The proof uses `lie_eq_range` to write `F.lie A` as the range of the tangent
map of `i`. It then uses the published compatibility of tangent maps with the
bracket, `Lie.targetMapLinear_lie` from `AffineBracketFunctoriality.lean`. No
field, smoothness or finiteness hypothesis is used.

## Lie ideals of normal subgroups over a field

Let `k` be a field. Let `G` and `H` be group schemes over `Spec k` whose
structure maps are affine and locally of finite type. Let `F` be a normal
subgroup functor of `G` (`F.IsNormal`: conjugation by every point of `G`
preserves the points of `F`) represented by `i : H ⟶ G`.

- `lie_lie_mem_of_isNormal`: for every `x` in the tangent Lie algebra
  `Additive (lieKernel G k)` of `G` and every `y ∈ F.lie k`, the bracket
  `⁅x, y⁆` lies in `F.lie k`.
- `lieIdeal F hF i hrep`: the corresponding Lie ideal of the tangent Lie algebra
  of `G` over `k`, with underlying submodule `F.lie k` (`mem_lieIdeal`,
  `lieIdeal_toSubmodule`).

The ring and Lie algebra structures on `Additive (lieKernel G k)` are local
aliases of the published instances `Lie.instAffineKernelLieRing` and
`Lie.instAffineKernelLieAlgebra`, specialised to the coefficient ring
`CommRingCat.of k`. Instance search does not find these instances through
`CommRingCat.of k` automatically. `AffineBracketAdjoint.lean` uses the same
local alias for the ring structure.

The proof follows the stabilizer argument of Milne's Proposition 10.31 in four
steps, each a separate declaration.

1. `adjoint_mem_lie_of_isNormal`: for every test algebra `A`, every `A`-point
   `g` of `G` and every `y ∈ F.lie A`, the actual adjoint action
   `adjoint G A g y` lies in `F.lie A`. Normality is applied to the constant
   `A[ε]`-point given by `g`. This step uses neither representability nor
   finiteness.
2. `linearFunctional_coordinates_mem_lie`: fix finite tangent coordinates
   `c : Lie.FiniteCoordinates G d`. For `z ∈ F.lie A` and a `k`-linear map
   `ℓ : A → k`, applying `ℓ` to the coordinates of `z` gives a vector in the
   coordinate image `W` of `F.lie k`. By `lie_eq_range`, `z` is the image of a
   tangent vector of `H` over `A`. `Lie.kernelScalarExtension H A` writes that
   tangent vector as a sum of elements `a ⊗ y` with `a ∈ A` and `y` a tangent
   vector of `H` over `k`; this is where `H` locally of finite type is used. For
   `a ⊗ y`, naturality of the coordinates gives coordinates `a` times the
   (scalar-extended) coordinates of the base tangent vector. Applying `ℓ`
   gives `ℓ a` times a vector of `W`.
3. `isStableSubspace_adjointRepresentation`: `W` is a stable subspace of the
   actual adjoint matrix representation `Lie.adjointRepresentation c`, in the
   all-test-algebra sense of `MatrixRepresentation.IsStableSubspace`. The adjoint
   matrix acts on coordinates as the adjoint action
   (`Lie.adjointRepresentation_affineAction`); steps 1 and 2 then apply.
4. `lie_lie_mem_of_isNormal` takes the coordinates `Lie.finiteCoordinates G`.
   By `IsStableSubspace.tangentMatrix_mulVec_mem` (from
   `Reductive/CharZeroSemisimplicity/TangentStability.lean`; this lemma does not
   assume characteristic zero), the tangent matrix of the adjoint representation
   at `x` preserves `W`. By `Lie.adjointDifferentialLieHom_apply_bracket`, that
   matrix sends the coordinates of `y` to the coordinates of `⁅x, y⁆`. The
   coordinate map is injective, so `⁅x, y⁆ ∈ F.lie k`.

## Source and scope

Milne, *Algebraic Groups* (2017 and 2022 corrected reprint), §10e, printed
p.196: the Lie algebra structure is natural in the group. Theorem 10.23 and
equation (62), 2022 printed p.193, show that `Lie(f)` preserves the bracket. For
an algebraic subgroup this makes the Lie algebra a Lie subalgebra. We did not
find a numbered statement in Milne that the Lie algebra of a normal algebraic
subgroup is an ideal. Milne uses this fact, for example in the proof of Lemma
23.68 (2017 printed p.506; 2022 printed p.508): "Then Lie(N) is a commutative
ideal". The ideal proof here
follows Proposition 10.31 (Lie algebra of a stabilizer, 2017 and 2022 printed
p.196) together with the identification of the differential of the adjoint
representation with the bracket (10.20–10.23, 2022 printed pp.192–193). The
2017 errata entry for p.506 changes only the cross-reference "p.475" to "p.476"
in the proof of Lemma 23.68. Neither errata snapshot (2017, 2 November 2026;
2022 reprint, 4 November 2026) has an entry for pp.192–196, and the 2022
snapshot has none for p.508.

Milne's algebraic groups from Chapter 10 on are affine of finite type over a
field. An algebraic subgroup of such a group is represented in the above sense
by its closed immersion, so the hypotheses cover Milne's setting. The subalgebra
part is proved more generally, over any commutative base ring and for any
subgroup functor represented by a monomorphism from an affine group scheme. The
ideal part is proved only over a field, with `G` and `H` affine and locally of
finite type. This module does not assert smoothness of `F` or `H`. It does not
treat the converse, that a connected subgroup whose Lie algebra is an ideal is
normal; Milne uses that converse in characteristic zero (2022 printed p.477). It
does not identify the quotient Lie algebra with the Lie algebra of a quotient
group.
