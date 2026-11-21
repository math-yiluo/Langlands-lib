# Scalar extension of tangent Lie algebras of subgroups over a field

This module combines the tangent submodule of a subgroup functor
(`SubgroupTangent.lean`, `SubgroupLieIdeal.lean`) with the scalar-extension
isomorphism of tangent Lie algebras (`ScalarExtension.lean`,
`ScalarExtensionBracket.lean`).

**A linear-algebra lemma.** `Lie.range_baseChange` states that, for an
`R`-linear map `f : M → N` and an `R`-algebra `A`, the range of
`f.baseChange A : A ⊗[R] M → A ⊗[R] N` is `(range f).baseChange A`. Mathlib's
`Submodule.baseChange p` is the range of the base change of the inclusion of
`p`. Both inclusions are proved by tensor induction.

**Tangent submodules commute with scalar extension.** Let `k` be a field. Let
`G` and `H` be group schemes over `Spec k` whose structure maps are affine and
locally of finite type. Let `F` be a subgroup functor of `G` represented by
`i : H ⟶ G`, and let `A` be any commutative `k`-algebra.

- `lie_eq_map_baseChange`: `F.lie A` is the image of `(F.lie k).baseChange A`
  under `kernelScalarExtension G A`.

Proof: by `lie_eq_range`, `F.lie A` is the range of the tangent map of `i` over
`A`, and `F.lie k` is its range over `k`. The scalar-extension isomorphism for
`H` is surjective. The published `targetMapLinear_kernelScalarExtension` states
that the tangent map over `A`, composed with `kernelScalarExtension H A`, equals
`kernelScalarExtension G A` composed with the base change of the tangent map over
`k`. `Lie.range_baseChange` rewrites the range of that base change as
`(F.lie k).baseChange A`.

**Lie ideals over every coefficient algebra.** Suppose in addition that `F` is
normal.

- `lie_lie_mem_of_isNormal_coefficients`: for every `x` in the actual tangent
  Lie algebra `Additive (lieKernel G A)` and every `y ∈ F.lie A`, the bracket
  `⁅x, y⁆` lies in `F.lie A`.
- `coefficientLieIdeal F A hF i hrep`: the corresponding Lie ideal over `A`,
  with carrier `F.lie A` (`mem_coefficientLieIdeal`).

Proof: transport `x` and `y` along `kernelScalarExtension G A`, which preserves
the bracket (`kernelScalarExtension_lie`). Then `y` comes from
`(F.lie k).baseChange A`. Tensor induction reduces the claim to pure tensors
`a ⊗ x'` and `b ⊗ y'` with `y' ∈ F.lie k`. Their extended-scalars bracket is
`(a * b) ⊗ ⁅x', y'⁆`. By `lie_lie_mem_of_isNormal`, the field case proved in
`SubgroupLieIdeal.lean`, `⁅x', y'⁆ ∈ F.lie k`.

As in `ScalarExtensionBracket.lean`, the published Lie instances
`Lie.instAffineKernelLieRing` and `Lie.instAffineKernelLieAlgebra` are restated
as local instances for `k`-algebras viewed over `CommRingCat.of k`, because
instance search does not find them. They add no new structure.

## Source and scope

Milne, *Algebraic Groups* (2017 and 2022 corrected reprint), 10.18–10.19,
printed pp.191–192, identifies `g(R) = Ker(G(R[ε]) → G(R))` with `g ⊗ R` for a
finitely generated `k`-algebra `R`, functorially in the group (equation (59)).
Applied to an algebraic subgroup `H` and its inclusion into `G`, this
identifies `h(R)` with the image of `h ⊗ R` in `g ⊗ R`. That is the content of
`lie_eq_map_baseChange`. The ideal statement over an arbitrary coefficient
algebra is derived from the field case and has no separate statement in Milne.
Neither errata snapshot (2017, 2 November 2026; 2022 reprint, 4 November 2026)
has an entry for pp.191–192.

The Lean results hold for every commutative `k`-algebra, not only finitely
generated ones. They need `G` and `H` affine and locally of finite type over a
field. This module does not treat base change of the group schemes themselves
or smoothness of `F`.
