# The trace of `ad` on the Lie algebra of a parabolic, split along its Levi decomposition

Module `Langlands.GroupScheme.Rational.LeviRadicalTrace`, namespace
`Langlands.GroupScheme.Lie`. Throughout, `k` is a field and `A` a commutative `k`-algebra. For an
affine group scheme `H` over `k`, `Additive (lieKernel H A)` is the Lie algebra of `H` over `A`
(the kernel of `H(A[ε]) → H(A)`). Its bracket is the Library's `instAffineKernelLieRing`, used
through the local instances `kernelLieRingOfField` and `kernelLieAlgebraOfField` of the module
`Langlands.GroupScheme.Lie.AdjointTangentBracket`. `Lie.targetMapLinear j A` is the Lie map of
a morphism `j`.

## Lie algebras of normal subgroups

Let `iV : V ⟶ Q` be a monomorphism of affine group schemes of locally finite type over `k`
whose image `SubgroupFunctor.range iV` is a normal subgroup functor.

- `lie_targetMapLinear_mem_range`: for `x` in the Lie algebra of `Q` over `A` and `w` in that
  of `V`, `⁅x, Lie iV w⁆` lies in the image of `Lie iV`. This is the Library's
  `SubgroupFunctor.lie_lie_mem_of_isNormal_coefficients` (the Lie algebra of a normal subgroup
  is an ideal over every coefficient algebra). `SubgroupFunctor.lie_eq_range` identifies the
  tangent submodule of the image with the range of `Lie iV`.
- `normalAdjoint iV hV A x`: the `A`-linear endomorphism `w ↦ (Lie iV)⁻¹ ⁅x, Lie iV w⁆` of the
  Lie algebra of `V`. `Lie iV` is injective (`targetMapLinear_injective`).
- `targetMapLinear_normalAdjoint`: `Lie iV (normalAdjoint x w) = ⁅x, Lie iV w⁆`.

## Reductive groups

- `trace_toEnd_eq_zero_of_isConnectedReductive`: if `H` is affine, of locally finite type and
  connected reductive over `k`, then `tr_A (ad y) = 0` for every `y` in the Lie algebra of `H`
  over `A`. The proof evaluates the adjoint determinant character at the dual-number point
  `y ∈ H(A[ε])`:
  - the character is trivial (`connectedReductiveAdjointDeterminant`), so its value is `1`;
  - by `adjointDeterminantCharacter_affinePoints` and `coordinateMatrix_det`, the value is the
    determinant of the coordinate matrix of `Ad` at `y`;
  - that matrix reduces to the identity modulo `ε` (`coordinateMatrix_naturality`), so its
    determinant is `1 + ε · tr N` with `N` its `ε`-part (`det_eq_of_map_fst_eq_one`);
  - `N` is the tangent matrix of the coordinate adjoint representation at `y`
    (`coordinateMatrix_conjugation_snd`), whose trace is `tr (ad y)`
    (`trace_toEnd_eq_trace_kernelDifferential`).

  Hence `tr (ad y) = 0`.
- `free_finite_lieKernel`: the Lie algebra over `A` of an affine group of locally finite type
  over `k` is finite free over `A` (by the Library's coordinates `finiteCoordinates`).

## Parabolics

Let `G` be connected reductive over `k`, `q : Q ⟶ G` a parabolic subgroup, `iV : V ⟶ Q` its
geometric unipotent radical (`LeviSubgroup.IsGeometricUnipotentRadical`) and `l : M' ⟶ Q` a
rational Levi subgroup (`IsRationalLeviSubgroup`), all affine of locally finite type.

- `trace_toEnd_levi`: for `y` in the Lie algebra of `M'` over `A`,

  ```text
  tr_A (ad (Lie l y) | Lie Q) = tr_A (normalAdjoint (Lie l y) | Lie V) + tr_A (ad y | Lie M').
  ```

  Proof. The Library gives a dynamic presentation of `Q` (`parabolicDynamic`) and a central
  cocharacter `ψ` of `M'` presenting `Q` as `P_G(ψ)`
  (`IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic`). For it, `M'` and `V`
  represent the centralizer and the unipotent subgroup
  (`IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic`,
  `Dynamic.range_comp_radical_eq_unipotent_of_reductive`). The Library's `Dynamic.lieProductEquiv` is then an `A`-linear
  isomorphism `Lie V × Lie M' ≅ Lie Q`, `(a, b) ↦ Lie iV a + Lie l b`. The inclusions
  `Dynamic.unipotentToParabolic` and `Dynamic.centralizerToParabolic` are `iV` and `l`
  (`SubgroupFunctor.IsRepresentedBy.hom_ext`). Conjugated by this isomorphism, `ad (Lie l y)` is the product
  map of `normalAdjoint (Lie l y)` and `ad y`: on the first factor by
  `targetMapLinear_normalAdjoint`, on the second because `Lie l` preserves brackets
  (`targetMapLinear_lie`). Mathlib's `LinearMap.trace_conj'` and `LinearMap.trace_prodMap'`
  give the formula.

With `trace_toEnd_eq_zero_of_isConnectedReductive` for `M'` (connected reductive by
`IsRationalLeviSubgroup.isConnectedReductive`), the last term vanishes.

## Provenance

Internal. The vanishing of `tr ad` on a reductive Lie algebra is the infinitesimal form of the
triviality of `det Ad` on a connected reductive group. The splitting `Lie Q = Lie V ⊕ Lie M'` is
the Lie algebra form of the Levi decomposition, as packaged in the Library's
`Dynamic.ParabolicLieDecomposition`.
