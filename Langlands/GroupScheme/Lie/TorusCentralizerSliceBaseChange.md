# Lie containment in a torus-centralizer slice after field extension

Author: Worker 1630.

This derived helper module proves one statement. Let `G` be a group scheme over
a field `k` and `j₀ : T₀ ⟶ G` a homomorphism from a commutative group scheme.
Suppose the Lie algebra of `T₀` centralizes every column of a matrix `B` over
`k`. Then, over any field extension `K` of `k`, the Lie algebra of the base
change `T_K` centralizes every Lie element of `G_K` whose coordinates lie in the
`K`-column space of `B`. Worker 1420 requested this statement, in the exact form
of `targetMap_mem_elementCentralizerLie_baseChange_of_mulVec`, for the project's
route to unirationality of the scheme of maximal tori (SGA 3, Exposé XIV). It
extends the slice from `TorusCentralizerSlice` to a field extension. It is
derived linear algebra, not a cited theorem. No external theorem is asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`. Throughout,
`k` and `K` are fields in one universe with `[Algebra k K]`. `G` is a group
scheme over `Spec k` with affine structure morphism, and
`c : FiniteCoordinates G d` gives finite Lie coordinates. These identify the
Library's Lie algebra `lieKernel G A` with `Fin d → A` through
`c.equiv (.of (CommRingCat.of k) A)`. `G_K` and `T_K` denote the Library's base
changes `(GroupScheme.baseChange (algebraBaseMap k K)).obj G`, and likewise for
`T₀`. `c.baseChange k K` gives the pulled-back coordinates on `G_K`.
`kernelBaseChangeEquiv k K G A` is the Library comparison between Lie points of
`G_K` and of `G` with values in a `K`-algebra `A`, and
`kernelBaseChangeLinearEquiv` is its linear version on `Additive` vectors.
`tangentMatrix` of `adjointRepresentation c` is the coordinate matrix of `ad`.
`elementCentralizerLie G Z` is the Library's Lie centralizer of the Lie element
`Z`.

## Coordinate bridges

- `kernelBaseChangeLinearEquiv_ofMul`: the linear comparison applied to
  `Additive.ofMul x` is `Additive.ofMul` of the multiplicative comparison. This
  holds by definition (`rfl`).
- `FiniteCoordinates.baseChange_equiv_apply`: for a `K`-algebra `A` that is
  also a `k`-algebra with a scalar tower, the pulled-back coordinates of a Lie
  vector of `G_K` are the original coordinates of its image under
  `kernelBaseChangeLinearEquiv`. Proof: the given `k`-algebra structure on `A`
  equals the one obtained by composing with `algebraMap k K`
  (`Algebra.algebra_ext` and the scalar tower). After substituting it, both
  sides agree by definition.

## Adjoint matrices kill the slice

Here `T₀` is a commutative group scheme over `Spec k`, `j₀ : T₀ ⟶ G`, and `B`
is a `d × r` matrix over `k`. The hypothesis `hB` says: for every column `j`
and every Lie element `Y` of `T₀`, the element `j₀ Y` lies in
`elementCentralizerLie G` of the Lie element with coordinates column `j` of
`B`.

- `tangentMatrix_targetMap_mul_eq_zero`: under `hB`, the matrix product
  `tangentMatrix k (j₀ Y) * B` is zero for every Lie element `Y` of `T₀`.
  Proof: the Library criterion `mem_elementCentralizerLie_iff_adjointDifferential`
  turns each membership into `ad(j₀ Y)` killing column `j`. The Library lemmas
  `adjointDifferentialFamily_apply` and `Matrix.toLin'_apply` then give
  entrywise vanishing.

From here on `T₀` also has affine, locally finite type structure morphism.

- `targetMapAdjointApplyBaseChange c j₀ v` (definition): for `v : Fin d → K`,
  the `K`-linear map from the Lie algebra of `T_K` (as `Additive` vectors
  with values in `K`) to `Fin d → K` sending `t` to `ad(j₀ t) v`. Here
  `ad(j₀ t)` is the adjoint matrix of `G_K` in the pulled-back coordinates. It
  is the composite of the Library's `targetMapLinear` for the base-changed
  homomorphism, the representation's `kernelDifferential`, `Matrix.toLin'` and
  evaluation at `v`. It exists to make the linear structure available to the
  spanning argument below.
- `targetMapAdjointApplyBaseChange_apply`: its value at `Additive.ofMul t` is
  `tangentMatrix K (j₀ t) *ᵥ v`. Proof: unfold the composite and rewrite with
  `MatrixRepresentation.kernelDifferential_apply` and `Matrix.toLin'_apply`.
- `tangentMatrix_targetMap_baseChange_mulVec_eq_zero`: under `hB`, for every
  `s : Fin r → K` and every Lie element `t` of `T_K` with values in `K`,
  `tangentMatrix K (j₀ t) *ᵥ (B.map (algebraMap k K) *ᵥ s) = 0`.
  Proof: let `L` be `targetMapAdjointApplyBaseChange c j₀` at the vector
  `B.map (algebraMap k K) *ᵥ s`. On a Lie element extended from `T₀`, the
  Library's `kernelFieldExtension`, `L` vanishes. Indeed, by
  `tangentMatrix_targetMap_kernelFieldExtension` (from `TorusCentralizerSlice`)
  its adjoint matrix is the image over `K` of `tangentMatrix k (j₀ Y)`. Multiplying it by
  `B` mapped to `K` gives the image of `tangentMatrix k (j₀ Y) * B = 0`. Every
  Lie element of `T_K` comes from `K ⊗[k] Lie(T₀)` under the Library's
  linear equivalence `schemeScalarExtension`. By `TensorProduct.inductionOn` it
  suffices to treat `a ⊗ y = a • (1 ⊗ y)` and sums. The Library's
  `schemeScalarExtension_one_tmul` identifies `1 ⊗ y` with the extension of
  `y`, so `L` vanishes on these by linearity.

## Main statement

- `targetMap_mem_elementCentralizerLie_baseChange_of_mulVec`: assume `hB`. Let
  `Z : lieKernel G K` be a Lie point of `G` with values in `K` whose
  coordinates `c.equiv (.of (CommRingCat.of k) K) (Additive.ofMul Z)` lie in
  the range of multiplication by `B.map (algebraMap k K)`. Then for every Lie
  element `t` of `T_K`, `Additive.ofMul (j₀ t)` lies in
  `elementCentralizerLie G_K ((kernelBaseChangeEquiv k K G K).symm Z)`. Proof:
  by `mem_elementCentralizerLie_iff_adjointDifferential` for the pulled-back
  coordinates, the membership means `ad(j₀ t)` kills the coordinate vector of
  the transported `Z`. By the coordinate bridges, that vector equals the
  original coordinates of `Z`, which equal `B.map (algebraMap k K) *ᵥ s` for
  some `s`. The previous lemma concludes.

## Provenance

The content is an internal helper for the project's route to the
unirationality of the scheme of maximal tori (SGA 3, Exposé XIV); it is not
taken from a cited source. The argument is the routine fact that the condition "`ad(j₀ Y)` kills
`v`" is `K`-linear in both the torus Lie element and `v`, so it passes from a
`k`-spanning set to its `K`-span. The module uses only the Library API cited
above and Mathlib's matrix and tensor-product API. It places no hypothesis on
the fields beyond those stated.
