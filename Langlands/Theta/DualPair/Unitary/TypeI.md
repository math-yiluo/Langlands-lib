# The unitary dual pair on `W ⊗ V`

**GKT §10.5.2**, **Theorem 10.28** (p. 288), in Case `3₊` with `W` split.

The module `Langlands.Theta.DualPair.Unitary.TypeI` identifies the symplectic space of the unitary
dual pair used by the Library's Weil representation (`𝕎 = M_{α×2ν}(E)`, written
`M_{α×ν}(E) × M_{α×ν}(E)` by first and last `ν` columns, with the book's form
`polarizedForm (hermitianTracePairing c Q)`) with the tensor product `W ⊗_E V` of
`Langlands.Theta.DualPair.TypeI`, and the actions of `U(ν, ν)` and `U(Q)` with `g ⊗ 1` and `1 ⊗ h`.

## Setting

`E / F` with an involutive `c : E →ₐ[F] E` (`hc`), `Q` Hermitian (`hQ`), and from
`Langlands.Group.Unitary.Classical`: `W = E^{ν ⊕ ν}` (row vectors) with the skew-Hermitian form
`hyperbolicHermitianForm c hc ν`, `V = E^α` (column vectors) with the Hermitian form
`hermitianFormOf c hc Q hQ`, the isomorphisms `toIsometryGroup c hc : U(ν, ν) ≃* U(W)` and
`toIsometryGroupOfForm c hc hQ : U(Q) →* U(V)`.

## Content

- `UnitaryGroup.conj_ringInvo_algebraMap`: `c` fixes `F`, the hypothesis `hτ` of `tensorForm`.
- `matrixColsEquiv`, `unitaryTensorEquiv F α ν : W ⊗[E] V ≃ₗ[F] M_{α×ν}(E) × M_{α×ν}(E)`, from
  Mathlib's `TensorProduct.piScalarRight`: `w ⊗ v` goes to the matrix `(vᵢ wⱼ)`
  (`unitaryTensorEquiv_tmul`, `fromCols_unitaryTensorEquiv_tmul`).
- `unitaryTensorForm hc ν hQ`: the book's form `tensorForm` of `W ⊗ V`.
- `hermitianTensor_of_mul`: the Library's `hermitianTensor` at two matrices `(vᵢ wⱼ)`, `(v'ᵢ w'ⱼ)`
  is `⟨w, w'⟩ (v, v')_Q`.
- `polarizedForm_unitaryTensorEquiv` (`2 ≠ 0` in `F`): **`unitaryTensorEquiv` is an isometry from
  `tensorForm` to `polarizedForm (hermitianTracePairing c Q)`**. The Library's form
  `hermitianSymplecticForm c Q = ½ tr_{E/F}(…)` enters only here, through
  `hermitianSymplecticForm_fromCols` and `polarizedForm_eq_mul`.
- `toTraceIsometry_unitaryTensorEquiv`: `toTraceIsometry hc hQ g` (`w ↦ w g⁻¹`) corresponds to
  `tensorIsometryLeft (toIsometryGroup c hc g)`, i.e. **`g ⊗ 1`**.
- `toTraceIsometryOfForm_unitaryTensorEquiv`: `toTraceIsometryOfForm ν h` (`w ↦ h w`) corresponds
  to `tensorIsometryRight (toIsometryGroupOfForm c hc hQ h)`, i.e. **`1 ⊗ h`**.
- `pairToTraceIsometry_unitaryTensorEquiv`: the pair `(g, h)` acts by `g ⊗ h`
  (`tensorIsometry`).

All proofs reduce to pure tensors by `TensorProduct.inductionOn`.

## Declarations

`UnitaryGroup.conj_ringInvo_algebraMap`, `matrixColsEquiv`, `unitaryTensorEquiv`,
`unitaryTensorEquiv_tmul`, `fromCols_unitaryTensorEquiv_tmul`, `hermitianTensor_of_mul`,
`unitaryTensorForm`, `polarizedForm_unitaryTensorEquiv`, `toTraceIsometry_unitaryTensorEquiv`,
`toTraceIsometryOfForm_unitaryTensorEquiv`, `pairToTraceIsometry_unitaryTensorEquiv`. In the name
space `Langlands.Theta` (the first in `Langlands.UnitaryGroup`).

## Dependencies

`Langlands.Theta.DualPair.TypeI`, `Langlands.Group.Unitary.Classical`,
`Langlands.Theta.DualPair.Unitary.Pair` (with `Form`, `LeraySplitting`), Mathlib's
`TensorProduct.piScalarRight`.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), §10.5.2,
Theorem 10.28, p. 288.
