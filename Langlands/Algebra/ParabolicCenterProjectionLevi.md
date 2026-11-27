# The Levi factor of grading data and its Harish-Chandra projection

Module `Langlands.Algebra.ParabolicCenterProjectionLevi`, namespace
`Langlands.Algebra.ParabolicCenterProjection.GradingData`.

Fix grading data `D : GradingData g H` and an injective Lie map `j : m →ₗ⁅ℂ⁆ g` whose range is
the centralizer of `H` (hypotheses `hj`, `hrange`), as in
`ParabolicCenterProjectionFiniteStatement`.

## The Levi basis

- `leviIndex`: the basis indices `i` with `wt i H = 0`; for them `⁅H, b i⁆ = 0`
  (`lie_H_basis_levi`).
- `leviBasis`: a basis of `m` with `j (leviBasis i) = b i` (`j_leviBasis`). The preimages are
  linearly independent, and they span because `j x` is an eigenvector of `ad H` of eigenvalue
  `0`, hence a combination of the `b i` with `wt i H = 0`.
- `repr_j`, `repr_j_eq_zero`: the coordinates of `j x` are those of `x`, and vanish outside
  `leviIndex`.

## Gradings, form and nondegeneracy on the Levi factor

- `φm`, `evm`, `regLevi`: the restricted grading and eigenvalues, and the preimage of `reg`
  (`lie_regLevi`: `⁅regLevi, leviBasis i⁆ = evm i • leviBasis i`).
- `leviForm`: the form pulled back by `j`; `leviForm_separating`: it is nondegenerate on the
  Levi basis, since a vector of `H`-weight zero is orthogonal to basis vectors of nonzero
  `H`-weight.
- `leviDualOf γ`: the preimage of `T γ`, which commutes with `H`.
- `exists_shiftPart_ne_zero_levi`: the nondegeneracy hypothesis of the vanishing theorem for
  central elements of `U(m)`, transported from the corresponding facts in `g` through `j`.

## The Cartan subalgebra of the Levi factor and the projection

- `leviCartan`: the span of the Levi basis vectors of grading zero, an abelian Lie subalgebra
  (`leviCartan_lie_eq_zero`), with basis `leviCartanBasis`.
- `leviPositive`: the span of the Levi basis vectors of positive grading.
- `leviDecomposition`: the `RelativeEnvelopingDecomposition` of `U(m)` relative to
  `U(leviCartan)` given by `LieWeightProjection.relativeEnvelopingDecomposition_of_weight`.
- `leviProj`: its centre projection `Z(U(m)) → Z(U(leviCartan))`, with
  `z - U(incl)(leviProj z) ∈ positiveWeightRightIdeal (leviBasis) φm` (`sub_leviProj_mem`).
- `leviProj_injective`: if `leviProj z = 0`, then `z` lies in the positive right ideal, and
  `center_eq_zero_of_mem_positiveWeightRightIdeal` gives `z = 0`.

## Provenance

This is the Harish-Chandra homomorphism of the Levi factor with respect to the Cartan
subalgebra and the positive system given by the regular grading, and its injectivity on the
centre (Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups*, 1968, Chapter I, §6, uses
the corresponding isomorphism of the Levi centre with Weyl group invariants). The construction
is internal.
