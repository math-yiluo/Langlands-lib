# Gelfand central elements of an enveloping algebra with an invariant form

Module `Langlands.Algebra.LieGelfandCentralElements`, namespace
`Langlands.Algebra.LieGelfandCentral`.

Let `k` be a field, `L` a `k`-Lie algebra with a finite basis `b : Basis I k L`, and `B` a
nondegenerate bilinear form on `L`; `B.dualBasis hB b` is the dual basis `b^i` with
`B (b^i) (b j) = δ_{ij}`. Write `U = U(L)` and `ι` for the canonical map.

## Definitions

- `adCoeff b x p q = b.repr ⁅x, b q⁆ p`, the matrix of `ad x` in the basis `b`.
- `gelfandMatrix B hB b : Matrix I I U`, the matrix `T` with entries
  `T p q = ∑ i, adCoeff b (b i) p q • ι (b^i)`; that is, `T = ∑ i ad(b i) ⊗ ι(b^i)`.
- `adMatrix b x`, the matrix of `ad x` with scalar entries in `U`; `commMat x A`, the entrywise
  commutator `ι x * A p q - A p q * ι x`.
- `gelfand B hB b n = trace (T ^ n)`.
- `symbolMatrix B hB b`, the matrix of linear forms `Ξ p q = ∑ i, adCoeff b (b i) p q • ξ (b^i)`.

## Results

- `commMat_mul`: `commMat x` is a derivation of the matrix ring over `U`.
- `adCoeff_lie`: `ad ⁅x, y⁆ = ad x ad y - ad y ad x` on matrix coefficients.
- `commMat_gelfandMatrix` (**Gelfand's rule**): if `B` is invariant,
  `B ⁅x, y⁆ z = B x ⁅y, z⁆`, then `commMat x T = T R - R T` with `R = adMatrix b x`. The
  coordinates of `⁅x, b^i⁆` in the dual basis are the negatives of the transposed coordinates of
  `ad x` (`LieCasimir.invariant_form_skew_adjoint`, `form_dual_left_eq_repr`), which expresses
  the invariance of the tensor `∑ b i ⊗ b^i`.
- `commMat_pow`: `commMat x (T ^ n) = T ^ n R - R T ^ n`, by induction.
- `gelfand_mem_center`: `gelfand n` is central. Its commutator with `ι x` is
  `trace (T ^ n R - R T ^ n)`, which vanishes because `R` has entries in the image of `k`, which
  commute with everything; the Library's `Kostant.mem_center_of_commute` concludes.
- `gelfandMatrix_mem`, `gelfandMatrix_pow_mem`, `gelfand_mem`: the entries of `T ^ n`, and
  `gelfand n`, lie in the filtration piece `U_n`.
- `symbol_gelfandMatrix_pow`, `symbol_gelfand`: for the symbols of
  `Langlands.Algebra.LieEnvelopingSymbol`, `symbol n (gelfand n) = trace (Ξ ^ n)`, by
  `symbol_mul` and induction.

## Provenance

Internal. This construction adapts the trace-power argument used for the matrix-generator
elements `gel` in the Library's `Langlands.Representation.Archimedean.Kostant.Center`
(`gel`, `adMat_pow`, `gel_mem_center`), whose proofs are followed here. It uses the adjoint
representation and a basis dual for the chosen invariant nondegenerate form. The elements are
not the same as `gel`: for `𝔤𝔩_1` every bracket vanishes, so `gelfand 1 = 0`, whereas the
degree-one matrix-generator element is the nonzero generator `ι(E₁₁)`.
