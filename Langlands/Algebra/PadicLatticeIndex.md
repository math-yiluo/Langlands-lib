# The index of the image of a `p`-adic endomorphism

This module proves lemmas about endomorphisms of free modules of finite rank over `ℤ_[p]`. It defines nothing. All names are in the namespace `Langlands.Algebra.PadicLattice`.

## Results

- `norm_card_quotient_span`: for `a ≠ 0` in `ℤ_[p]`, `‖#(ℤ_[p] ⧸ (a))‖ = ‖a‖` in `ℚ_[p]`. Write `a = u · p ^ v` with `u` a unit (Mathlib's `PadicInt.unitCoeff_spec`), so `(a) = (p ^ v)`. The ring `ℤ_[p] ⧸ (p ^ v)` is `ZMod (p ^ v)` by `PadicInt.ker_toZModPow`, so it has `p ^ v` elements. Both sides equal `p ^ (-v)`.
- `norm_card_quotient_range`: let `M` be free of finite rank over `ℤ_[p]` and `φ : M →ₗ M` with `det φ ≠ 0`. Then `‖#(M ⧸ range φ)‖ = ‖det φ‖`. The proof follows Mathlib's `Submodule.natAbs_det_equiv` (the case of `ℤ`). `φ` is injective because its matrix has nonzero determinant (`Matrix.mulVec_injective_of_det_ne_zero`). So `range φ` has full rank. The Smith normal form bases (`smithNormalFormTopBasis`, `smithNormalFormBotBasis`, coefficients `a_i`) give a map `f` with `det f = ∏ a_i`, and `det f` is associated to `det φ` (`LinearMap.associated_det_comp_equiv`). `Submodule.quotientEquivPiSpan` identifies `M ⧸ range φ` with `∏ ℤ_[p] ⧸ (a_i)`. The norms of associated elements agree because units of `ℤ_[p]` have norm `1`.
- `pow_smul_mem_range`: if `det φ ≠ 0` and `N` is at least the valuation of `det φ`, then `p ^ N • m ∈ range φ` for every `m`. The proof uses `A · adj(A) = det A · 1` (`Matrix.mul_adjugate`) for the matrix `A` of `φ`, and `p ^ N = det φ · (u⁻¹ p ^ (N - v))`.
- `det_ne_zero_of_injective`: an injective endomorphism has nonzero determinant. If the determinant were zero, `Matrix.exists_mulVec_eq_zero_iff` would give a nonzero vector in the kernel.

## Provenance

These are standard facts about lattices over the discrete valuation ring `ℤ_[p]`. The proof of `norm_card_quotient_range` adapts Mathlib's proof for `ℤ`. They are used for the step `#Coker(T_l β) = |det T_l β|_l^{-1}` in Milne, *Abelian Varieties* (author revision 2022), proof of Proposition 12.9, p. 23.
