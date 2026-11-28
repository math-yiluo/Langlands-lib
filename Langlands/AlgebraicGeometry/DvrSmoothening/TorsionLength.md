# Torsion lengths of finite modules over a discrete valuation ring

- `torsionLength R M`: the length (in `ℕ∞`) of the torsion submodule of `M`. Néron's defect
  `pointDefect` (module `Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect`) is the torsion
  length of a pulled-back differential module.
- `torsionMap`, `mem_torsion_map`, `torsionLength_le_of_injective`, `torsionLength_congr`:
  functoriality; injective maps do not decrease torsion length, isomorphisms preserve it.
- `torsionLength_eq_zero_iff`: the torsion length is zero iff the torsion submodule is zero.
- Over a discrete valuation ring: `isFiniteLength_of_isTorsion`, `isFiniteLength_torsion`,
  `torsionLength_ne_top` (the torsion of a finite module has finite length) and
  `torsionLength_eq_zero_iff_free`.
- `torsionLength_lt_of_lattice`: **lattice comparison.** Let `θ : F' → F` be a map with image in
  `ϖ F` (`ϖ` a uniformizer, `F` finite), `N ⊆ F` a submodule contained in the image of `θ`, and
  `N' ⊆ F'` a submodule containing `θ⁻¹ N` and contained in its saturation. If `F ⧸ N` has non-zero
  torsion, then the torsion of `F' ⧸ N'` is strictly shorter than that of `F ⧸ N`. The proof
  has three steps. Since `N'` lies in the saturation of `θ⁻¹ N`, the torsion of `F' ⧸ θ⁻¹ N` maps
  onto that of `F' ⧸ N'`. The map `F' ⧸ θ⁻¹ N → F ⧸ N` induced by `θ` is injective, so the
  torsion of `F' ⧸ θ⁻¹ N` is at most the length of the part of the torsion `T` of `F ⧸ N` in its
  image. This part is a proper submodule of `T`. Otherwise, using `N ⊆ im θ ⊆ ϖ F`, the inverse
  image `S ⊆ F` of `T` satisfies `S ⊆ ϖ S`. As `F` is finite over the noetherian ring `R`,
  Nakayama's lemma gives `S = 0`, contradicting `T ≠ 0`.

The lattice comparison replaces the comparison of Jacobian minors in Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.3, proof of Proposition 5 (printed pp. 70–71).
