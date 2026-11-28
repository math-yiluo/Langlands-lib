# The center `E ⊗_F K` at a nonsplit completion

Module: `Langlands.Algebra.CentralSimple.LandherrNonsplitChart`.

In the setting of `Langlands.Algebra.CentralSimple.LandherrNonsplit` (`d` not a square in
`K`):

- `nonsplitCenterMap : E ⊗_F K → K(√d)`, `e ⊗ k ↦ e k`, is an `E`-algebra map;
  `exists_eq_one_tmul_add_skewRoot_tmul` writes every element of `E ⊗_F K` as
  `1 ⊗ k₁ + r ⊗ k₂`, and `nonsplitCenterMap_one_add` computes the image as `k₁ + k₂ ω`.
  Hence it is bijective (`nonsplitCenterMap_bijective`), giving `nonsplitCenterEquiv`.
- `centerConj = conjugation F E ⊗ id` on `E ⊗_F K`; `nonsplitCenterEquiv_centerConj` says
  that it corresponds to the conjugation `star` of `K(√d)`.
- `map_nonsplitCenterEquiv_tensorEquiv`: composing the coefficient identification
  `UnitaryPoints.tensorEquiv F E B K : K ⊗_F B ≃ (E ⊗_F K) ⊗_E B` (module
  `Langlands.Algebra.CentralSimple.UnitaryPoints`) with `nonsplitCenterEquiv ⊗ id` gives
  `nonsplitEquiv`.
- `nonsplitCenterEquiv_relativeNorm`: for a unit `x` of `K ⊗_F B`, the relative reduced
  norm `UnitaryPoints.relativeNorm F E B K x ∈ E ⊗_F K` corresponds to the reduced norm of
  `nonsplitEquiv x` in `K(√d) ⊗_E B`, by naturality of the reduced norm
  (`reducedNorm_naturality`) along `nonsplitCenterEquiv`.

## Provenance

Elementary: `E ⊗_F K ≅ K(√d)` when `d` is not a square in `K`, and the reduced norm commutes
with scalar extension. This is the local form of the relative reduced norm used in the proof
of Landherr's theorem (Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.7, Theorem 6.27).
