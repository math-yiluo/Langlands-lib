# Naturality of the zero loci of linear-system sections in the base algebra

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`. Let `L` be a line bundle on `X` with frames `e i` on the members of `𝒰`, and `C` a
Čech representative of `L`.

- `appLE_algebraMap`; `eRes`, `isFrameOn_eRes` (frames restricted to the pieces `𝒰.inter s`);
  `tRes`, `isFrameOn_tRes` (pulled-back frames on the pieces of the base-changed cover).
- `coordΘ`, `coordΘ_tmul`, `coordΘ_add`, `frameEquiv_symm_apply`, `eq_frameEquiv_smul`: the
  coordinate of `Θ A x` on a piece in the pulled-back frame, and its value on `a ⊗ k`.
- `appLE_coordΘ`: these coordinates are natural in the algebra.
- `inter_eq_of_idx_zero`, `isAffineOpen_inter_of_idx_zero`, `iSup_inter_idx_zero`: the degree-zero
  pieces are the members of the cover.
- `pbLB f L`: the pullback of a line bundle with the pulled-back module as underlying module.
- `res_homEquivSections`: the restriction of `σ_u := C.homEquivSections A u` to a piece is the
  Čech component.
- `zeroIdeal_comap_homEquivSections`: for `φ : A → B` and any `g : X_B ⟶ X_A` over `Spec φ`
  compatible with the projections to `X`, `(zeroIdeal σ_u).comap g = zeroIdeal σ_{φ ∘ u}`.
- `zeroIdeal_homEquivSections_smul`: `zeroIdeal σ_{c • v} = zeroIdeal σ_v` for a unit `c`.

All comparisons are made on coordinates in frames, not through isomorphisms of pulled-back
modules.

## Source

Kleiman, *The Picard scheme*, p.25 (proof of Theorem 3.13): the correspondence (3.13.1) between maps
`Q_T → N` and sections is compatible with base change.
