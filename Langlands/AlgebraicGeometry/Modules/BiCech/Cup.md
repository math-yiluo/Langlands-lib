# The cup map into an external tensor product

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.Cup`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

Let `f : P ⟶ X` and `g : P ⟶ Y` be morphisms of schemes, `L : X.Modules` and
`M : Y.Modules`.

- `extTensor f g L M = tensorObj (pullback f L) (pullback g M)`. Here `pullback` is
  Mathlib's `Scheme.Modules.pullback`, and `tensorObj` is the Library's sheaf tensor.
- `tsec_add_left`, `tsec_add_right` and `tsec_smul_right` complete the bilinearity of
  `tsec` (`BiCech.TensorFrame`).
- `cup hW l m` is defined for `l ∈ L(U)`, `m ∈ M(V)` and `hW : W ≤ f⁻¹ U ⊓ g⁻¹ V`. It is
  `tsec` of the restrictions to `W` of the pulled-back local sections
  `pullbackLocalSection f l` and `pullbackLocalSection g m`. These are the adjunction units
  of the ported FLT definition `Scheme.Modules.pullbackLocalSection`.
- Linearity: `cup_add_left`, `cup_add_right`, and the semilinearity
  `cup_smul_left : cup hW (a • l) m = f.appLE U W _ a • cup hW l m` and `cup_smul_right`.
- Restriction: `map_cup` (restriction in `W`), `cup_map_left` and `cup_map_right`
  (restriction of `l` or `m`).
- `isFrameOn_cup`: if `e` is a frame of `L` over `U` and `e'` is a frame of `M` over `V`,
  then `cup hW e e'` is a frame of `extTensor f g L M` over `W`. Pulled-back frames are
  frames (FLT theorem `Scheme.Modules.IsFrameOn.pullbackLocalSection`). Frames restrict.
  The tensor of frames is a frame (`isFrameOn_tsec`).

Provenance: internal. The cup map is the canonical map
`L(U) ⊗ M(V) → (p₁^* L ⊗ p₂^* M)(U × V)` used in the proof of the Künneth formula
(Stacks Project, Varieties, tag 0BED).
