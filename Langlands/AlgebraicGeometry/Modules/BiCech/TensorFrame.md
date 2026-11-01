# The tensor of two frames is a frame

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.TensorFrame`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

Frames are the ported FLT notion `AlgebraicGeometry.Scheme.Modules.IsFrameOn`.
`IsFrameOn s V` means that for every open `W` contained in the domain of `s` and in `V`,
the map `g ↦ g • s|_W`, from `Γ(Z, W)` to the sections over `W`, is bijective. The tensor
product is the Library's sheafified sectionwise tensor `Langlands.Scheme.Modules.tensorObj`.

- `smul_tmul_bijective`: pure algebra. If `g ↦ g • a` and `g ↦ g • b` are bijective, so is
  `g ↦ g • (a ⊗ b)`, through `TensorProduct.lid` and `TensorProduct.congr`.
- `tsec a b` is the image of `a ⊗ₜ b` under the sheafification unit
  `tensorSheafifyUnit A B`. It is compatible with restriction (`tsec_map`) and with
  scalars (`tsec_smul`).
- `exists_tsec_locally` and `eq_locally_of_tensorSheafifyUnit` are the elementwise forms of
  local surjectivity and local injectivity of the sheafification unit. Both come from
  Mathlib's instances for `toSheafify`.
- `isFrameOn_tsec`: if `α` and `β` are frames of `A` and `B` over `W`, then `tsec α β` is a
  frame of `tensorObj A B` over `W`.

Proof of `isFrameOn_tsec`. On every `V ⊆ W` the sectionwise tensor is free of rank one
on `α|_V ⊗ β|_V`. Hence `θ_V : g ↦ g • (tsec α β)|_V` equals the sheafification unit
applied to `g • (α|_V ⊗ β|_V)`.

- Injectivity of `θ_V`: if `θ_V g = θ_V g'`, local injectivity of the unit makes the two
  sectionwise tensors agree locally. By freeness, `g` and `g'` then agree locally, hence
  globally by the sheaf property of `𝒪_Z`.
- Surjectivity of `θ_V`: a section is locally the image of sectionwise tensors
  `g_z • (α ⊗ β)`. The `g_z` agree on overlaps by injectivity of `θ`. They glue in `𝒪_Z`,
  and the glued function maps to the section by the sheaf property of the tensor sheaf.

Provenance: internal. This is the standard fact that a tensor product of trivialized
invertible sheaves is trivialized by the tensor of the trivializing sections.
