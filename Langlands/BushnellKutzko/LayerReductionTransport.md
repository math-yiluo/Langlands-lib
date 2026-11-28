# Transport of layer reductions and cuspidal data

The module `Langlands.BushnellKutzko.LayerReductionTransport` transports the finite-field
data of simple types (BK93 (5.5.10)) along a change of coordinates that may also change the
ring of scalars of the lattice chain. This covers the `𝔬_E`-lattice chain of a field
`E = F[β]` and its conjugate, whose rings of integers and residue fields are different
types.

## Bases

`basisTransport σ τ hτ b` is the basis obtained from a basis `b` of a `k₁`-vector space `M₁`
along an additive isomorphism `τ : M₁ ≃+ M₂` with `τ(cx) = σ(c) τ(x)` for a field
isomorphism `σ : k₁ ≃ k₂`. It is built with `Module.Basis.ofEquivFun`, and
`basisTransport_equivFun` says that the coordinates of `τ x` are the images under `σ` of
those of `x`.

## Semilinear images of lattice chains

`LatticeChain.SemilinearImage L₁ σO f L₂` says that the additive automorphism `f` of `V`
satisfies `f(av) = σO(a) f(v)` for a ring isomorphism `σO : O₁ ≃ O₂` and that
`v ∈ L₁ i ↔ f v ∈ L₂ i` for all `i`. `SemilinearImage.symm` gives the inverse statement.

- `SemilinearImage.period_eq`: the two chains have the same period. Each `L₂ i` is the image
  of `L₁ i`, and the image of `𝔭_{O₁} L` is `σO(𝔭_{O₁}) f(L) = 𝔭_{O₂} f(L)`
  (`map_smul_semilinear` and `map_ideal_ringJacobson`, module `StratumSemilinearTransport`),
  so `LatticeChain.period_unique` applies.
- `SemilinearImage.layerEquiv`: the additive isomorphism of layers
  `L₁ i/L₁ (i+1) ≃ L₂ i/L₂ (i+1)`, `[v] ↦ [f v]` (`layerEquiv_mk`), built from
  `Submodule.mapQ` of the restrictions of `f` and `f⁻¹`. It is `σO`-semilinear
  (`layerEquiv_smul`) and, for local rings, semilinear for the induced isomorphism of residue
  fields `ResidueField.mapEquiv σO` (`layerEquiv_residue_smul`), since residue scalars act
  through representatives (`LatticeChain.layerResidueTower`).
- `SemilinearImage.layerBasis` and `layerBasis_equivFun`: the transported layer bases.
- `SemilinearImage.isLayerReduction`: let `f` be the action of `g ∈ Aut_F(V)` and
  `U₂ = gU₁g⁻¹`. If `b₂` has the transported coordinates and `φ₂(u)` is the matrix of
  `φ₁(g⁻¹ug)` with the residue-field isomorphism applied to its entries, then
  `IsLayerReduction L₁ U₁ _ b₁ φ₁` implies `IsLayerReduction L₂ U₂ _ b₂ φ₂`. For
  `v ∈ L₂ i`, write `v = f(f⁻¹v)`; then `u v = f((g⁻¹ug) f⁻¹v)`, the class of `uv` is the
  image of the class of `(g⁻¹ug)(f⁻¹v)`, and applying a ring homomorphism entrywise commutes
  with the matrix action (`RingHom.map_mulVec`).

## General linear groups over isomorphic fields

- `generalLinearMapEquiv σ n : GL_n(k) ≃* GL_n(k')` applies a field isomorphism `σ` to the
  matrix entries (`Units.mapEquiv` of `RingEquiv.mapMatrix`).
- `isCuspidal_comp_generalLinearMapEquiv`: pulling a cuspidal representation
  (`FiniteGeneralLinear.IsCuspidal`) back along `GL_n(k') ≃ GL_n(k)` gives a cuspidal
  representation. Membership in the standard block parabolic and in its unipotent radical is
  a condition on the entries (`mem_parabolic_iff`, `mem_unipotentSubgroup_iff`) preserved by
  `σ` and `σ⁻¹`, so a proper parabolic over `k'` is proper over `k` and the unipotent
  radicals correspond.
- `tensorPowerRepresentation_comp_piMap`: the `e`-fold tensor power of the pulled-back
  representation, composed with the product isomorphism, is the original tensor power.

## Sources

These are change-of-coordinates properties of the data of a simple type in Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (5.5.10), printed
pp. 184–185 (PDF pp. 196–197): the reductions `U(𝔅_β) → GL_f(k_E)^e` on the layers and the
cuspidal representation `σ₀`. BK93 does not state them separately. Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
