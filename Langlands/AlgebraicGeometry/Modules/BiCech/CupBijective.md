# The cup map on products of affine opens is bijective

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.CupBijective`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

## Setting

- `R : CommRingCat`, with `πX : X ⟶ Spec R`, `πY : Y ⟶ Spec R` and `πP : P ⟶ Spec R`.
- Projections `p₁ : P ⟶ X`, `p₂ : P ⟶ Y`, with `hπ : p₁ ≫ πX = πP` and
  `hP : IsPullback p₁ p₂ πX πY`.
- Sections are `R`-modules through the structure morphisms, by
  `OModulePresheaf.ofModules`; this is the module structure of the Library's Čech cochains.

## Results

- `appLE_algebraMap_left` and `appLE_algebraMap_right`: pulling back the image of `r : R`
  along `p₁`, respectively `p₂`, gives the image of `r` in `Γ(P, W)`. The proofs use
  `Scheme.Hom.appLE_comp_appLE`; the right-hand version also uses `hP.w`.
- `cupBilin` and `cupLin`: the cup map of `BiCech.Cup` is `R`-bilinear. `cupLin` is the
  induced `R`-linear map `L(U) ⊗[R] M(V) → (p₁^* L ⊗ p₂^* M)(W)`, with
  `cupLin_tmul : cupLin (l ⊗ₜ m) = cup l m`.
- `frameEquiv he`: for a frame `e` of `N` on `U`, the `R`-linear bijection
  `Γ(Z, U) ≃ N(U)`, `a ↦ a • e`. Bijectivity is the frame property on `U` itself
  (`isFrameOn_self_bijective`).
- `cupLin_bijective hπ hP hU hV he he'`. Assume `U` and `V` are affine and carry frames
  `e` of `L` and `e'` of `M`. Then `cupLin` is bijective onto the sections over
  `p₁⁻¹ U ⊓ p₂⁻¹ V`.

Proof of `cupLin_bijective`. Write `ε = cup e e'`; it is a frame by `isFrameOn_cup`.
Precomposing `cupLin` with `frameEquiv ⊗ frameEquiv` gives the map
`a ⊗ b ↦ (p₁^♯ a · p₂^♯ b) • ε`. By the semilinearity of the cup map, this is
`tensorSec(a ⊗ b) • ε`. Here `tensorSec` is the ring map
`Γ(X, U) ⊗[R] Γ(Y, V) → Γ(P, p₁⁻¹ U ⊓ p₂⁻¹ V)` of
`Picard.FieldTwoAxisH1Injectivity`, which is bijective for affine `U` and `V`
(`tensorSec_bijective`). Multiplication by the frame `ε` is bijective, so `cupLin` is
bijective.

Provenance: internal. This is the affine computation
`Γ(U × V, p₁^* L ⊗ p₂^* M) = L(U) ⊗_R M(V)` used in the proof of the Künneth formula
(Stacks Project, Varieties, tag 0BED), proved here for frames.
