# Joint injectivity of global sections of tensor products over a field

This helper module for `ImageGenerationReducedProof` proves the following.
Over a field `k`, tensor products of morphisms of affine schemes preserve the
condition that a family of global-section maps can only all vanish on zero.
It is internal, derived content: a standard linear-algebra fact (vector spaces
over a field are free), moved to schemes using global sections of fibre
products. It formalizes no specific numbered result from the literature.

Throughout, "a family of maps `u i` is jointly injective" means
`∀ y, (∀ i, u i y = 0) → y = 0`. For linear or additive maps this is the same
as injectivity of the product map.

## Linear algebra

`k` is a field and `M`, `N` are `k`-vector spaces.

- `basisTensorEquiv M Q`: the linear equivalence `M ⊗[k] Q ≃ (ι →₀ Q)` given by
  the chosen basis of `M`, indexed by `ι = Module.Free.ChooseBasisIndex k M`.
  It is built from `Basis.repr` and Mathlib's `finsuppScalarLeft`.
- `basisTensorEquiv_lTensor`: these coordinates are natural in `Q`. The
  coordinate of `(v.lTensor M) x` is `v` applied to the coordinate of `x`.
- `lTensor_eq_zero_of_forall`: if the maps `v j : N → P j` are jointly
  injective, so are the maps `(v j).lTensor M` on `M ⊗[k] N`. Each coordinate
  of `x` is killed by every `v j`, so it vanishes.
- `rTensor_eq_zero_of_forall`: the same for `(u i).rTensor N`, obtained by
  transporting along `TensorProduct.comm`.
- `map_eq_zero_of_forall`: if both `u i : M → P i` and `v j : N → Q j` are
  jointly injective families, then so is the family
  `TensorProduct.map (u i) (v j)` indexed by pairs `(i, j)`. Writing
  `map (u i) (v j) = (v j).lTensor ∘ (u i).rTensor`, apply the two previous
  lemmas in turn.

## Transfer to schemes over `Spec k`

The setting is objects of `Over (Spec k)`, with the cartesian monoidal
structure (so `X ⊗ Y` is the fibre product over `Spec k`).

- `sectionsAlgebra X`: the `k`-algebra structure on `Γ(X, ⊤)` from the
  structure morphism. It is the published FLT definition
  `Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤`, used as a local instance.
- `appLE_top_top_of_le`: `φ.appLE ⊤ ⊤ e = φ.appTop`, for any proof
  `e : ⊤ ≤ ⊤`. This restates the published FLT lemma with the binder in the
  form that occurs inside `algebraOfHom`.
- `sectionsHom a`: the global-section map of a morphism `a : X ⟶ Y` over
  `Spec k`, as a `k`-algebra homomorphism `Γ(Y, ⊤) →ₐ[k] Γ(X, ⊤)`.
- `tensorSections X Y : Γ(X, ⊤) ⊗[k] Γ(Y, ⊤) →ₐ[k] Γ(X ⊗ Y, ⊤)` is the
  comparison map `a ⊗ b ↦ fst^* a · snd^* b`
  (`Algebra.TensorProduct.productMap`).
- `appTop_tensorHom_tensorSections`: the comparison map is natural. For
  `a : X' ⟶ X` and `b : Y' ⟶ Y`, the global-section map of `a ⊗ₘ b` after
  `tensorSections X Y` equals `tensorSections X' Y'` after
  `TensorProduct.map (sectionsHom a) (sectionsHom b)`. This is checked on pure
  tensors using `tensorHom_fst` and `tensorHom_snd`.
- `tensorSections_bijective`: if `X` and `Y` are affine, the comparison map is
  bijective. The published FLT solution
  `S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution`,
  applied to the top opens, gives a `k`-algebra isomorphism `e` from
  `Γ(X, ⊤) ⊗[k] Γ(Y, ⊤)` to the sections of the fibre product over
  `fst⁻¹ ⊤ ⊓ snd⁻¹ ⊤`. That open is `⊤`
  (`bijective_presheaf_map_of_eq_top`: restriction to it is bijective). The
  restriction of `tensorSections X Y` equals `e`, by checking pure tensors.
- `appTop_tensorHom_eq_zero`: the main result of the module. Let `X`, `Y` and
  all `X' i`, `Y' j` be affine over `Spec k`. Suppose the global-section maps
  of `a i : X' i ⟶ X` are jointly injective, and likewise those of
  `b j : Y' j ⟶ Y`. Then the global-section maps of the morphisms
  `a i ⊗ₘ b j : X' i ⊗ Y' j ⟶ X ⊗ Y` are jointly injective. Write a section of
  `X ⊗ Y` as `tensorSections X Y x`. By naturality and injectivity of
  `tensorSections (X' i) (Y' j)`, every `map (sectionsHom (a i))
  (sectionsHom (b j))` kills `x`, so `x = 0` by `map_eq_zero_of_forall`.
