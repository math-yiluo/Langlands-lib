# Sections of a base change over an affine open as a tensor product

This internal helper module serves the noetherian model step of proper
line-bundle Hom representability. It compares sections of the base change
`T ×_{Spec R} Y` over the preimage of an open `V ⊆ Y` with the tensor
product of global sections of `T` and sections of `Y` over `V`.

## Setting

Fix a commutative ring `R`, a scheme `Y` with a morphism
`p : Y ⟶ Spec R`, an object `T` of `Over (Spec R)` and an open `V` of `Y`.
Write `P = pullback T.hom p`, with projections `fst : P ⟶ T.left` and
`snd : P ⟶ Y`.

- `Γ(T.left, ⊤)` is an `R`-algebra through the local instance
  `FiniteLinearEquations.sectionsAlgebra`. Its scalar map is
  `R ≅ Γ(Spec R, ⊤)` followed by `T.hom.appTop`.
- `Γ(Y, V)` is an `R`-algebra through
  `Scheme.TwoAffineOpenCover.algebraOfHom p V`. Its scalar map is
  `R ≅ Γ(Spec R, ⊤)` followed by `p.appLE ⊤ V`.

## Declarations

- `le_preimage_top f V : V ≤ f ⁻¹ᵁ ⊤` is `le_top` with the preimage kept
  in its type. The module uses it as the inclusion argument of
  `Scheme.Hom.appLE` from `⊤`. With this argument, the resulting terms
  typecheck without unfolding `f ⁻¹ᵁ ⊤`, so `rw` with the Mathlib `appLE`
  lemmas works. The literal `le_top` has type `V ≤ ⊤`. It is accepted only
  after unfolding `f ⁻¹ᵁ ⊤` to `⊤`, and then such rewrites fail.
- `sectionsTensorHom p T V` is an additive map from
  `Γ(T.left, ⊤) ⊗[R] Γ(Y, V)` to `Γ(P, snd ⁻¹ᵁ V)`. It sends `x ⊗ b` to the
  product of `fst.appLE ⊤ (snd ⁻¹ᵁ V) x` and `snd.app V b`.
- `sectionsTensorHom_tmul` is this formula on pure tensors (a `simp` lemma).
- `sectionsTensorHom_naturality`: let `g : T' ⟶ T` be a morphism over
  `Spec R` and `G = ((Over.pullback p).map g).left` the induced morphism of
  base changes. For every inclusion
  `h : snd' ⁻¹ᵁ V ≤ G ⁻¹ᵁ (snd ⁻¹ᵁ V)`, the restriction
  `G.appLE (snd ⁻¹ᵁ V) (snd' ⁻¹ᵁ V) h` applied to `sectionsTensorHom p T V z`
  equals `sectionsTensorHom p T' V` applied to
  `TensorProduct.map (pullSections g) id z`. Here `pullSections g` is
  `g.left.appTop` as an `R`-algebra map.
- `sectionsTensorHom_bijective`: if `T.left` is affine and `V` is an affine
  open, then `sectionsTensorHom p T V` is bijective.

## Proofs

**Well-definedness.** The map is `TensorProduct.liftAddHom` of the
biadditive product map. The balancing condition reduces, through
`Algebra.smul_def` and multiplicativity, to equality of the two images of a
scalar `r : R` in `Γ(P, snd ⁻¹ᵁ V)`. The private lemma `scalars_compat`
gives this equality. It writes both composites
`T.hom.appTop ≫ fst.appLE ⊤ (snd ⁻¹ᵁ V)` and
`p.appLE ⊤ V ≫ snd.app V` as `appLE` of the composite morphisms
`fst ≫ T.hom` and `snd ≫ p` (`Scheme.Hom.comp_appLE`,
`Scheme.Hom.appLE_comp_appLE`). These composites agree by
`pullback.condition`.

**Pure tensors.** `sectionsTensorHom_tmul` holds by definition
(`TensorProduct.liftAddHom_tmul`).

**Naturality.** By `TensorProduct.inductionOn`, it suffices to treat pure
tensors, since both sides are additive. `G.appLE` is a ring map, so it
distributes over the product. Two private lemmas then compute the factors.

- `fst_appLE_naturality`: the composite `fst.appLE ⊤ (snd ⁻¹ᵁ V) ≫ G.appLE`
  equals `g.left.appTop ≫ fst'.appLE ⊤ (snd' ⁻¹ᵁ V)`. Both sides are `appLE`
  of composites, and `G ≫ fst = fst' ≫ g.left` by `pullback.lift_fst`.
- `snd_app_naturality`: the composite `snd.app V ≫ G.appLE` equals
  `snd'.app V`, using `G ≫ snd = snd'` by `pullback.lift_snd`.

Here `Over.pullback p` sends `g` to the morphism
`pullback.lift (fst' ≫ g.left) snd'`.

**Bijectivity.** The proof applies the published theorem
`AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage`
with `f = T.hom`, `U = ⊤` (affine because `T.left` is affine), `g = p` and
the affine open `V`. That theorem is ported from the Anthropic Lean
formalization of Fermat's Last Theorem. Its `R`-algebra structure on
`Γ(T.left, ⊤)` is `algebraOfHom T.hom ⊤`. The private lemma
`algebraOfHom_top_eq` proves this structure equal to `sectionsAlgebra T`,
by `Algebra.algebra_ext` and `T.hom.appLE ⊤ ⊤ = T.hom.appTop`
(`Scheme.Hom.appLE_eq_app`). After rewriting, the theorem gives an
`R`-algebra isomorphism `e` from the tensor product onto
`Γ(P, fst ⁻¹ᵁ ⊤ ⊓ snd ⁻¹ᵁ V)`. On pure tensors, `e (a ⊗ b)` is the product of
the restrictions of `a` and `b`.

The opens `snd ⁻¹ᵁ V` and `fst ⁻¹ᵁ ⊤ ⊓ snd ⁻¹ᵁ V` are equal. The restriction
`ρ` along `eqToHom` of this equality is an isomorphism, hence bijective
(`ConcreteCategory.bijective_of_isIso`). The two maps
`sectionsTensorHom p T V` and `ρ ∘ e` agree on pure tensors, by
`Scheme.Hom.appLE_map` and `Scheme.Hom.app_eq_appLE`. Both are additive, so
they agree everywhere. Therefore `sectionsTensorHom p T V` is a composite of
bijections.

## Provenance

This module is internal to the project. Its content is the standard
identification of sections of an affine base change,
`Γ(Spec A ×_{Spec R} V) = A ⊗_R Γ(V)` for affine `V`. The isomorphism itself
comes from the published ported FLT theorem cited above. This module adds the
explicit additive map, its value on pure tensors, and naturality in `T`.
