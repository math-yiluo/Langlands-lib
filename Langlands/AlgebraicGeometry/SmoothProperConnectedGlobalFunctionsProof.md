# Proof of relative global functions for smooth proper morphisms

This module proves the Library proposition
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions` in every universe `u`:

```lean
theorem Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions :
    SmoothProperConnectedGlobalFunctions.{u}
```

For schemes `X` and `S` and a morphism `p : X ⟶ S` that is smooth, proper and geometrically
connected, the canonical map `p.app U : Γ(S, U) ⟶ Γ(X, p ⁻¹ᵁ U)` is an isomorphism for every
open `U` of `S`. The base is arbitrary.

The theorem is `main` applied to the proofs of two published prerequisite propositions:

- `Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctions` (the field case),
  proved by `Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`. For a
  field `K`, a morphism `p : X ⟶ Spec K` that is smooth, proper and geometrically connected
  has `IsIso p.appTop`. Sources: Stacks Tags 0BUG and 056T.
- `Langlands.Algebra.SmoothEqualizerFibreCriterion` (the fibrewise Čech criterion), proved by
  `Langlands.Algebra.smoothEqualizerFibreCriterion`. Let `δ₁ δ₂ : C₀ →ₐ[A] C₁` be maps between
  smooth `A`-algebras, with `C₀` faithfully flat over `A`. Suppose that for every prime `P` of
  `A` the equalizer of the base changes `id ⊗ δᵢ` to `P.ResidueField` consists of scalars.
  Then the equalizer of `δ₁` and `δ₂` is the image of `A`. This is a derived Čech form of the
  degree-zero part of Stacks Tag 0E62. It is not literally stated in the source.

The theorem

```lean
theorem SmoothProperConnectedGlobalFunctionsProof.main
    (hF : FieldSmoothProperConnectedGlobalFunctions.{u})
    (hC : Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}) :
    SmoothProperConnectedGlobalFunctions.{u}
```

does the scheme-theoretic reduction to these two statements.

The proof follows the route behind Stacks Tag 0E0L, but works with Čech algebras of a finite
affine cover instead of perfect complexes.

## Steps of the Lean proof

1. **Reduction to affine opens** (`isIso_app_of_forall_isAffineOpen`). Suppose `p.app V` is
   bijective for every affine open `V` of `S`. Then the stalk maps of `p.c` are injective
   (affine opens form a basis). So `p.app U` is injective for every open `U`, and it is
   surjective because sections of the pushforward sheaf are locally in the image.
2. **Reduction to the base `Spec R`** (`main`). For an affine open `V` we use
   `(p ∣_ V) ≫ hV.isoSpec.hom`. It is still smooth and proper, and it is geometrically
   connected (stability under base change and composition with an isomorphism). Its `appTop`
   is `p.app V` up to the isomorphisms `IsAffineOpen.isoSpec_hom_appTop`,
   `morphismRestrict_appTop` and `Scheme.Opens.ι_image_top`.
3. **Affine base** (`isIso_appTop_of_spec`). `X` is quasi-compact, so it has a finite family
   of affine opens `U i` covering it. Since `p` is separated, all pairwise intersections
   `U i ⊓ U j` are affine (`isAffineHom_diagonal_iff`). The fibre `X_P = X ×_{Spec R} Spec κ(P)`
   over each prime `P` is smooth, proper and geometrically connected over `κ(P)`. So the
   field case gives that `(pullback.snd p (fibreMap κ(P))).appTop` is an isomorphism.
4. **Čech argument** (`isIso_appTop_of_cover`). Put `C₀ = ∏ i Γ(X, U i)` and
   `C₁ = ∏ (i, j) Γ(X, U i ⊓ U j)`, both as `R`-algebras through `secHom`. Let
   `cechLeft` and `cechRight` be the two restriction maps.
   - Both algebras are smooth over `R`: `smooth_secHom` uses `HasRingHomProperty.appLE` for
     `Smooth`, and finite products of smooth algebras are smooth.
   - `C₀` is faithfully flat. Its fibre `κ(P) ⊗ C₀` is nonzero (`fibre_nontrivial`), since
     it maps to the sections of the nonempty fibre `X_P`.
   - The fibre hypothesis of the Čech criterion is `fibre_hyp`. Over each affine `U i`, the
     map `κ(P) ⊗[R] Γ(X, U i) → Γ(X_P, U i ×_R κ(P))` is injective. This follows from
     `isPushout_fibre`, which is Mathlib's `isIso_pushoutSection_of_isAffineOpen` for the
     fibre square, through `fibreTensor`. A `κ(P)`-Čech cocycle therefore glues to a global
     section of `X_P`. That section is a constant from `κ(P)` by the field case.
   - The Čech criterion then shows that a global section of `X` comes from `R`, because
     its restrictions to the `U i` form a cocycle. This gives surjectivity, using
     `eq_of_locally_eq'` for the sheaf `X.sheaf`. Injectivity follows from faithful
     flatness (`FaithfulSMul.algebraMap_injective`).

## Provenance

The statement is a derived specialization of Stacks Lemma 36.32.6 (Tag 0E0L), registered as
`stacks-relative-global-functions-0e0l-2026-10-22`. The Stacks proof uses Lemma 36.32.5
(Tag 0E62), which needs perfect complexes and cohomology and base change. Mathlib does not
have these. This proof replaces that step by the algebraic criterion above, applied to the
Čech algebras of a finite affine cover. The reduction to affine opens, the choice of cover,
and the identification of the fibre Čech algebras with base changes are written for this
module and are not taken from the source.
