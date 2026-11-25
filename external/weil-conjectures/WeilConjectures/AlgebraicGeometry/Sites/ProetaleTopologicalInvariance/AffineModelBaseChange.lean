/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.AffineModel
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.IndEtaleFullyFaithful
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Base change of affine models along a universal homeomorphism

Let `r : X ⟶ Y` be a morphism of schemes, `U ⊆ Y` an affine open with affine preimage
`r ⁻¹ᵁ U`, and write `A = Γ(Y, U)`, `A' = Γ(X, r ⁻¹ᵁ U)`, an `A`-algebra via `r.app U`.
Base change along `r` of the affine model `ofAlgebra hU D` of a weakly étale `A`-algebra `D` is
the affine model of `A' ⊗[A] D`. If `r` is a universal homeomorphism, then so is `A → A'`, and
base change is full on affine models of ind-étale algebras.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isPullback_fromSpec`: the square
  `Spec A' ⟶ Spec A` over `r` is cartesian.
- `Algebra.IsUniversalHomeomorphism.of_isUniversalHomeomorphism_app`: if `r` is a universal
  homeomorphism, then so is `A → A'`.
- `AlgebraicGeometry.Scheme.ProEt.overPullbackObjOfAlgebraIso`: the base change of
  `ofAlgebra hU D` is `ofAlgebra hU' (A' ⊗[A] D)`.
- `AlgebraicGeometry.Scheme.ProEt.overPullback_map_ofAlgebraMap_comp_iso_hom`: compatibility of
  this isomorphism with algebra maps.
- `AlgebraicGeometry.Scheme.ProEt.exists_overPullback_map_eq_of_indEtale`: base change along a
  universal homeomorphism is full on affine models of ind-étale algebras.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Y : Scheme.{u}} (r : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
  (hU' : IsAffineOpen (r ⁻¹ᵁ U)) [Algebra Γ(Y, U) Γ(X, r ⁻¹ᵁ U)]
  (hr : algebraMap Γ(Y, U) Γ(X, r ⁻¹ᵁ U) = (r.app U).hom)

include hr in
/-- The square
```
  Spec Γ(X, r⁻¹U) ──→ Spec Γ(Y, U)
        │                  │
        ↓                  ↓
        X ───────r───────→ Y
```
given by the inclusions of the affine opens `r ⁻¹ᵁ U` and `U` is cartesian. -/
lemma isPullback_fromSpec :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, r ⁻¹ᵁ U))))
      hU'.fromSpec hU.fromSpec r := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [hr, CommRingCat.ofHom_hom, Scheme.Hom.app_eq_appLE,
      IsAffineOpen.SpecMap_appLE_fromSpec r hU hU']
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

include hr hU hU' in
/-- If `r` is a universal homeomorphism, then so is `Γ(Y, U) → Γ(X, r ⁻¹ᵁ U)`. -/
lemma _root_.Algebra.IsUniversalHomeomorphism.of_isUniversalHomeomorphism_app
    [IsUniversalHomeomorphism r] :
    Algebra.IsUniversalHomeomorphism Γ(Y, U) Γ(X, r ⁻¹ᵁ U) :=
  ⟨MorphismProperty.of_isPullback (isPullback_fromSpec r hU hU' hr).flip inferInstance⟩

variable (D : Type u) [CommRing D] [Algebra Γ(Y, U) D] [Algebra.WeaklyEtale Γ(Y, U) D]

include hr in
/-- The base change of the affine model `ofAlgebra hU D` along `r` is the affine model of
`Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D`, the projection to `Spec D` being induced by
`Algebra.TensorProduct.includeRight`. -/
lemma isPullback_ofAlgebra :
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        D →+* Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D)))
      (ofAlgebra hU' (Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D)).hom (ofAlgebra hU D).hom r :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, U) Γ(X, r ⁻¹ᵁ U) D)).flip.paste_vert
    (isPullback_fromSpec r hU hU' hr)

/-- The base change of the affine model `ofAlgebra hU D` along `r` is the affine model
`ofAlgebra hU' (Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D)`. -/
noncomputable def overPullbackObjOfAlgebraIso :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ofAlgebra hU D) ≅
      ofAlgebra hU' (Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D) :=
  MorphismProperty.Over.isoMk (isPullback_ofAlgebra r hU hU' hr D).isoPullback.symm
    (isPullback_ofAlgebra r hU hU' hr D).isoPullback_inv_snd

@[simp]
lemma overPullbackObjOfAlgebraIso_inv_left :
    (overPullbackObjOfAlgebraIso r hU hU' hr D).inv.left =
      (isPullback_ofAlgebra r hU hU' hr D).isoPullback.hom := rfl

@[simp]
lemma overPullbackObjOfAlgebraIso_hom_left :
    (overPullbackObjOfAlgebraIso r hU hU' hr D).hom.left =
      (isPullback_ofAlgebra r hU hU' hr D).isoPullback.inv := rfl

/-- Under `overPullbackObjOfAlgebraIso`, the projection of the base change to `Spec D` is
induced by `Algebra.TensorProduct.includeRight`. -/
@[reassoc (attr := simp)]
lemma overPullbackObjOfAlgebraIso_inv_left_fst :
    (overPullbackObjOfAlgebraIso r hU hU' hr D).inv.left ≫ pullback.fst (ofAlgebra hU D).hom r =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        D →+* Γ(X, r ⁻¹ᵁ U) ⊗[Γ(Y, U)] D)) :=
  (isPullback_ofAlgebra r hU hU' hr D).isoPullback_hom_fst

variable {D₁ D₂ : Type u} [CommRing D₁] [CommRing D₂] [Algebra Γ(Y, U) D₁] [Algebra Γ(Y, U) D₂]
  [Algebra.WeaklyEtale Γ(Y, U) D₁] [Algebra.WeaklyEtale Γ(Y, U) D₂]

/-- `overPullbackObjOfAlgebraIso` is compatible with algebra maps: base change along `r` of the
morphism of affine models induced by `g : D₁ →ₐ D₂` is the morphism induced by
`Γ(X, r ⁻¹ᵁ U) ⊗ g`. -/
@[reassoc]
lemma overPullback_map_ofAlgebraMap_comp_iso_hom (g : D₁ →ₐ[Γ(Y, U)] D₂) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map (ofAlgebraMap hU g) ≫
        (overPullbackObjOfAlgebraIso r hU hU' hr D₁).hom =
      (overPullbackObjOfAlgebraIso r hU hU' hr D₂).hom ≫
        ofAlgebraMap hU' (Algebra.TensorProduct.map (AlgHom.id _ _) g) := by
  rw [← Iso.inv_comp_eq]
  apply MorphismProperty.Over.Hom.ext
  refine (isPullback_ofAlgebra r hU hU' hr D₁).hom_ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, overPullbackObjOfAlgebraIso_hom_left,
      Category.assoc, IsPullback.isoPullback_inv_fst, ofAlgebraMap_left]
    rw [← (MorphismProperty.Over.isPullback_map_left r (ofAlgebraMap hU g)).w,
      overPullbackObjOfAlgebraIso_inv_left_fst_assoc, ofAlgebraMap_left, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · rw [MorphismProperty.Over.w, MorphismProperty.Over.w]

include hU' hr in
/-- **Fullness of base change on ind-étale affine models.** If `r` is a universal homeomorphism
and `D₂` is ind-étale over `Γ(Y, U)`, every morphism between the base changes along `r` of the
affine models `ofAlgebra hU D₁` and `ofAlgebra hU D₂` is the base change of a morphism. -/
theorem exists_overPullback_map_eq_of_indEtale [IsUniversalHomeomorphism r]
    [Algebra.IndEtale Γ(Y, U) D₂]
    (φ : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ofAlgebra hU D₁) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ofAlgebra hU D₂)) :
    ∃ ψ : ofAlgebra hU D₁ ⟶ ofAlgebra hU D₂,
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map ψ = φ := by
  have := Algebra.IsUniversalHomeomorphism.of_isUniversalHomeomorphism_app r hU hU' hr
  obtain ⟨F, hF⟩ := (ofAlgebraMap_bijective hU').2
    ((overPullbackObjOfAlgebraIso r hU hU' hr D₁).inv ≫ φ ≫
      (overPullbackObjOfAlgebraIso r hU hU' hr D₂).hom)
  obtain ⟨g, rfl⟩ := (Algebra.IsUniversalHomeomorphism.bijective_tensorProductMap
    Γ(Y, U) Γ(X, r ⁻¹ᵁ U) D₂ D₁).2 F
  refine ⟨ofAlgebraMap hU g, ?_⟩
  have h := overPullback_map_ofAlgebraMap_comp_iso_hom r hU hU' hr g
  rw [hF, Iso.hom_inv_id_assoc, cancel_mono] at h
  exact h

end AlgebraicGeometry.Scheme.ProEt
