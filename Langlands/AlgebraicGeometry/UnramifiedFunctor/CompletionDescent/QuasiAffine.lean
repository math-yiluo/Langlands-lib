import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Descent of a quasi-affine scheme along a flat surjection of affine schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

/-- Two points with the same image in the base of a pullback square come from one point of
the corner. -/
theorem exists_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ z : P, fst z = x ∧ snd z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]

variable {Z Z' W : Scheme.{u}} (π : Z' ⟶ Z) (g : W ⟶ Z')

theorem firstLift_w :
    (pullback.fst (pullback.snd (g ≫ π) π ≫ π) π ≫ pullback.fst (g ≫ π) π) ≫ g ≫ π =
      pullback.snd (pullback.snd (g ≫ π) π ≫ π) π ≫ π := by
  rw [Category.assoc, pullback.condition (f := g ≫ π) (g := π)]
  exact pullback.condition

/-- The map `(W ×_Z Z') ×_Z Z' ⟶ W ×_Z Z'` forgetting the middle factor. -/
def firstLift : pullback (pullback.snd (g ≫ π) π ≫ π) π ⟶ pullback (g ≫ π) π :=
  pullback.lift _ _ (firstLift_w π g)

theorem secondLift_w (σ : pullback (g ≫ π) π ⟶ W) (hσ : σ ≫ g = pullback.snd _ _) :
    (pullback.fst (pullback.snd (g ≫ π) π ≫ π) π ≫ σ) ≫ g ≫ π =
      pullback.snd (pullback.snd (g ≫ π) π ≫ π) π ≫ π := by
  rw [Category.assoc, reassoc_of% hσ, pullback.condition]

/-- The map `(W ×_Z Z') ×_Z Z' ⟶ W ×_Z Z'` applying `σ` to the first two factors. -/
def secondLift (σ : pullback (g ≫ π) π ⟶ W) (hσ : σ ≫ g = pullback.snd _ _) :
    pullback (pullback.snd (g ≫ π) π ≫ π) π ⟶ pullback (g ≫ π) π :=
  pullback.lift _ _ (secondLift_w π g σ hσ)

@[reassoc]
theorem firstLift_fst : firstLift π g ≫ pullback.fst (g ≫ π) π =
    pullback.fst (pullback.snd (g ≫ π) π ≫ π) π ≫ pullback.fst (g ≫ π) π :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem firstLift_snd : firstLift π g ≫ pullback.snd (g ≫ π) π =
    pullback.snd (pullback.snd (g ≫ π) π ≫ π) π :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem secondLift_fst (σ : pullback (g ≫ π) π ⟶ W) (hσ : σ ≫ g = pullback.snd _ _) :
    secondLift π g σ hσ ≫ pullback.fst (g ≫ π) π =
      pullback.fst (pullback.snd (g ≫ π) π ≫ π) π ≫ σ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem secondLift_snd (σ : pullback (g ≫ π) π ⟶ W) (hσ : σ ≫ g = pullback.snd _ _) :
    secondLift π g σ hσ ≫ pullback.snd (g ≫ π) π =
      pullback.snd (pullback.snd (g ≫ π) π ≫ π) π :=
  pullback.lift_snd _ _ _

/-- Descent of a quasi-affine scheme. Let `π : Z' ⟶ Z` be a flat surjective morphism of affine
schemes and `g : W ⟶ Z'` with `W` quasi-affine. Let `σ : W ×_Z Z' ⟶ W` be a morphism over the
second projection, with the diagonal as a section and satisfying the cocycle identity. Then
`W` is the base change along `π` of a scheme `V` over `Z`, by a map `p : W ⟶ V` which
identifies the first projection with `σ`. -/
theorem exists_isPullback_of_isQuasiAffine [IsAffine Z] [IsAffine Z'] [Flat π] [Surjective π]
    [W.IsQuasiAffine]
    (σ : pullback (g ≫ π) π ⟶ W) (hσ : σ ≫ g = pullback.snd _ _)
    (hsec : pullback.lift (𝟙 W) g (by simp) ≫ σ = 𝟙 W)
    (hcoc : firstLift π g ≫ σ = secondLift π g σ hσ ≫ σ) :
    ∃ (V : Scheme.{u}) (w : V ⟶ Z) (p : W ⟶ V), IsPullback p g w π ∧
      pullback.fst (g ≫ π) π ≫ p = σ ≫ p := by
  classical
  have hK : IsPullback (pullback.fst (g ≫ π) π) (pullback.snd (g ≫ π) π) (g ≫ π) π :=
    IsPullback.of_hasPullback _ _
  have : IsAffineHom (pullback.fst (g ≫ π) π) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hK.flip inferInstance
  have : (pullback (g ≫ π) π).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (pullback.fst (g ≫ π) π)
  -- Flat base change of global sections.
  have h₁ := LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback hK
  rw [Scheme.Hom.comp_appTop] at h₁
  have hE := LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback (pullback.snd (g ≫ π) π ≫ π) π)
  rw [Scheme.Hom.comp_appTop] at hE
  -- The diagonal is a section of `σ`, so `σ` is injective on global sections.
  have hsec' : σ.appTop ≫ (pullback.lift (𝟙 W) g (by simp) :
      W ⟶ pullback (g ≫ π) π).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hsec, Scheme.Hom.id_appTop]
  have hinj : Function.Injective σ.appTop.hom :=
    Function.LeftInverse.injective
      (g := (pullback.lift (𝟙 W) g (by simp) : W ⟶ pullback (g ≫ π) π).appTop.hom)
      (fun x => by simpa using congrArg (fun φ => φ.hom x) hsec')
  have ha : g.appTop ≫ σ.appTop = (pullback.snd (g ≫ π) π).appTop := by
    rw [← Scheme.Hom.comp_appTop, hσ]
  obtain ⟨B, rB, ιB, hB, hιB⟩ := LocallyQuasiFiniteDescent.exists_isPushout_eqLocus
    π.appTop π.flat_appTop g.appTop (pullback.fst (g ≫ π) π).appTop σ.appTop
    (pullback.snd (g ≫ π) π).appTop h₁
    (pullback.fst (pullback.snd (g ≫ π) π ≫ π) π).appTop
    (pullback.snd (pullback.snd (g ≫ π) π ≫ π) π).appTop hE
    (firstLift π g).appTop (secondLift π g σ hσ).appTop
    (by rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, firstLift, pullback.lift_fst])
    (by rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, secondLift, pullback.lift_fst])
    (by rw [← Scheme.Hom.comp_appTop, firstLift, pullback.lift_snd])
    (by rw [← Scheme.Hom.comp_appTop, secondLift, pullback.lift_snd])
    ha (by rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hcoc]) hinj
  -- The spectrum of the pushout square.
  have hSpec := isPullback_SpecMap_of_isPushout rB π.appTop ιB g.appTop hB
  have hSr : Spec.map π.appTop = Z'.isoSpec.inv ≫ π ≫ Z.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : Flat (Spec.map π.appTop) := by rw [hSr]; infer_instance
  have : Surjective (Spec.map π.appTop) := by rw [hSr]; infer_instance
  have : Flat (Spec.map ιB) := MorphismProperty.of_isPullback (P := @Flat) hSpec.flip inferInstance
  have : Surjective (Spec.map ιB) :=
    MorphismProperty.of_isPullback (P := @Surjective) hSpec.flip inferInstance
  have hq := Flat.isQuotientMap_of_surjective (Spec.map ιB)
  -- `Γ(W ×_Z Z')` is `Γ(W) ⊗_B Γ(W)`, with the two maps `fst` and `σ`.
  have hD : IsPushout ιB ιB (pullback.fst (g ≫ π) π).appTop σ.appTop := by
    refine IsPushout.of_left ?_ hιB hB
    rw [hB.w, ha]
    exact h₁
  have hSpecD := isPullback_SpecMap_of_isPushout _ _ _ _ hD
  have hfstΓ := Scheme.isPullback_toSpecΓ_toSpecΓ (pullback.fst (g ≫ π) π)
  -- The open image of `W` in `Spec B`.
  let ω : W ⟶ Spec B := W.toSpecΓ ≫ Spec.map ιB
  have hpre : Spec.map ιB ⁻¹' Set.range ω = Set.range W.toSpecΓ := by
    apply le_antisymm
    · rintro y ⟨x, hx⟩
      obtain ⟨δ, hδ₁, hδ₂⟩ := exists_of_isPullback hSpecD (W.toSpecΓ x) y
        (by rw [← hx]; rfl)
      obtain ⟨d, hd₁, hd₂⟩ := exists_of_isPullback hfstΓ x δ hδ₁.symm
      refine ⟨σ d, ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply, hd₂, hδ₂]
    · rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hopen : IsOpen (Set.range ω) := by
    rw [← hq.isOpen_preimage, hpre]
    exact W.toSpecΓ.isOpenEmbedding.isOpen_range
  let V : (Spec B).Opens := ⟨Set.range ω, hopen⟩
  have hωV : Set.range ω ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_rfl
  let p : W ⟶ V := IsOpenImmersion.lift V.ι ω hωV
  have hpfac : p ≫ V.ι = ω := IsOpenImmersion.lift_fac _ _ _
  have hWV : IsPullback p W.toSpecΓ V.ι (Spec.map ιB) := by
    refine IsOpenImmersion.isPullback _ _ _ _ hpfac.symm ?_
    ext1
    rw [Scheme.Opens.opensRange_ι]
    exact hpre
  have hpaste := hWV.paste_vert hSpec
  refine ⟨V, V.ι ≫ Spec.map rB ≫ Z.isoSpec.inv, p, ?_, ?_⟩
  · refine hpaste.of_iso (Iso.refl _) (Iso.refl _) Z'.isoSpec.symm Z.isoSpec.symm
      (by simp) ?_ (by simp) ?_
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, Category.assoc]
      rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id,
        Category.comp_id]
    · simp only [Iso.symm_hom, hSr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hpfac]
    simp only [ω, ← Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Category.assoc, ← Spec.map_comp, hιB]

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
