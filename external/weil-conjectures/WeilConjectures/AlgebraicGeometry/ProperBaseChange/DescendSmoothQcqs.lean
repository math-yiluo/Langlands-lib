/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Smoothness descends along qcqs affine-transition limits

## References

* Stacks Project, Limits, Tag 0C0C, in Situation 081D
* Stacks Project, Limits, Tag 0C0C, Situation 081D
* Morphisms, Tag 01VB
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem descend_smooth_to_stage {J : Type u} [SmallCategory J]
    [IsCofiltered J] (X : J ⥤ Scheme.{u}) (c : Cone X) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (X.map f)]
    {i : J} [CompactSpace (X.obj i)] [QuasiSeparatedSpace (X.obj i)]
    {P : Scheme.{u}} [CompactSpace P] (p : P ⟶ X.obj i)
    [LocallyOfFinitePresentation p] [Smooth (pullback.snd p (c.π.app i))] :
    ∃ j : Over i, Smooth (pullback.snd p (X.map j.hom)) := by
  classical
  let B := (X.obj i).affineCover.finiteSubcover
  have hBaff (k : B.I₀) : IsAffine (B.X k) := by
    dsimp [B]
    rw [Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  let V := B.pullback₁ p
  have hVcompact (k : V.I₀) : CompactSpace (V.X k) := by
    have : IsAffine (B.X k) := hBaff k
    change CompactSpace ↥(pullback p (B.f k) : Scheme.{u})
    infer_instance
  let W (k : V.I₀) := (V.X k).affineCover.finiteSubcover
  let U := V.bind W
  have : Fintype U.I₀ := by
    change Fintype (Sigma fun k : B.I₀ ↦ (W k).I₀)
    infer_instance
  have hUaff (k : U.I₀) : IsAffine (U.X k) := by
    change IsAffine ((W k.1).X k.2)
    dsimp [W]
    rw [Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  have hstage (k : U.I₀) :
      ∃ j : Over i, Smooth (pullback.snd (U.f k ≫ p) (X.map j.hom)) := by
    have : IsAffine (B.X k.1) := hBaff k.1
    have : IsAffine (U.X k) := hUaff k
    let a : U.X k ⟶ B.X k.1 := (W k.1).f k.2 ≫ B.pullbackHom p k.1
    have ha : a ≫ B.f k.1 = U.f k ≫ p := by
      dsimp [a, U, V]
      simp only [Category.assoc, Scheme.Cover.pullbackHom_map]
      rfl
    have : LocallyOfFinitePresentation (a ≫ B.f k.1) := by
      rw [ha]
      infer_instance
    have : LocallyOfFinitePresentation a :=
      MorphismProperty.of_postcomp @LocallyOfFinitePresentation a (B.f k.1)
        (inferInstance : IsOpenImmersion (B.f k.1)) ‹_›
    have : Smooth (pullback.snd (a ≫ B.f k.1) (c.π.app i)) := by
      rw [ha]
      rw [← pullbackRightPullbackFstIso_inv_snd_snd p (c.π.app i) (U.f k)]
      infer_instance
    have : Smooth (pullback.snd a (pullback.fst (B.f k.1) (c.π.app i))) := by
      have h : Smooth (pullback.snd (a ≫ B.f k.1) (c.π.app i)) := inferInstance
      rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
        (pullbackRightPullbackFstIso (B.f k.1) (c.π.app i) a).hom,
        pullbackRightPullbackFstIso_hom_snd] at h
      exact (MorphismProperty.postcomp_iff @Smooth _ _
        (inferInstance : IsOpenImmersion (pullback.snd (B.f k.1) (c.π.app i)))).mp h
    let D := baseChangeDiagram X (B.f k.1)
    let d := baseChangeCone X c (B.f k.1)
    let t : D ⟶ (Functor.const (Over i)).obj (B.X k.1) :=
      { app := fun j ↦ pullback.fst _ _
        naturality := fun j l f ↦ by simp [D] }
    have hD (j : Over i) : IsAffine (D.obj j) := by
      change IsAffine (pullback (B.f k.1) (X.map j.hom))
      infer_instance
    obtain ⟨j, hj⟩ := Scheme.exists_smooth_stage_of_affine_diagram D d
      (isLimitBaseChangeCone X c (B.f k.1) hc) hD t
      (pullback.fst (B.f k.1) (c.π.app i))
      (fun j ↦ baseChangeCone_π_app_fst X c (B.f k.1) j) a
    refine ⟨j, ?_⟩
    rw [← ha]
    rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
      (pullbackRightPullbackFstIso (B.f k.1) (X.map j.hom) a).hom,
      pullbackRightPullbackFstIso_hom_snd]
    exact (MorphismProperty.postcomp_iff @Smooth _ _
      (inferInstance : IsOpenImmersion (pullback.snd (B.f k.1) (X.map j.hom)))).mpr hj
  choose js hs using hstage
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image js)
  refine ⟨j, ?_⟩
  apply IsZariskiLocalAtSource.of_openCover
    (P := @Smooth) (U.pullback₂ (pullback.fst p (X.map j.hom)))
  intro k
  change U.I₀ at k
  obtain ⟨f⟩ := hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  have : Smooth (pullback.snd (U.f k ≫ p) (X.map (js k).hom)) := hs k
  have hmap : X.map j.hom = X.map f.left ≫ X.map (js k).hom := by
    rw [← X.map_comp, Over.w f]
  have : Smooth (pullback.snd (U.f k ≫ p) (X.map j.hom)) := by
    rw [hmap]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd
      (U.f k ≫ p) (X.map (js k).hom) (X.map f.left)]
    infer_instance
  change Smooth (pullback.snd (U.f k) (pullback.fst p (X.map j.hom)) ≫
    pullback.snd p (X.map j.hom))
  rw [← pullbackRightPullbackFstIso_hom_snd p (X.map j.hom) (U.f k)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem exists_smooth_over_pullback {J : Type u} [SmallCategory J]
    [IsCofiltered J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    {k : J} {Z Y : Over (D.obj k)} (γ : Z ⟶ Y)
    [LocallyOfFinitePresentation γ.left]
    [CompactSpace Z.left] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (hS : Smooth ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (k' : J) (f : k' ⟶ k), ∀ {k'' : J} (f' : k'' ⟶ k'),
      Smooth ((Over.pullback (D.map (f' ≫ f))).map γ).left := by
  classical
  -- The identity-stage model of `γ` over the system base changed to `Y`.
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFinitePresentation Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw))
  have hI4 : @Smooth (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  have hsm : Smooth (pullback.snd (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k)))) := by
    rw [← hsq.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j, hj⟩ := @descend_smooth_to_stage (Over k) _ _ (baseChangeDiagram D Y.hom)
    (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc) _
    (Over.mk (𝟙 k)) _ _ Z.left _ (pullback.lift γ.left Z.hom hw) hI1 hsm
  refine ⟨j.left.left, j.left.hom, ?_⟩
  intro k'' f'
  let m : Over.mk (f' ≫ j.left.hom) ⟶ j.left := Over.homMk f'
  have : Smooth (pullback.snd (pullback.lift γ.left Z.hom hw)
      ((baseChangeDiagram D Y.hom).map j.hom)) := hj
  have htail : Smooth (pullback.snd (pullback.lift γ.left Z.hom hw)
      ((baseChangeDiagram D Y.hom).map (m ≫ j.hom))) := by
    rw [Functor.map_comp, ← pullbackLeftPullbackSndIso_inv_snd_snd]
    infer_instance
  -- Both the resulting smooth morphism and the base change of `γ` to the stage `k''` are
  -- pullbacks of `γ.left` along the projection of the stage model of `Y`.
  have hργ : IsPullback (pullback.fst Z.hom (D.map (f' ≫ j.left.hom)))
      ((Over.pullback (D.map (f' ≫ j.left.hom))).map γ).left γ.left
      (pullback.fst Y.hom (D.map (f' ≫ j.left.hom))) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map (f' ≫ j.left.hom)))
    · refine (IsPullback.of_hasPullback Z.hom (D.map (f' ≫ j.left.hom))).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (m ≫ j.hom : Over.mk (f' ≫ j.left.hom) ⟶ _)))
      (pullback.snd (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (m ≫ j.hom : Over.mk (f' ≫ j.left.hom) ⟶ _)))
      γ.left (pullback.fst Y.hom (D.map (f' ≫ j.left.hom))) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map
          (m ≫ j.hom : Over.mk (f' ≫ j.left.hom) ⟶ _))).paste_horiz hsq3
    exact h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have hcomp : (hρq.isoIsPullback _ _ hργ).hom ≫
      ((Over.pullback (D.map (f' ≫ j.left.hom))).map γ).left =
      pullback.snd (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (m ≫ j.hom)) :=
    hρq.isoIsPullback_hom_snd _ _ hργ
  rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
    (hρq.isoIsPullback _ _ hργ).hom, hcomp]
  exact htail

/-- A locally finitely presented morphism between qcqs schemes over a qcqs stage is
smooth at every sufficiently late stage if its limit base change is smooth. -/
theorem exists_eventually_smooth_of_isLimit_qcqs
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (_hf : Smooth (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      Smooth (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left) := by
  obtain ⟨i, hi, h⟩ := exists_smooth_over_pullback D c _hc f₀ _hf
  refine ⟨i.unop, leOfHom hi.unop, ?_⟩
  intro j hij
  exact h (homOfLE hij).op

end AlgebraicGeometry
