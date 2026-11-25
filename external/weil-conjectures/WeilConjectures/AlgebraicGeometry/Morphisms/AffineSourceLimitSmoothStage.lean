/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual smoothness for an affine source model

## References

* Stacks Project, Tag 0C0C, affine-local reduction using Tags 0CAQ and 01ZM
* Stacks Project, Tag 0C0C, with Situation 081D and Tags 0CAQ, 01ZM(2)-(3)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem smooth_snd_target_iff {A B D E : Scheme.{u}}
    (p : A ⟶ B) (g : D ⟶ E) (q : B ⟶ E) [IsOpenImmersion q] :
    Smooth (pullback.snd (p ≫ q) g) ↔
      Smooth (pullback.snd p (pullback.fst q g)) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
    (pullbackRightPullbackFstIso q g p).hom,
    pullbackRightPullbackFstIso_hom_snd]
  exact MorphismProperty.postcomp_iff @Smooth _ _
    (inferInstance : IsOpenImmersion (pullback.snd q g))

/-- Eventual smoothness for a single affine source chart. -/
theorem exists_smooth_stage_of_affine_source_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    {i : I} {P : Scheme.{u}} [IsAffine P] (p : P ⟶ X.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Smooth (pullback.snd p (α.app i))] :
    ∃ j : Over i, Smooth (pullback.snd p (X.map j.hom)) := by
  classical
  have : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (X.map f) := hXa
  have (j : I) : IsNoetherian (X.obj j) := hN j
  have (j : I) : QuasiSeparatedSpace (X.obj j) := hqs j
  let B := (X.obj i).affineCover.finiteSubcover
  have hBaff (k : B.I₀) : IsAffine (B.X k) := by
    dsimp [B]
    rw [OpenCover.finiteSubcover_X]
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
    rw [OpenCover.finiteSubcover_X]
    infer_instance
  have hstage (k : U.I₀) :
      ∃ j : Over i, Smooth (pullback.snd (U.f k ≫ p) (X.map j.hom)) := by
    have : IsAffine (B.X k.1) := hBaff k.1
    have : IsAffine (U.X k) := hUaff k
    let a : U.X k ⟶ B.X k.1 := (W k.1).f k.2 ≫ B.pullbackHom p k.1
    have ha : a ≫ B.f k.1 = U.f k ≫ p := by
      dsimp [a, U, V]
      simp only [Category.assoc, Cover.pullbackHom_map]
      rfl
    have : LocallyOfFinitePresentation (a ≫ B.f k.1) := by
      rw [ha]
      infer_instance
    have : LocallyOfFinitePresentation a :=
      MorphismProperty.of_postcomp @LocallyOfFinitePresentation a (B.f k.1)
        (inferInstance : IsOpenImmersion (B.f k.1)) ‹_›
    have : Smooth (pullback.snd (a ≫ B.f k.1) (α.app i)) := by
      rw [ha]
      rw [← pullbackRightPullbackFstIso_inv_snd_snd p (α.app i) (U.f k)]
      infer_instance
    have : Smooth (pullback.snd a (pullback.fst (B.f k.1) (α.app i))) :=
      (smooth_snd_target_iff a (α.app i) (B.f k.1)).mp ‹_›
    let D := baseChangeDiagram X (B.f k.1)
    let c := baseChangeCone X (Cone.mk S α) (B.f k.1)
    let t : D ⟶ (Functor.const (Over i)).obj (B.X k.1) :=
      { app := fun j ↦ pullback.fst _ _
        naturality := fun j l f ↦ by simp [D] }
    have hD (j : Over i) : IsAffine (D.obj j) := by
      change IsAffine (pullback (B.f k.1) (X.map j.hom))
      infer_instance
    obtain ⟨j, hj⟩ := exists_smooth_stage_of_affine_diagram D c
      (isLimitBaseChangeCone X (Cone.mk S α) (B.f k.1) hα) hD t
      (pullback.fst (B.f k.1) (α.app i))
      (fun j ↦ baseChangeCone_π_app_fst X (Cone.mk S α) (B.f k.1) j) a
    refine ⟨j, ?_⟩
    rw [← ha]
    exact (smooth_snd_target_iff a (X.map j.hom) (B.f k.1)).mpr hj
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

end AlgebraicGeometry.Scheme
