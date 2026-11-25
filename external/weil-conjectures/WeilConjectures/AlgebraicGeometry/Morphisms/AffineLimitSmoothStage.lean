/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineSourceLimitSmoothStage
import WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual smoothness of a finitely presented model over affine transition limits

## References

* Stacks Project, Tag 0C0C, with Situation 081D
* Stacks Project, Tags 0CAQ and 01ZM
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem smooth_snd_comp {A B D E : Scheme.{u}}
    (p : A ⟶ B) (g : D ⟶ B) (f : E ⟶ D)
    [Smooth (pullback.snd p g)] : Smooth (pullback.snd p (f ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p g f]
  infer_instance

private theorem smooth_snd_source {A B D E : Scheme.{u}}
    (p : A ⟶ B) (g : D ⟶ B) (e : E ⟶ A) [IsOpenImmersion e]
    [Smooth (pullback.snd p g)] : Smooth (pullback.snd (e ≫ p) g) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd p g e]
  infer_instance

/-- A finitely presented model whose limit base change is smooth becomes smooth later. -/
theorem exists_smooth_stage_of_affine_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    {i : I} {P : Scheme.{u}} (p : P ⟶ X.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (c : C ⟶ S) [Smooth c] (a : C ⟶ P)
    (H : IsPullback a c p (α.app i)) :
    ∃ j : Over i, Smooth (pullback.snd p (X.map j.hom)) := by
  classical
  have : IsNoetherian (X.obj i) := hN i
  have : QuasiSeparatedSpace (X.obj i) := hqs i
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : Smooth (pullback.snd p (α.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let U := P.affineCover.finiteSubcover
  have hUaff (k : U.I₀) : IsAffine (U.X k) := by
    dsimp [U]
    rw [OpenCover.finiteSubcover_X]
    infer_instance
  have hstage (k : U.I₀) :
      ∃ j : Over i, Smooth (pullback.snd (U.f k ≫ p) (X.map j.hom)) := by
    have : IsAffine (U.X k) := hUaff k
    have : Smooth (pullback.snd (U.f k ≫ p) (α.app i)) :=
      smooth_snd_source p (α.app i) (U.f k)
    exact exists_smooth_stage_of_affine_source_limit X α hα hXa hN hqs (U.f k ≫ p)
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
    exact smooth_snd_comp (U.f k ≫ p) (X.map (js k).hom) (X.map f.left)
  change Smooth (pullback.snd (U.f k) (pullback.fst p (X.map j.hom)) ≫
    pullback.snd p (X.map j.hom))
  rw [← pullbackRightPullbackFstIso_hom_snd p (X.map j.hom) (U.f k)]
  infer_instance

end AlgebraicGeometry.Scheme
