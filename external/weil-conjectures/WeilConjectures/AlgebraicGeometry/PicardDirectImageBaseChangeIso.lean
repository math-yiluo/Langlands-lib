/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapPasting
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso

/-! # Invertibility of the non-iterated direct-image base-change map
Source: Stacks Project, Tags 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

private theorem baseChange_isIso_of_iso_top {A B A' A'' T : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ T) (p'' : A'' ⟶ T) (h : T ⟶ B) (v : A' ⟶ A)
    (e : A'' ≅ A') (w : v ≫ p = p' ≫ h) (we : e.hom ≫ p' = p'') (F : A.Modules)
    (hbc : IsIso (Modules.moduleBaseChangeMap p p' h v w F)) :
    IsIso (Modules.moduleBaseChangeMap p p'' h (e.hom ≫ v)
      (by rw [Category.assoc, w, ← Category.assoc, we]) F) := by
  have w' : e.hom ≫ p' = p'' ≫ 𝟙 T := by simpa only [Category.comp_id] using we
  have hrange : Set.range e.hom = p' ⁻¹' Set.range (𝟙 T) := by
    have hs : Function.Surjective e.hom := by
      intro x
      refine ⟨e.inv x, ?_⟩
      exact congrArg (fun k : A' ⟶ A' ↦ k x) e.inv_hom_id
    rw [Set.range_eq_univ.mpr hs]
    change Set.univ = p' ⁻¹' Set.range (id : T → T)
    rw [Set.range_id, Set.preimage_univ]
  have hi : IsIso (Modules.moduleBaseChangeMap p' p'' (𝟙 T) e.hom w'
      ((Modules.tensorPullback v).obj F)) :=
    Modules.moduleBaseChangeMap_open_square_isIso p' p'' (𝟙 T) e.hom w' hrange _
  have hout : IsIso (Modules.moduleBaseChangeMap p p'' (𝟙 T ≫ h) (e.hom ≫ v)
      ((Category.assoc e.hom v p).trans
        ((congrArg (fun k ↦ e.hom ≫ k) w).trans
          ((Category.assoc e.hom p' h).symm.trans
            ((congrArg (fun k ↦ k ≫ h) w').trans (Category.assoc p'' (𝟙 T) h))))) F) := by
    rw [Modules.moduleBaseChangeMap_pasting p p' p'' h v (𝟙 T) e.hom w w' F]
    infer_instance
  have heq : 𝟙 T ≫ h = h := Category.id_comp h
  cases heq
  exact hout

/-- Invertibility of the iterated cartesian base-change map implies invertibility
of the canonical map to the non-iterated fibre product.

Source: Stacks Project, Tag 08HY (canonical base change) and Tag 0BDP
(compatibility with arbitrary change of base).
(blueprint: lem-sc-picard-direct-image-base-change-iso)

Proof: Paste the pullback squares for f and j with the square for p_W and h.
The resulting pullback cone is canonically isomorphic to X_T. The top projection
under this isomorphism is picardBaseChangeTop f j h. Pushforward along this
scheme isomorphism is an equivalence, with inverse pushforward along its inverse.
Use uniqueness of left adjoints to compare the two tensor pullbacks. Taking
adjoints of the two base-change maps identifies their defining pushforwards of
the pullback units, by naturality of the unit and the sectionwise composition
identifications of pushforward. Hence the non-iterated map is the iterated map
followed by the pushforward and tensor-composition isomorphisms. Every factor is
invertible, so the displayed map is invertible. This applies to arbitrary M,
without finite local freeness or flatness; empty fibre products cause no change. -/
theorem picardDirectImageBaseChangeMap_isIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules)
    (hbc : IsIso (Modules.moduleBaseChangeMap (pullback.snd f j)
      (pullback.snd (pullback.snd f j) h) h (pullback.fst (pullback.snd f j) h)
      pullback.condition ((Modules.tensorPullback (pullback.fst f j)).obj M))) :
    IsIso (Modules.picardDirectImageBaseChangeMap f j h M)  := by
  let p := pullback.snd f j
  let pi := pullback.snd p h
  let vi := pullback.fst p h
  let pt := pullback.snd f (h ≫ j)
  let v := Modules.picardBaseChangeTop f j h
  let sq := (IsPullback.of_hasPullback p h).paste_horiz (IsPullback.of_hasPullback f j)
  let e := sq.isoPullback.symm
  have he : e.hom ≫ pi = pt := sq.isoPullback_inv_snd
  have hv : e.hom ≫ vi = v := by
    apply pullback.hom_ext
    · dsimp [v, Modules.picardBaseChangeTop]
      rw [pullback.lift_fst]
      exact sq.isoPullback_inv_fst
    · rw [Category.assoc, pullback.condition, ← Category.assoc, he]
      dsimp [v, Modules.picardBaseChangeTop]
      rw [pullback.lift_snd]
  have hi : IsIso (Modules.moduleBaseChangeMap p pt h v
      (by dsimp [v, Modules.picardBaseChangeTop]; rw [pullback.lift_snd])
      ((Modules.tensorPullback (pullback.fst f j)).obj M)) := by
    have hh := baseChange_isIso_of_iso_top p pi pt h vi e pullback.condition he
      ((Modules.tensorPullback (pullback.fst f j)).obj M) hbc
    have hall : ∀ w' : (e.hom ≫ vi) ≫ p = pt ≫ h,
        IsIso (Modules.moduleBaseChangeMap p pt h (e.hom ≫ vi) w'
          ((Modules.tensorPullback (pullback.fst f j)).obj M)) := fun _ ↦ hh
    have htransport := congrArg (fun v' ↦ ∀ w' : v' ≫ p = pt ≫ h,
      IsIso (Modules.moduleBaseChangeMap p pt h v' w'
        ((Modules.tensorPullback (pullback.fst f j)).obj M))) hv
    exact (htransport.mp hall) _
  dsimp only [Modules.picardDirectImageBaseChangeMap]
  infer_instance

end AlgebraicGeometry.Scheme
