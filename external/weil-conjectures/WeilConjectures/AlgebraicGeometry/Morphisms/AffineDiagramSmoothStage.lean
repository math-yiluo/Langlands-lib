/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.RingTheory.SmoothPushoutFilteredColimitStage

/-!
# Smoothness of an affine model over an affine inverse system

## References

* Stacks Project, Tags 0C0C, 0CAQ and 01ZM(2)-(3)
* Stacks Project, Tag 0C0C, affine case, using Tags 0CAQ and 01ZM(2)-(3)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Smoothness of a fixed finitely presented affine model descends along an affine system. -/
theorem exists_smooth_stage_of_affine_diagram {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ j, IsAffine (D.obj j))
    {Q P : Scheme.{u}} [IsAffine Q] [IsAffine P]
    (t : D ⟶ (Functor.const I).obj Q) (s : c.pt ⟶ Q)
    (hs : ∀ j, c.π.app j ≫ t.app j = s)
    (p : P ⟶ Q) [LocallyOfFinitePresentation p]
    [Smooth (pullback.snd p s)] :
    ∃ j, Smooth (pullback.snd p (t.app j)) := by
  have (j : I) : IsAffine (D.obj j) := hD j
  have : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f) := fun f ↦ inferInstance
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let F := D.op ⋙ Scheme.Γ
  let d := Scheme.Γ.mapCocone c.op
  let tR : (Functor.const Iᵒᵖ).obj Γ(Q, ⊤) ⟶ F :=
    { app := fun j ↦ (t.app j.unop).appTop
      naturality := fun j k f ↦ by
        dsimp [F]
        rw [Category.id_comp, ← Scheme.Hom.comp_appTop]
        congr 1
        simp only [Functor.const_obj_obj] at *
        exact (t.naturality f.unop).symm }
  have hsR (j : Iᵒᵖ) : tR.app j ≫ d.ι.app j = s.appTop := by
    change (t.app j.unop).appTop ≫ (c.π.app j.unop).appTop = _
    rw [← Scheme.Hom.comp_appTop, hs]
  have hp := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)
    (f := p)).mp ‹_›
  have hsm := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)
    (f := pullback.snd p s)).mp ‹_›
  obtain ⟨j, hj⟩ := CommRingCat.exists_smooth_pushout_stage F d
    (nonempty_isColimit_Γ_mapCocone D c hc).some p.appTop hp tR s.appTop hsR
    (fun j ↦ Γ(pullback p (t.app j.unop), ⊤))
    (fun j ↦ (pullback.fst p (t.app j.unop)).appTop)
    (fun j ↦ (pullback.snd p (t.app j.unop)).appTop)
    (fun j ↦ isPushout_appTop_of_isPullback (IsPullback.of_hasPullback p (t.app j.unop)))
    (pullback.fst p s).appTop (pullback.snd p s).appTop
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback p s)) hsm
  exact ⟨j.unop, (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mpr hj⟩

end AlgebraicGeometry.Scheme
