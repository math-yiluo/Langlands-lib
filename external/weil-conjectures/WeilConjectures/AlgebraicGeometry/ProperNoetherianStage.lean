/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import Mathlib.CategoryTheory.Presentable.Directed

/-! # A proper finitely presented scheme descends to a proper stage -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A proper finitely presented scheme over a Noetherian approximation descends to
one proper stage, with its pullback square retained.
Source: Stacks Project, Limits, Tags 01ZM and 081F, as used in Tag 0A0P.
(blueprint: lem-weil-pbc-proper-noetherian-stage)
Proof: reindex N by a nonempty directed set using Tag 0032. Apply
finite-presentation descent to its limiting cone. This gives a finitely presented
stage morphism p and a cartesian square with g.
The stage source is qcqs because p is finitely presented and the base is Noetherian.
Apply properness descent (081F) to p and the identity of its base: its limit base
change is g, hence proper. Pull back p to the stage supplied by 081F. Properness
holds there; finite presentation is preserved by base change. Pasting pullback
squares gives the displayed square with g and the original approximation leg.
The resulting stage in the directed reindexing is an object of N.I. -/
theorem exists_proper_noetherian_stage
    {Y S : Scheme.{u}} (g : Y ⟶ S) [IsProper g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (N : S.NoetherianApproximation) :
    ∃ (a : N.I) (Y₀ : Scheme.{u}) (p : Y₀ ⟶ N.D.obj a) (h : Y ⟶ Y₀),
      IsProper p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
        QuasiSeparated p ∧ IsPullback h g p (N.π.app a) := by
  classical
  obtain ⟨A, horder, hdir, hne, F, hfinal⟩ := IsFiltered.exists_directed N.Iᵒᵖ
  let := horder
  let := hfinal
  let R := F.leftOp
  let D := R ⋙ N.D
  let π := Functor.whiskerLeft R N.π
  let c := Cone.mk S π
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv R (Cone.mk S N.π)).symm N.isLimit
  have (j : Aᵒᵖ) : CompactSpace (D.obj j) := N.compactSpace_obj _
  have (j : Aᵒᵖ) : QuasiSeparatedSpace (D.obj j) := by
    change QuasiSeparatedSpace (N.D.obj (R.obj j))
    infer_instance
  have {j k : Aᵒᵖ} (b : j ⟶ k) : IsAffineHom (D.map b) :=
    N.isAffineHom_map (R.map b)
  obtain ⟨j, Y₀, p, hfp, hqc, hqs, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hc g
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated p
  have hs : IsProper (pullback.snd p (c.π.app j)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let ψ := pullback.map p (c.π.app j) (𝟙 (D.obj j)) (c.π.app j)
    p (𝟙 S) (𝟙 (D.obj j)) (Category.comp_id p)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hψ : IsProper ψ := by
    have he : ψ ≫ pullback.snd (𝟙 (D.obj j)) (c.π.app j) =
        pullback.snd p (c.π.app j) := by
      dsimp [ψ]
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he] at hs
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp hs
  obtain ⟨l, hjl, hl⟩ := exists_isProper_baseChange_of_isLimit D c hc j.unop
    p (𝟙 (D.obj j)) p (by simp) hψ
  let t := D.map (homOfLE hjl).op
  let p' := pullback.snd p t
  have hp' : IsProper p' := by
    have he :
        (pullback.map p t (𝟙 (D.obj j)) t p (𝟙 (D.obj (Opposite.op l)))
          (𝟙 (D.obj j)) (Category.comp_id p) (Category.comp_id t)) ≫
            pullback.snd (𝟙 (D.obj j)) t = p' := by
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he]
    have := hl
    infer_instance
  let h' : Y ⟶ pullback p t := pullback.lift h (g ≫ c.π.app (Opposite.op l)) (by
    rw [Category.assoc, c.w (homOfLE hjl).op, H.w])
  have H' : IsPullback h' g p' (c.π.app (Opposite.op l)) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback p t)
    · rw [show h' ≫ pullback.fst p t = h from pullback.lift_fst _ _ _]
      change IsPullback h g p (c.π.app (Opposite.op l) ≫ D.map (homOfLE hjl).op)
      rw [c.w]
      exact H
    · simp only [h', p', pullback.lift_snd]
  exact ⟨R.obj (Opposite.op l), pullback p t, p', h', hp', inferInstance,
    inferInstance, inferInstance, H'⟩

end AlgebraicGeometry
