import Langlands.AlgebraicGeometry.PointTopology.RealApproximation
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.GroupScheme.BaseChangeReflection

/-! # Real approximation on open affine subschemes -/

noncomputable section

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- An affine open subscheme inherits real approximation from its ambient scheme. -/
theorem HasRealApproximation.of_isOpenImmersion
    {X Y : Over (Spec (CommRingCat.of ℚ))} [IsAffine X.left] [IsAffine Y.left]
    (hY : HasRealApproximation Y) (f : X ⟶ Y) [IsOpenImmersion f.left] :
    HasRealApproximation X := by
  let F : RingPoint ℚ X ℝ → RingPoint ℚ Y ℝ := fun p => p ≫ f
  have hF : IsOpenEmbedding F := by
    have h := isOpenEmbedding_schemePointMap ℚ ℝ f
    change @IsOpenEmbedding (RingPoint ℚ X ℝ) (RingPoint ℚ Y ℝ)
      (schemePointTopology ℚ X ℝ) (schemePointTopology ℚ Y ℝ) F at h
    rw [schemePointTopology_eq_affine ℚ X ℝ, schemePointTopology_eq_affine ℚ Y ℝ] at h
    exact h
  intro x
  apply mem_closure_iff.mpr
  intro W hW hx
  obtain ⟨_, ⟨y, hyW, rfl⟩, ⟨q, hq⟩⟩ :=
    mem_closure_iff.mp (hY (F x)) (F '' W) (hF.isOpenMap W hW) ⟨x, hx, rfl⟩
  let a := ringTestMap ℚ (Algebra.ofId ℚ ℝ)
  have ha : Function.Surjective a.left :=
    (Langlands.GroupScheme.fieldExtension_fpqc ℚ ℝ).1.surj
  have hq' : Set.range q.left ⊆ Set.range f.left := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := ha z
    refine ⟨y.left w, ?_⟩
    have h := congrArg (fun p : RingPoint ℚ Y ℝ => p.left w) hq
    change q.left (a.left w) = f.left (y.left w) at h
    rw [hw] at h
    exact h.symm
  let l := IsOpenImmersion.lift f.left q.left hq'
  have hl : l ≫ f.left = q.left := IsOpenImmersion.lift_fac f.left q.left hq'
  let p : RingPoint ℚ X ℚ := Over.homMk l (by
    rw [← Over.w f, ← Category.assoc, hl]
    exact Over.w q)
  have hp : p ≫ f = q := Over.OverMorphism.ext hl
  have he : p.changeRing (Algebra.ofId ℚ ℝ) = y := by
    apply hF.injective
    change (a ≫ p) ≫ f = F y
    rw [Category.assoc, hp]
    exact hq
  exact ⟨y, hyW, p, he⟩

end Langlands.AlgebraicGeometry.PointTopology
