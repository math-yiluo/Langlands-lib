import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotientStatement

/-! # The arrow scheme of a group action and its smooth projections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotient

variable {S : Scheme.{u}} {G : GroupScheme S} {V : Over S} (a : SchemeAction G V)

/-- The action graph `(g, v) ↦ (g.v, v)` of `a`. -/
abbrev graph : G.X ⊗ V ⟶ V ⊗ V := lift a.hom (snd G.X V)

/-- The stabilizer scheme of `a`: the base change of the graph along the diagonal. -/
abbrev stabilizer : Over S := Limits.pullback (graph a) (lift (𝟙 V) (𝟙 V))

/-- The projection of the stabilizer scheme to `V`. -/
abbrev stabilizerProj : stabilizer a ⟶ V := pullback.snd (graph a) (lift (𝟙 V) (𝟙 V))

/-- The action map evaluated on a point of the product. -/
lemma act_fst_snd {T : Over S} (m : T ⟶ G.X ⊗ V) :
    a.act (m ≫ fst G.X V) (m ≫ snd G.X V) = m ≫ a.hom := by
  rw [SchemeAction.act, lift_comp_fst_snd]

/-- Two points of the product have the same graph image exactly when they have the same
image under the action and the same second component. -/
lemma comp_graph_eq_iff {T : Over S} (m m' : T ⟶ G.X ⊗ V) :
    m ≫ graph a = m' ≫ graph a ↔
      m ≫ a.hom = m' ≫ a.hom ∧ m ≫ snd G.X V = m' ≫ snd G.X V := by
  rw [comp_lift, comp_lift]
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· ≫ fst V V) h, by simpa using congrArg (· ≫ snd V V) h⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]

/-- A point of the stabilizer scheme is a point of the product whose action image and
second component are both its point of `V`. -/
lemma stabilizer_fst {T : Over S} (k : T ⟶ stabilizer a) :
    k ≫ pullback.fst _ _ ≫ a.hom = k ≫ stabilizerProj a ∧
      k ≫ pullback.fst _ _ ≫ snd G.X V = k ≫ stabilizerProj a := by
  have hw := congrArg (k ≫ ·) (pullback.condition (f := graph a) (g := lift (𝟙 V) (𝟙 V)))
  exact ⟨by simpa using congrArg (· ≫ fst V V) hw, by simpa using congrArg (· ≫ snd V V) hw⟩

/-- A point of the stabilizer scheme fixes its point of `V`. -/
lemma stabilizer_act {T : Over S} (k : T ⟶ stabilizer a) :
    a.act (k ≫ pullback.fst _ _ ≫ fst G.X V) (k ≫ stabilizerProj a) = k ≫ stabilizerProj a := by
  obtain ⟨h₁, h₂⟩ := stabilizer_fst a k
  conv_lhs => rw [← h₂]
  simpa only [Category.assoc] using (act_fst_snd a (k ≫ pullback.fst _ _)).trans
    (by simpa only [Category.assoc] using h₁)

variable {a} {R : Over S} {r s : R ⟶ G.X ⊗ V}

/-- Both legs of a pair of points with the same graph image have the same second
component and the same action image. -/
lemma arrow_eq (h : IsPullback r s (graph a) (graph a)) :
    r ≫ a.hom = s ≫ a.hom ∧ r ≫ snd G.X V = s ≫ snd G.X V :=
  (comp_graph_eq_iff a r s).mp h.w

/-- For a pair of points `(g, v)` and `(g', v)` with `g.v = g'.v`, the element
`g' g⁻¹` fixes `g.v`. -/
lemma act_arrow (h : IsPullback r s (graph a) (graph a)) :
    a.act ((s ≫ fst G.X V) * (r ≫ fst G.X V)⁻¹) (r ≫ a.hom) = r ≫ a.hom := by
  obtain ⟨h₁, h₂⟩ := arrow_eq h
  conv_lhs => rw [← act_fst_snd a r, ← a.act_mul, inv_mul_cancel_right, h₂, act_fst_snd]
  exact h₁.symm

/-- The point `(g' g⁻¹, g.v)` of the stabilizer attached to a pair of points
`(g, v)` and `(g', v)` with `g.v = g'.v`. -/
def arrowToStabilizer (h : IsPullback r s (graph a) (graph a)) : R ⟶ stabilizer a :=
  pullback.lift (lift ((s ≫ fst G.X V) * (r ≫ fst G.X V)⁻¹) (r ≫ a.hom)) (r ≫ a.hom) (by
    rw [comp_lift, comp_lift, lift_snd, Category.comp_id]
    exact congrArg (lift · (r ≫ a.hom)) (act_arrow h))

/-- The arrow scheme is the base change of the stabilizer projection along the action
map: `((g, v), (g', v)) ↦ ((g' g⁻¹, g.v), (g, v))`. -/
lemma isPullback_arrowToStabilizer (h : IsPullback r s (graph a) (graph a)) :
    IsPullback (arrowToStabilizer h) r (stabilizerProj a) a.hom := by
  have hw : arrowToStabilizer h ≫ stabilizerProj a = r ≫ a.hom := pullback.lift_snd _ _ _
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c ↦ h.lift c.snd (lift ((c.fst ≫ pullback.fst _ _ ≫ fst G.X V) * (c.snd ≫ fst G.X V))
      (c.snd ≫ snd G.X V)) ?_) ?_ ?_ ?_)
  · apply (comp_graph_eq_iff a _ _).mpr
    refine ⟨?_, by rw [lift_snd]⟩
    rw [← act_fst_snd a (lift _ _), lift_fst, lift_snd, a.act_mul, act_fst_snd, ← c.condition]
    exact (stabilizer_act a c.fst).symm
  · intro c
    obtain ⟨-, h₂⟩ := stabilizer_fst a c.fst
    apply pullback.hom_ext
    · rw [arrowToStabilizer, Category.assoc, pullback.lift_fst, comp_lift]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, MonObj.comp_mul, GrpObj.comp_inv, IsPullback.lift_snd_assoc,
          IsPullback.lift_fst_assoc, mul_inv_cancel_right, Category.assoc]
      · simp only [lift_snd, IsPullback.lift_fst_assoc, ← c.condition, Category.assoc, h₂]
    · simp only [arrowToStabilizer, Category.assoc, pullback.lift_snd,
        IsPullback.lift_fst_assoc, ← c.condition]
  · intro c
    exact h.lift_fst _ _ _
  · intro c n hn₁ hn₂
    obtain ⟨-, h₂⟩ := arrow_eq h
    apply h.hom_ext
    · rw [hn₂, h.lift_fst]
    · rw [h.lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, ← hn₁, ← hn₂, arrowToStabilizer, Category.assoc,
          pullback.lift_fst_assoc, MonObj.comp_mul, GrpObj.comp_inv,
          inv_mul_cancel_right]
      · simp only [lift_snd, ← hn₂, Category.assoc, h₂]

/-- The first projection of the arrow scheme is smooth when the stabilizer is. -/
lemma smooth_arrow_fst (h : IsPullback r s (graph a) (graph a))
    (hσ : Smooth (stabilizerProj a).left) : Smooth r.left :=
  MorphismProperty.of_isPullback (P := @Smooth) ((isPullback_arrowToStabilizer h).map
    (Over.forget S)) hσ

/-- The second projection of the arrow scheme is smooth when the stabilizer is. -/
lemma smooth_arrow_snd (h : IsPullback r s (graph a) (graph a))
    (hσ : Smooth (stabilizerProj a).left) : Smooth s.left :=
  smooth_arrow_fst h.flip hσ

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotient
