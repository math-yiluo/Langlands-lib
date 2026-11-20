import Langlands.GroupScheme.ClosedFiniteSubschemeStabilizer

/-! # Conjugation stabilizers under base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} (b : T ⟶ S) {G : GroupScheme S}
  {Z : Over S} {Z' : Over T} (z : Z ⟶ G.X) (z' : Z' ⟶ ((baseChange b).obj G).X)
  (k : Z'.left ⟶ Z.left) (hk : IsPullback k Z'.hom Z.hom b)
  (hz : z'.left ≫ pullback.fst G.X.hom b = k ≫ z.left)

include hk hz in
/-- An actual pullback square identifies factoring points after arbitrary base change. -/
theorem mem_schemePointRange_baseChange_iff {U : Over T}
    (x : U ⟶ ((baseChange b).obj G).X) :
    x ∈ schemePointRange z' U ↔
      baseChangePointsEquiv b G U x ∈ schemePointRange z ((Over.map b).obj U) := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Over.homMk (y.left ≫ k) ?_, ?_⟩
    · change (y.left ≫ k) ≫ Z.hom = U.hom ≫ b
      rw [Category.assoc, hk.w, ← Category.assoc, y.w]
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, baseChangePointsEquiv_left, Category.assoc, hz]
  · rintro ⟨y, hy⟩
    have hw : y.left ≫ Z.hom = U.hom ≫ b := y.w
    let h := hk.lift y.left U.hom hw
    refine ⟨Over.homMk h (hk.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    change h ≫ z'.left = x.left
    apply pullback.hom_ext
    · rw [Category.assoc, hz, ← Category.assoc, hk.lift_fst]
      exact congrArg (fun p : (Over.map b).obj U ⟶ G.X => p.left) hy
    · rw [Category.assoc, show z'.left ≫ pullback.snd G.X.hom b = Z'.hom from z'.w,
        hk.lift_snd]
      exact x.w.symm

private theorem schemePointRange_comp {Z : Over S} (z : Z ⟶ G.X)
    {V W : Over S} (a : W ⟶ V) {x : V ⟶ G.X} (hx : x ∈ schemePointRange z V) :
    a ≫ x ∈ schemePointRange z W := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨a ≫ y, Category.assoc _ _ _⟩

/-- Conjugation stabilizers commute with the base change of the subscheme they stabilize. -/
def ConjugationStabilizerBaseChangeStatement : Prop :=
  ∀ {S T : Scheme.{u}} (b : T ⟶ S) {G : GroupScheme S} {Z : Over S} {Z' : Over T}
    (z : Z ⟶ G.X) (z' : Z' ⟶ ((baseChange b).obj G).X) (k : Z'.left ⟶ Z.left),
    IsPullback k Z'.hom Z.hom b →
    z'.left ≫ pullback.fst G.X.hom b = k ≫ z.left →
    (conjugationStabilizer z).baseChange b = conjugationStabilizer z'

set_option maxHeartbeats 800000 in
theorem conjugationStabilizerBaseChange : ConjugationStabilizerBaseChangeStatement.{u} := by
  intro S T b G Z Z' z z' k hk hz
  have hpoint := @mem_schemePointRange_baseChange_iff S T b G Z Z' z z' k hk hz
  apply le_antisymm
  · intro U g hg V a x hx
    change baseChangePointsEquiv b G U g ∈ (conjugationStabilizer z).carrier _ at hg
    have h := hg ((Over.map b).obj V) ((Over.map b).map a) (baseChangePointsEquiv b G V x)
      ((hpoint x).mp hx)
    refine ⟨(hpoint _).mpr ?_, (hpoint _).mpr ?_⟩
    · simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality] using h.1
    · simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality] using h.2
  · intro U g hg
    change baseChangePointsEquiv b G U g ∈ (conjugationStabilizer z).carrier _
    intro V a x hx
    let W : Over T := Over.mk (a.left ≫ U.hom)
    let e : (Over.map b).obj W ≅ V := Over.isoMk (Iso.refl _) (by
      change (𝟙 V.left) ≫ V.hom = (a.left ≫ U.hom) ≫ b
      have hw : a.left ≫ (U.hom ≫ b) = V.hom := a.w
      simpa only [Category.id_comp, Category.assoc] using hw.symm)
    let a' : W ⟶ U := Over.homMk a.left rfl
    let y := (baseChangePointsEquiv b G W).symm (e.hom ≫ x)
    have hy : y ∈ schemePointRange z' W := (hpoint y).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact schemePointRange_comp z e.hom hx)
    have h := hg W a' y hy
    have ha : (Over.map b).map a' = e.hom ≫ a := by
      apply Over.OverMorphism.ext
      change a.left = (𝟙 V.left) ≫ a.left
      exact (Category.id_comp _).symm
    have h₁ : e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g) * x *
        (a ≫ baseChangePointsEquiv b G U g)⁻¹) ∈ schemePointRange z _ := by
      simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality, y, MulEquiv.apply_symm_apply,
        ha, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using (hpoint _).mp h.1
    have h₂ : e.hom ≫ ((a ≫ baseChangePointsEquiv b G U g)⁻¹ * x *
        (a ≫ baseChangePointsEquiv b G U g)) ∈ schemePointRange z _ := by
      simpa only [map_mul, map_inv, baseChangePointsEquiv_naturality, y, MulEquiv.apply_symm_apply,
        ha, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using (hpoint _).mp h.2
    exact ⟨by simpa only [Iso.inv_hom_id_assoc] using schemePointRange_comp z e.inv h₁,
      by simpa only [Iso.inv_hom_id_assoc] using schemePointRange_comp z e.inv h₂⟩

end Langlands.GroupScheme
