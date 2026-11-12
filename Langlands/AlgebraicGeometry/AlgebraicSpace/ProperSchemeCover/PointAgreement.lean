import Langlands.AlgebraicGeometry.AlgebraicSpace.FibrePowerCoordinates

/-! # Agreement of two morphisms at a point

Two morphisms of schemes `f g : Y ⟶ Z` agree at a point `y` of `Y` when their composites with
the canonical morphism `Spec κ(y) ⟶ Y` are equal. Agreement at a point can be tested after
precomposition with any morphism hitting the point, and when `f` and `g` are morphisms over a
base `S` to a scheme separated over `S`, the agreement locus is closed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

/-- Two morphisms agree at a point `y`: their composites with `Spec κ(y) ⟶ Y` are equal. -/
def EqAt {Y Z : Scheme.{u}} (f g : Y ⟶ Z) (y : Y) : Prop :=
  Y.fromSpecResidueField y ≫ f = Y.fromSpecResidueField y ≫ g

theorem EqAt.comp_right {Y Z Z' : Scheme.{u}} {f g : Y ⟶ Z} {y : Y} (h : EqAt f g y)
    (k : Z ⟶ Z') : EqAt (f ≫ k) (g ≫ k) y := by
  unfold EqAt at h ⊢
  rw [reassoc_of% h]

theorem EqAt.symm {Y Z : Scheme.{u}} {f g : Y ⟶ Z} {y : Y} (h : EqAt f g y) : EqAt g f y :=
  Eq.symm h

theorem EqAt.trans {Y Z : Scheme.{u}} {f g h : Y ⟶ Z} {y : Y} (h₁ : EqAt f g y)
    (h₂ : EqAt g h y) : EqAt f h y :=
  Eq.trans h₁ h₂

theorem eqAt_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (y : Y) : EqAt f g y := by
  rw [h]; rfl

/-- Agreement at a point can be tested after precomposition with a morphism. -/
theorem eqAt_comp_iff {A Y Z : Scheme.{u}} (e : A ⟶ Y) (f g : Y ⟶ Z) (a : A) :
    EqAt (e ≫ f) (e ≫ g) a ↔ EqAt f g (e a) := by
  unfold EqAt
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  constructor
  · intro h
    exact Spec_map_field_cancel (e.residueFieldMap a).hom h
  · intro h
    rw [h]

/-- For morphisms over `S` to a scheme separated over `S`, the agreement locus is the range of
the equalizer. -/
theorem setOf_eqAt_eq_range {S : Scheme.{u}} {Y Z : Over S} [IsSeparated Z.hom] (f g : Y ⟶ Z) :
    {y | EqAt f.left g.left y} = Set.range (equalizer.ι f g).left := by
  ext y
  constructor
  · intro hy
    let T : Over S := Over.mk (Y.left.fromSpecResidueField y ≫ Y.hom)
    let yh : T ⟶ Y := Over.homMk (Y.left.fromSpecResidueField y)
    have hyh : yh ≫ f = yh ≫ g := Over.OverMorphism.ext hy
    refine ⟨(equalizer.lift yh hyh).left
      (show T.left from IsLocalRing.closedPoint (Y.left.residueField y)), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    exact Scheme.fromSpecResidueField_apply _ _
  · rintro ⟨e, rfl⟩
    change EqAt f.left g.left _
    rw [← eqAt_comp_iff, ← Over.comp_left, ← Over.comp_left, equalizer.condition]
    exact eqAt_of_eq rfl _

/-- For morphisms over `S` to a scheme separated over `S`, the agreement locus is closed. -/
theorem isClosed_setOf_eqAt {S : Scheme.{u}} {Y Z : Over S} [IsSeparated Z.hom]
    (f g : Y ⟶ Z) : IsClosed {y | EqAt f.left g.left y} := by
  rw [setOf_eqAt_eq_range]
  exact (equalizer.ι f g).left.isClosedEmbedding.isClosed_range

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
