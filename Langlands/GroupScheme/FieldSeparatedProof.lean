import Langlands.GroupScheme.FieldSeparatedStatement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group schemes over a field are separated -/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- In a cartesian monoidal category, the diagonal of a group object is the pullback of the
unit along the division map `(x, y) ↦ x * y⁻¹`. -/
lemma diagonal_isPullback_unit {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (fst G G / snd G G) η[G] := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst G G) ?_ ?_ ?_⟩⟩
  · rw [GrpObj.comp_div, lift_fst, lift_snd, div_self', Hom.one_def]
  · intro s
    have h : s.fst ≫ (fst G G / snd G G) = s.snd ≫ η[G] := s.condition
    rw [GrpObj.comp_div, toUnit_unique s.snd (toUnit _), ← Hom.one_def, div_eq_one] at h
    ext
    · simp
    · simp [h]
  · intro s
    exact toUnit_unique _ _
  · intro s m h₁ _
    rw [← h₁, Category.assoc, lift_fst, Category.comp_id]

/-- Over a base scheme with at most one point, the unit section of a group scheme is a closed
immersion, because it is a section of the structure morphism. -/
theorem unit_isClosedImmersion_of_subsingleton {S : Scheme.{u}} [Subsingleton S]
    (G : Langlands.GroupScheme S) : IsClosedImmersion η[G.X].left :=
  isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left η[G.X].w

/-- Every group scheme over the spectrum of an arbitrary field has separated structure
morphism. -/
theorem fieldSeparated : FieldSeparatedStatement.{u} := by
  intro k _ G
  have : Subsingleton (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have h := (diagonal_isPullback_unit G.X).map (Over.forget _)
  change IsPullback (pullback.diagonal G.X.hom) G.X.hom _ η[G.X].left at h
  exact ⟨MorphismProperty.of_isPullback h.flip (unit_isClosedImmersion_of_subsingleton G)⟩

end Langlands.GroupScheme
