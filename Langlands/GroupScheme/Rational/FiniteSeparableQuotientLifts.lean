import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint
import Langlands.AlgebraicGeometry.SmoothEtaleLocalSections
import Langlands.GroupScheme.Dynamic.FlagQuotientFiber

/-! # Finite separable local lifts through smooth surjections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.AlgebraicGeometry

variable {F : Type u} [Field F]

/-- An actual point over a finite separable extension in the base field's universe. -/
structure FiniteSeparablePoint (T : Over (Spec (CommRingCat.of F))) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra F extension]
  [finiteDimensional : FiniteDimensional F extension]
  [separable : Algebra.IsSeparable F extension]
  point : specOver F extension ⟶ T

attribute [instance] FiniteSeparablePoint.field FiniteSeparablePoint.algebra
  FiniteSeparablePoint.finiteDimensional FiniteSeparablePoint.separable

/-- A nonempty smooth scheme over a field has a point over a finite
separable field extension in the same universe. -/
theorem exists_finiteSeparable_point_of_smooth
    (T : Over (Spec (CommRingCat.of F))) [Smooth T.hom] [Nonempty T.left] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      FiniteDimensional F L ∧ Algebra.IsSeparable F L ∧
        Nonempty (specOver F L ⟶ T) := by
  have : Surjective T.hom := by
    constructor
    intro x
    obtain ⟨z⟩ := ‹Nonempty T.left›
    exact ⟨z, Subsingleton.elim _ _⟩
  obtain ⟨V, e, s, he, hs, hfac⟩ := hasEtaleLocalSections_of_smooth T.hom
  let E : Over (Spec (CommRingCat.of F)) := Over.mk e
  have : Etale E.hom := he
  have : Nonempty E.left := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
    obtain ⟨z, -⟩ := hs.surj x
    exact ⟨z⟩
  let s' : E ⟶ T := Over.homMk s hfac
  obtain ⟨L, _, _, hL, hLs, ⟨w⟩⟩ := GaloisChartPoint.exists_separable_point E
  exact ⟨L, inferInstance, inferInstance, hL, hLs, ⟨w ≫ s'⟩⟩

/-- Choose the actual finite separable point supplied by smoothness and nonemptiness. -/
def finiteSeparablePointOfSmooth
    (T : Over (Spec (CommRingCat.of F))) [Smooth T.hom] [Nonempty T.left] :
    FiniteSeparablePoint T :=
  Classical.choice (by
    obtain ⟨L, hfield, halgebra, hfinite, hseparable, ⟨w⟩⟩ :=
      exists_finiteSeparable_point_of_smooth T
    exact ⟨{
      extension := L
      field := hfield
      algebra := halgebra
      finiteDimensional := hfinite
      separable := hseparable
      point := w }⟩)

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Dynamic

variable {F : Type u} [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    {Q : Over (Spec (CommRingCat.of F))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left]

/-- Every point of the target of a smooth surjection from a group scheme
lifts over some finite separable field extension. -/
theorem exists_finiteSeparable_quotient_lift
    (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      FiniteDimensional F L ∧ Algebra.IsSeparable F L ∧
        ∃ g : specOver F L ⟶ G.X, g ≫ q = toUnit (specOver F L) ≫ y := by
  let T := flagQuotientFiber G q y
  have : Smooth T.hom := by
    change Smooth (pullback.snd q.left y.left)
    infer_instance
  have : Nonempty T.left := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
    obtain ⟨z, -⟩ := (inferInstance : Surjective T.hom).surj x
    exact ⟨z⟩
  obtain ⟨L, _, _, hL, hLs, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.exists_finiteSeparable_point_of_smooth T
  refine ⟨L, inferInstance, inferInstance, hL, hLs,
    w ≫ flagQuotientFiberι G q y, ?_⟩
  rw [Category.assoc, flagQuotientFiberι_comp, comp_toUnit_assoc]

/-- Actual finite separable local-lift data, including its quotient-image equation. -/
def finiteSeparableQuotientLift
    (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q) :
    {p : Langlands.AlgebraicGeometry.FiniteSeparablePoint G.X //
      p.point ≫ q = toUnit (specOver F p.extension) ≫ y} :=
  Classical.choice (by
    obtain ⟨L, hfield, halgebra, hfinite, hseparable, g, hg⟩ :=
      exists_finiteSeparable_quotient_lift G q y
    exact ⟨⟨{
      extension := L
      field := hfield
      algebra := halgebra
      finiteDimensional := hfinite
      separable := hseparable
      point := g }, hg⟩⟩)

end Langlands.GroupScheme
