import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Action.Basic

/-!
# Filtered colimits of module complexes

These proposition definitions state the algebraic passage to a filtered
direct limit used in Harris 1999, Section 2. They use the constructed colimit
and its canonical map to cohomology; invertibility is a conclusion.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v w

/-- Filtered colimits preserve short exact sequences of module diagrams.
No exactness of the colimit functor is supplied as a hypothesis. -/
def FilteredColimitExactnessStatement (R : Type u) [Ring R] : Prop :=
  ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
    (S : ShortComplex (J ⥤ ModuleCat.{v} R)),
    S.ShortExact →
      (S.map (colim : (J ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact

/-- The canonical map from the filtered colimit of cohomology modules to
cohomology of the colimit complex is invertible in every integer degree. -/
def FilteredColimitCohomologyStatement (R : Type u) [Ring R] : Prop :=
  ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
    (K : J ⥤ CochainComplex (ModuleCat.{v} R) ℤ) (q : ℤ),
    IsIso (colimit.post K
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q))

/-- The canonical cohomology comparison is natural in the diagram.
This equality of maps does not require filteredness. -/
def ColimitCohomologyNaturalityStatement (R : Type u) [Ring R] : Prop :=
  ∀ (J : Type v) [SmallCategory J]
    (K L : J ⥤ CochainComplex (ModuleCat.{v} R) ℤ) (f : K ⟶ L) (q : ℤ),
    colimit.post K
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q).map
        (colimMap f) =
      colimMap (Functor.whiskerRight f
          (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)) ≫
        colimit.post L
          (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)

/-- A pointwise quasi-isomorphism of filtered diagrams of module complexes
induces a quasi-isomorphism of their actual colimit complexes. -/
def FilteredColimitQuasiIsoStatement (R : Type u) [Ring R] : Prop :=
  ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
    (K L : J ⥤ CochainComplex (ModuleCat.{v} R) ℤ) (f : K ⟶ L),
    (∀ j : J, QuasiIso (f.app j)) → QuasiIso (colimMap f)

/-- For an algebraic monoid action by natural transformations on a diagram,
the canonical filtered-colimit comparison is an isomorphism of actions.
Smoothness and continuity are separate assertions. -/
def FilteredColimitCohomologyEquivarianceStatement (R : Type u) [Ring R] : Prop :=
  ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
    (G : Type w) [Monoid G]
    (K : Action (J ⥤ CochainComplex (ModuleCat.{v} R) ℤ) G) (q : ℤ),
    ∃ e :
        ((((Functor.whiskeringRight J _ _).obj
            (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
              (ComplexShape.up ℤ) q)) ⋙ colim).mapAction G).obj K ≅
          ((colim ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
              (ComplexShape.up ℤ) q).mapAction G).obj K,
      e.hom.hom = colimit.post K.V
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q)

/-- The exactness and canonical cohomology-comparison family.
No component proposition is assumed to define this conjunction. -/
def FilteredColimitComparisonStatements (R : Type u) [Ring R] : Prop :=
  FilteredColimitExactnessStatement.{u, v} R ∧
  FilteredColimitCohomologyStatement.{u, v} R ∧
  ColimitCohomologyNaturalityStatement.{u, v} R ∧
  FilteredColimitQuasiIsoStatement.{u, v} R ∧
  FilteredColimitCohomologyEquivarianceStatement.{u, v, w} R

end Langlands.Cohomology
