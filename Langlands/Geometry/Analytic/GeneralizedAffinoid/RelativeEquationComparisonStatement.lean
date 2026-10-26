import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelations

/-! # Comparison with relative weighted series modulo additional equations: target -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

section Construction

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K))

/-- The supplied scalar equations evaluated in the actual relative series algebra. -/
def relativeEquationRelations : Set (GeneralizedTateAlgebra s A) :=
  relativeSeriesEvaluation K A s '' equations

/-- The actual relative series quotient by the closed ideal of evaluated equations. -/
abbrev relativeEquationAlgebra :=
  RelativeRelations.QuotientAlgebra K A s (relativeEquationRelations K A s equations)

/-- Scalar evaluation followed by the actual relative equation quotient map. -/
def relativeEquationEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra (A.polyradius.append s) K)
      (relativeEquationAlgebra K A s equations) :=
  (RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)).comp
    (relativeSeriesEvaluation K A s)

@[simp] theorem relativeEquationEvaluation_apply
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquationEvaluation K A s equations f =
      RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
        (relativeSeriesEvaluation K A s f) := rfl

theorem norm_relativeEquationEvaluation_le
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    ‖relativeEquationEvaluation K A s equations f‖ ≤ ‖f‖ :=
  (RelativeRelations.norm_quotientMap_le K A s
    (relativeEquationRelations K A s equations) _).trans
      (norm_relativeSeriesEvaluation_le K A s f)

/-- Evaluation on old variables agrees with the relative quotient's coefficient map. -/
@[simp] theorem relativeEquationEvaluation_appendLeft
    (f : GeneralizedTateAlgebra A.polyradius K) :
    relativeEquationEvaluation K A s equations (appendLeft A.polyradius s K f) =
      RelativeRelations.baseMap K A s (relativeEquationRelations K A s equations)
        (presentationMap K A f) := by
  change RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
      (relativeSeriesEvaluation K A s (appendLeft A.polyradius s K f)) =
    RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
      (constantAlgHom s K A (presentationMap K A f))
  rw [relativeSeriesEvaluation_appendLeft]

/-- Every supplied extra scalar equation vanishes after relative quotienting. -/
@[simp] theorem relativeEquationEvaluation_equation
    {f : GeneralizedTateAlgebra (A.polyradius.append s) K} (hf : f ∈ equations) :
    relativeEquationEvaluation K A s equations f = 0 :=
  RelativeRelations.quotientMap_equation K A s
    (relativeEquationRelations K A s equations) ⟨f, hf, rfl⟩

/-- Both the included old ideal and the supplied extra equations vanish. -/
theorem relativeEquationEvaluation_relations
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K)
    (hf : f ∈ relations K A s equations) :
    relativeEquationEvaluation K A s equations f = 0 := by
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · rw [relativeEquationEvaluation_appendLeft,
      (presentationMap_eq_zero_iff K A g).mpr hg, map_zero]
  · exact relativeEquationEvaluation_equation K A s equations hf

/-- The natural map from scalar variable adjunction with equations to the relative quotient. -/
def relativeEquationMap :
    BoundedAlgHom K (algebra K A s equations) (relativeEquationAlgebra K A s equations) :=
  descendRelations K (A.arity + m) (A.polyradius.append s) (relations K A s equations)
    (relativeEquationAlgebra K A s equations) (relativeEquationEvaluation K A s equations)
    (relativeEquationEvaluation_relations K A s equations)

@[simp] theorem relativeEquationMap_presentationMap
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquationMap K A s equations
        (presentationMap K (algebra K A s equations) f) =
      relativeEquationEvaluation K A s equations f := rfl

theorem relativeEquationMap_comp_presentationMap :
    (relativeEquationMap K A s equations).comp
        (presentationMap K (algebra K A s equations)) =
      relativeEquationEvaluation K A s equations :=
  BoundedAlgHom.ext fun _ => rfl

/-- The natural map is contractive for the two actual quotient norms. -/
theorem norm_relativeEquationMap_le (a : algebra K A s equations) :
    ‖relativeEquationMap K A s equations a‖ ≤ ‖a‖ := by
  exact (norm_descendRelations_le K (A.arity + m) (A.polyradius.append s)
    (relations K A s equations) (relativeEquationAlgebra K A s equations)
    (relativeEquationEvaluation K A s equations)
    (relativeEquationEvaluation_relations K A s equations) 1 zero_lt_one
    (fun f => by simpa only [one_mul] using
      norm_relativeEquationEvaluation_le K A s equations f) a).trans_eq (one_mul _)

@[simp] theorem relativeEquationMap_baseMap (a : A) :
    relativeEquationMap K A s equations (baseMap K A s equations a) =
      RelativeRelations.baseMap K A s (relativeEquationRelations K A s equations) a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [baseMap_presentationMap, relativeEquationMap_presentationMap,
    relativeEquationEvaluation_appendLeft]

@[simp] theorem relativeEquationMap_newCoordinate (j : Fin m) :
    relativeEquationMap K A s equations (newCoordinate K A s equations j) =
      RelativeRelations.newCoordinate K A s
        (relativeEquationRelations K A s equations) j := by
  change RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
      (relativeSeriesEvaluation K A s
        (X (A.polyradius.append s) K (Fin.natAdd A.arity j))) =
    RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
      (X s A j)
  rw [relativeSeriesEvaluation_X, relativeSeriesTuple_natAdd]

end Construction

/-- The natural comparison is a surjective isometry, and scalar evaluation has
exactly the full closed ideal of old and additional relations as its kernel. -/
def RelativeEquationComparisonStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (m : ℕ) (s : PositivePolyradius (Fin m))
    (equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K)),
    Function.Surjective (relativeEquationMap K A s equations) ∧
    Isometry (relativeEquationMap K A s equations) ∧
    (∀ f : GeneralizedTateAlgebra (A.polyradius.append s) K,
      relativeEquationEvaluation K A s equations f = 0 ↔
        f ∈ (algebra K A s equations).ideal)

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
