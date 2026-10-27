import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeEquationComparisonStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison

/-! # The isometric comparison with relative series modulo additional equations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K))

omit [CompleteSpace K] in
/-- The new coordinates of the scalar quotient satisfy the weighted monomial bound. -/
theorem newCoordinate_monomial_bound_equations (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (algebra K A s equations)
      (newCoordinate K A s equations) d‖ ≤ s.weight d :=
  monomialValue_norm_le_weight s (algebra K A s equations)
    (norm_one_le K (algebra K A s equations)) (newCoordinate K A s equations)
    (norm_newCoordinate_le K A s equations) d

/-- Evaluate relative series in the scalar quotient with additional equations. -/
def relativeEquationInverseEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra s A) (algebra K A s equations) :=
  evaluateCoefficientsHom s (baseMap K A s equations) (newCoordinate K A s equations)
    (norm_baseMap_le K A s equations) (newCoordinate_monomial_bound_equations K A s equations)

theorem norm_relativeEquationInverseEvaluation_le (f : GeneralizedTateAlgebra s A) :
    ‖relativeEquationInverseEvaluation K A s equations f‖ ≤ ‖f‖ :=
  norm_evaluateCoefficients_le s (baseMap K A s equations) (newCoordinate K A s equations)
    (norm_baseMap_le K A s equations) (newCoordinate_monomial_bound_equations K A s equations) f

@[simp] theorem relativeEquationInverseEvaluation_constant (a : A) :
    relativeEquationInverseEvaluation K A s equations (constantAlgHom s K A a) =
      baseMap K A s equations a :=
  evaluateCoefficients_constant s (baseMap K A s equations) (newCoordinate K A s equations) a

@[simp] theorem relativeEquationInverseEvaluation_X (j : Fin m) :
    relativeEquationInverseEvaluation K A s equations (X s A j) =
      newCoordinate K A s equations j :=
  evaluateCoefficients_X s (baseMap K A s equations) (newCoordinate K A s equations) j

/-- Reverse evaluation after scalar relative evaluation is the scalar presentation map. -/
theorem relativeEquationInverseEvaluation_comp_relativeSeriesEvaluation :
    (relativeEquationInverseEvaluation K A s equations).comp
        (relativeSeriesEvaluation K A s) =
      presentationMap K (algebra K A s equations) := by
  apply GeneralizedTateAlgebra.hom_ext (A.polyradius.append s) K (algebra K A s equations)
  intro i
  change relativeEquationInverseEvaluation K A s equations
    (relativeSeriesEvaluation K A s (X (A.polyradius.append s) K i)) =
      coordinate K (algebra K A s equations) i
  rw [relativeSeriesEvaluation_X]
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [relativeSeriesTuple_castAdd, relativeEquationInverseEvaluation_constant,
      baseMap_coordinate]
  · intro j
    rw [relativeSeriesTuple_natAdd, relativeEquationInverseEvaluation_X]
    rfl

@[simp] theorem relativeEquationInverseEvaluation_relativeSeriesEvaluation
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquationInverseEvaluation K A s equations (relativeSeriesEvaluation K A s f) =
      presentationMap K (algebra K A s equations) f :=
  congrArg (fun ψ : BoundedAlgHom K (GeneralizedTateAlgebra (A.polyradius.append s) K)
    (algebra K A s equations) => ψ f)
    (relativeEquationInverseEvaluation_comp_relativeSeriesEvaluation K A s equations)

/-- Reverse evaluation annihilates every evaluated additional equation. -/
theorem relativeEquationInverseEvaluation_relations :
    ∀ g ∈ relativeEquationRelations K A s equations,
      relativeEquationInverseEvaluation K A s equations g = 0 := by
  rintro _ ⟨f, hf, rfl⟩
  rw [relativeEquationInverseEvaluation_relativeSeriesEvaluation]
  exact presentationMap_equation K A s equations hf

/-- The reverse map from the relative equation quotient to the scalar quotient. -/
def relativeEquationInverse :
    BoundedAlgHom K (relativeEquationAlgebra K A s equations) (algebra K A s equations) :=
  RelativeRelations.descend K A s (relativeEquationRelations K A s equations)
    (algebra K A s equations) (relativeEquationInverseEvaluation K A s equations)
    (relativeEquationInverseEvaluation_relations K A s equations)

@[simp] theorem relativeEquationInverse_quotientMap (f : GeneralizedTateAlgebra s A) :
    relativeEquationInverse K A s equations
        (RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations) f) =
      relativeEquationInverseEvaluation K A s equations f := rfl

/-- The reverse map is contractive for the two actual quotient norms. -/
theorem norm_relativeEquationInverse_le (a : relativeEquationAlgebra K A s equations) :
    ‖relativeEquationInverse K A s equations a‖ ≤ ‖a‖ := by
  exact (RelativeRelations.norm_descend_le K A s (relativeEquationRelations K A s equations)
    (algebra K A s equations) (relativeEquationInverseEvaluation K A s equations)
    (relativeEquationInverseEvaluation_relations K A s equations) 1 zero_lt_one
    (fun f => by
      simpa only [one_mul] using norm_relativeEquationInverseEvaluation_le K A s equations f)
    a).trans_eq (one_mul _)

/-- The reverse map after the natural map is the scalar quotient identity. -/
@[simp] theorem relativeEquationInverse_map (a : algebra K A s equations) :
    relativeEquationInverse K A s equations (relativeEquationMap K A s equations a) = a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (algebra K A s equations) a
  exact relativeEquationInverseEvaluation_relativeSeriesEvaluation K A s equations f

/-- The natural map after reverse evaluation is the relative quotient map. -/
theorem relativeEquationMap_comp_inverseEvaluation :
    (relativeEquationMap K A s equations).comp
        (relativeEquationInverseEvaluation K A s equations) =
      RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations) := by
  apply relative_hom_ext
  · intro a
    change relativeEquationMap K A s equations
      (relativeEquationInverseEvaluation K A s equations (constantAlgHom s K A a)) =
        RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
          (constantAlgHom s K A a)
    rw [relativeEquationInverseEvaluation_constant, relativeEquationMap_baseMap,
      RelativeRelations.baseMap_apply]
  · intro j
    change relativeEquationMap K A s equations
      (relativeEquationInverseEvaluation K A s equations (X s A j)) =
        RelativeRelations.quotientMap K A s (relativeEquationRelations K A s equations)
          (X s A j)
    rw [relativeEquationInverseEvaluation_X, relativeEquationMap_newCoordinate]
    rfl

/-- The natural map after the reverse map is the relative quotient identity. -/
@[simp] theorem relativeEquationMap_inverse (a : relativeEquationAlgebra K A s equations) :
    relativeEquationMap K A s equations (relativeEquationInverse K A s equations a) = a := by
  obtain ⟨f, rfl⟩ := RelativeRelations.quotientMap_surjective K A s
    (relativeEquationRelations K A s equations) a
  rw [relativeEquationInverse_quotientMap]
  exact congrArg (fun ψ : BoundedAlgHom K (GeneralizedTateAlgebra s A)
    (relativeEquationAlgebra K A s equations) => ψ f)
    (relativeEquationMap_comp_inverseEvaluation K A s equations)

/-- The natural map is surjective. -/
theorem relativeEquationMap_surjective :
    Function.Surjective (relativeEquationMap K A s equations) :=
  fun a => ⟨relativeEquationInverse K A s equations a,
    relativeEquationMap_inverse K A s equations a⟩

/-- The natural map preserves the actual quotient norms exactly. -/
theorem norm_relativeEquationMap (a : algebra K A s equations) :
    ‖relativeEquationMap K A s equations a‖ = ‖a‖ := by
  apply le_antisymm (norm_relativeEquationMap_le K A s equations a)
  simpa only [relativeEquationInverse_map] using
    norm_relativeEquationInverse_le K A s equations (relativeEquationMap K A s equations a)

/-- The natural map is an isometry, including for zero quotients. -/
theorem isometry_relativeEquationMap : Isometry (relativeEquationMap K A s equations) :=
  AddMonoidHomClass.isometry_of_norm (relativeEquationMap K A s equations).toAlgHom
    (norm_relativeEquationMap K A s equations)

/-- The kernel of scalar evaluation into the relative equation quotient is exactly the
closed ideal of old relations and additional equations. -/
theorem relativeEquationEvaluation_eq_zero_iff
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquationEvaluation K A s equations f = 0 ↔
      f ∈ (algebra K A s equations).ideal := by
  have hk := presentationMap_eq_zero_iff K (algebra K A s equations) f
  have hz : relativeEquationInverse K A s equations
      (0 : relativeEquationAlgebra K A s equations) = 0 :=
    map_zero (relativeEquationInverse K A s equations).toAlgHom
  have hz' : relativeEquationMap K A s equations (0 : algebra K A s equations) = 0 :=
    map_zero (relativeEquationMap K A s equations).toAlgHom
  constructor
  · intro h
    apply hk.mp
    calc presentationMap K (algebra K A s equations) f
        = relativeEquationInverse K A s equations
            (relativeEquationEvaluation K A s equations f) :=
          (relativeEquationInverseEvaluation_relativeSeriesEvaluation K A s equations f).symm
      _ = 0 := by rw [h, hz]
  · intro h
    exact (relativeEquationMap_presentationMap K A s equations f).symm.trans
      ((congrArg (relativeEquationMap K A s equations) (hk.mpr h)).trans hz')

/-- The complete unchanged comparison statement with additional equations. -/
theorem relativeEquationComparison : RelativeEquationComparisonStatement.{u} := by
  intro K _ _ _ A m s equations
  exact ⟨relativeEquationMap_surjective K A s equations,
    isometry_relativeEquationMap K A s equations,
    relativeEquationEvaluation_eq_zero_iff K A s equations⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
