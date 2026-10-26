import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparisonStatement
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation

/-! # The isometric comparison between variable adjunction and relative series -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))

omit [CompleteSpace K] in
/-- The new quotient coordinates satisfy the exact weighted monomial bound. -/
theorem newCoordinate_monomial_bound (d : Fin m →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (algebra K A s ∅)
      (newCoordinate K A s ∅) d‖ ≤ s.weight d :=
  monomialValue_norm_le_weight s (algebra K A s ∅) (norm_one_le K (algebra K A s ∅))
    (newCoordinate K A s ∅) (norm_newCoordinate_le K A s ∅) d

/-- Evaluate relative series back in the actual enlarged quotient. -/
def relativeSeriesInverse :
    BoundedAlgHom K (GeneralizedTateAlgebra s A) (algebra K A s ∅) :=
  evaluateCoefficientsHom s (baseMap K A s ∅) (newCoordinate K A s ∅)
    (norm_baseMap_le K A s ∅) (newCoordinate_monomial_bound K A s)

/-- Reverse evaluation is contractive for the weighted and quotient norms. -/
theorem norm_relativeSeriesInverse_le (f : GeneralizedTateAlgebra s A) :
    ‖relativeSeriesInverse K A s f‖ ≤ ‖f‖ :=
  norm_evaluateCoefficients_le s (baseMap K A s ∅) (newCoordinate K A s ∅)
    (norm_baseMap_le K A s ∅) (newCoordinate_monomial_bound K A s) f

@[simp] theorem relativeSeriesInverse_constant (a : A) :
    relativeSeriesInverse K A s (constantAlgHom s K A a) = baseMap K A s ∅ a :=
  evaluateCoefficients_constant s (baseMap K A s ∅) (newCoordinate K A s ∅) a

@[simp] theorem relativeSeriesInverse_X (j : Fin m) :
    relativeSeriesInverse K A s (X s A j) = newCoordinate K A s ∅ j :=
  evaluateCoefficients_X s (baseMap K A s ∅) (newCoordinate K A s ∅) j

/-- Reverse evaluation after the forward map is the quotient identity. -/
theorem relativeSeriesInverse_comp_map :
    (relativeSeriesInverse K A s).comp (relativeSeriesMap K A s) =
      BoundedAlgHom.id K (algebra K A s ∅) := by
  have h : ((relativeSeriesInverse K A s).comp (relativeSeriesMap K A s)).comp
      (presentationMap K (algebra K A s ∅)) =
        presentationMap K (algebra K A s ∅) := by
    apply GeneralizedTateAlgebra.hom_ext (A.polyradius.append s) K (algebra K A s ∅)
    intro i
    change relativeSeriesInverse K A s
      (relativeSeriesEvaluation K A s (X (A.polyradius.append s) K i)) =
        coordinate K (algebra K A s ∅) i
    rw [relativeSeriesEvaluation_X]
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [relativeSeriesTuple_castAdd, relativeSeriesInverse_constant,
        baseMap_coordinate]
    · intro j
      rw [relativeSeriesTuple_natAdd, relativeSeriesInverse_X]
      rfl
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (algebra K A s ∅) a
  exact congrArg (fun ψ : BoundedAlgHom K
    (GeneralizedTateAlgebra (A.polyradius.append s) K) (algebra K A s ∅) => ψ f) h

/-- The forward map after reverse evaluation is the relative-series identity. -/
theorem relativeSeriesMap_comp_inverse :
    (relativeSeriesMap K A s).comp (relativeSeriesInverse K A s) =
      BoundedAlgHom.id K (GeneralizedTateAlgebra s A) := by
  apply relative_hom_ext
  · intro a
    change relativeSeriesMap K A s
      (relativeSeriesInverse K A s (constantAlgHom s K A a)) = constantAlgHom s K A a
    rw [relativeSeriesInverse_constant, relativeSeriesMap_baseMap]
  · intro j
    change relativeSeriesMap K A s (relativeSeriesInverse K A s (X s A j)) = X s A j
    rw [relativeSeriesInverse_X, relativeSeriesMap_newCoordinate]

@[simp] theorem relativeSeriesInverse_map (a : algebra K A s ∅) :
    relativeSeriesInverse K A s (relativeSeriesMap K A s a) = a :=
  congrArg (fun ψ : BoundedAlgHom K (algebra K A s ∅) (algebra K A s ∅) => ψ a)
    (relativeSeriesInverse_comp_map K A s)

@[simp] theorem relativeSeriesMap_inverse (f : GeneralizedTateAlgebra s A) :
    relativeSeriesMap K A s (relativeSeriesInverse K A s f) = f :=
  congrArg (fun ψ : BoundedAlgHom K (GeneralizedTateAlgebra s A)
    (GeneralizedTateAlgebra s A) => ψ f) (relativeSeriesMap_comp_inverse K A s)

/-- The actual comparison preserves the quotient norm exactly. -/
theorem norm_relativeSeriesMap (a : algebra K A s ∅) :
    ‖relativeSeriesMap K A s a‖ = ‖a‖ := by
  apply le_antisymm (norm_relativeSeriesMap_le K A s a)
  simpa only [relativeSeriesInverse_map] using
    norm_relativeSeriesInverse_le K A s (relativeSeriesMap K A s a)

/-- The actual comparison is an isometry, including for a zero quotient. -/
theorem isometry_relativeSeriesMap : Isometry (relativeSeriesMap K A s) :=
  AddMonoidHomClass.isometry_of_norm (relativeSeriesMap K A s).toAlgHom
    (norm_relativeSeriesMap K A s)

/-- Every relative series is represented by the enlarged closed-relation quotient. -/
theorem relativeSeriesMap_surjective : Function.Surjective (relativeSeriesMap K A s) :=
  fun f => ⟨relativeSeriesInverse K A s f, relativeSeriesMap_inverse K A s f⟩

/-- The prequotient evaluation kernel is exactly the closed ideal of old relations. -/
theorem relativeSeriesEvaluation_eq_zero_iff
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeSeriesEvaluation K A s f = 0 ↔ f ∈ (algebra K A s ∅).ideal := by
  have hk := presentationMap_eq_zero_iff K (algebra K A s ∅) f
  have hz : relativeSeriesMap K A s (0 : algebra K A s ∅) = 0 :=
    map_zero (relativeSeriesMap K A s).toAlgHom
  constructor
  · intro h
    apply hk.mp
    apply (isometry_relativeSeriesMap K A s).injective
    exact (relativeSeriesMap_presentationMap K A s f).trans (h.trans hz.symm)
  · intro h
    exact (relativeSeriesMap_presentationMap K A s f).symm.trans
      ((congrArg (relativeSeriesMap K A s) (hk.mpr h)).trans hz)

/-- The complete unchanged comparison statement. -/
theorem relativeSeriesComparison : RelativeSeriesComparisonStatement.{u} := by
  intro K _ _ _ A m s
  exact ⟨relativeSeriesMap_surjective K A s, isometry_relativeSeriesMap K A s,
    relativeSeriesEvaluation_eq_zero_iff K A s⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
