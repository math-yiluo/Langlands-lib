import Langlands.Geometry.Analytic.GeneralizedAffinoid.Adjoin
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeAlgebra
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation

/-! # The forward map from variable adjunction to relative series -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace GeneralizedTateAlgebra

/-- Coordinate bounds imply the weighted monomial bound even for a zero target. -/
theorem monomialValue_norm_le_weight {σ : Type u} (r : PositivePolyradius σ)
    (B : Type v) [NormedCommRing B] (h1 : ‖(1 : B)‖ ≤ 1)
    (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ r i) (d : σ →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ r.weight d := by
  classical
  unfold StrictTateAlgebra.monomialValue PositivePolyradius.weight Finsupp.prod
  by_cases hd : d.support.Nonempty
  · apply (Finset.norm_prod_le' _ hd _).trans
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    exact (norm_pow_le' (b i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hb i) _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hd]
    simpa only [Finset.prod_empty] using h1

end GeneralizedTateAlgebra

namespace PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- The quotient unit has norm at most one; the zero quotient is allowed. -/
theorem norm_one_le : ‖(1 : A)‖ ≤ 1 := by
  have h := norm_presentationMap_le K A 1
  simpa only [map_one, norm_one] using h

namespace Adjoin

variable {m : ℕ} (s : PositivePolyradius (Fin m))

/-- Old coordinates become constant series and new coordinates become variables. -/
def relativeSeriesTuple : Fin (A.arity + m) → GeneralizedTateAlgebra s A :=
  Fin.addCases (fun i => constantAlgHom s K A (coordinate K A i)) (X s A)

@[simp] theorem relativeSeriesTuple_castAdd (i : Fin A.arity) :
    relativeSeriesTuple K A s (Fin.castAdd m i) =
      constantAlgHom s K A (coordinate K A i) := by
  simp [relativeSeriesTuple]

@[simp] theorem relativeSeriesTuple_natAdd (j : Fin m) :
    relativeSeriesTuple K A s (Fin.natAdd A.arity j) = X s A j := by
  simp [relativeSeriesTuple]

theorem norm_relativeSeriesTuple_le (i : Fin (A.arity + m)) :
    ‖relativeSeriesTuple K A s i‖ ≤ (A.polyradius.append s) i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [relativeSeriesTuple_castAdd, norm_constantAlgHom,
      PositivePolyradius.append_castAdd] using norm_coordinate_le K A j
  · intro j
    simp only [relativeSeriesTuple_natAdd, norm_X, PositivePolyradius.append_natAdd]
    exact mul_le_of_le_one_left (s.positive j).le (norm_one_le K A)

theorem relativeSeriesTuple_monomial_bound (d : Fin (A.arity + m) →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (GeneralizedTateAlgebra s A)
      (relativeSeriesTuple K A s) d‖ ≤ (A.polyradius.append s).weight d := by
  apply monomialValue_norm_le_weight _ _ _ _ (norm_relativeSeriesTuple_le K A s)
  have h := norm_algebraMap s A (1 : A)
  rw [map_one] at h
  exact h.le.trans (norm_one_le K A)

variable [CompleteSpace K]

/-- Evaluate the enlarged scalar series in the actual relative series algebra. -/
def relativeSeriesEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra (A.polyradius.append s) K)
      (GeneralizedTateAlgebra s A) :=
  evaluateHom (A.polyradius.append s) K (GeneralizedTateAlgebra s A)
    (relativeSeriesTuple K A s)
    ⟨1, zero_lt_one, fun d => by
      simpa only [one_mul] using relativeSeriesTuple_monomial_bound K A s d⟩

theorem norm_relativeSeriesEvaluation_le
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    ‖relativeSeriesEvaluation K A s f‖ ≤ ‖f‖ := by
  exact (evaluate_norm_le_bound (A.polyradius.append s) K (GeneralizedTateAlgebra s A)
    (relativeSeriesTuple K A s) 1 zero_lt_one
    (fun d => by simpa only [one_mul] using relativeSeriesTuple_monomial_bound K A s d)
    f).trans_eq (one_mul _)

@[simp] theorem relativeSeriesEvaluation_X (i : Fin (A.arity + m)) :
    relativeSeriesEvaluation K A s (X (A.polyradius.append s) K i) =
      relativeSeriesTuple K A s i :=
  evaluate_X (A.polyradius.append s) K (GeneralizedTateAlgebra s A)
    (relativeSeriesTuple K A s) i

/-- Evaluating the old variable block agrees with the quotient coefficient map. -/
theorem relativeSeriesEvaluation_comp_appendLeft :
    (relativeSeriesEvaluation K A s).comp (appendLeft A.polyradius s K) =
      (constantAlgHom s K A).comp (presentationMap K A) := by
  apply GeneralizedTateAlgebra.hom_ext
  intro i
  change relativeSeriesEvaluation K A s (appendLeft A.polyradius s K
    (X A.polyradius K i)) = constantAlgHom s K A (coordinate K A i)
  rw [appendLeft_X, relativeSeriesEvaluation_X, relativeSeriesTuple_castAdd]

@[simp] theorem relativeSeriesEvaluation_appendLeft
    (f : GeneralizedTateAlgebra A.polyradius K) :
    relativeSeriesEvaluation K A s (appendLeft A.polyradius s K f) =
      constantAlgHom s K A (presentationMap K A f) :=
  congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K)
    (GeneralizedTateAlgebra s A) => φ f) (relativeSeriesEvaluation_comp_appendLeft K A s)

/-- The old ideal relations vanish in relative series. -/
theorem relativeSeriesEvaluation_relations
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K)
    (hf : f ∈ relations K A s ∅) : relativeSeriesEvaluation K A s f = 0 := by
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · rw [relativeSeriesEvaluation_appendLeft, (presentationMap_eq_zero_iff K A g).mpr hg,
      map_zero]
  · exact False.elim hf

/-- The actual bounded map from unconstrained variable adjunction to relative series. -/
def relativeSeriesMap : BoundedAlgHom K (algebra K A s ∅) (GeneralizedTateAlgebra s A) :=
  descendRelations K (A.arity + m) (A.polyradius.append s) (relations K A s ∅)
    (GeneralizedTateAlgebra s A) (relativeSeriesEvaluation K A s)
    (relativeSeriesEvaluation_relations K A s)

@[simp] theorem relativeSeriesMap_presentationMap
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeSeriesMap K A s (presentationMap K (algebra K A s ∅) f) =
      relativeSeriesEvaluation K A s f := rfl

/-- The descended map is contractive for the quotient and weighted series norms. -/
theorem norm_relativeSeriesMap_le (a : algebra K A s ∅) :
    ‖relativeSeriesMap K A s a‖ ≤ ‖a‖ := by
  exact (norm_descendRelations_le K (A.arity + m) (A.polyradius.append s)
    (relations K A s ∅) (GeneralizedTateAlgebra s A) (relativeSeriesEvaluation K A s)
    (relativeSeriesEvaluation_relations K A s) 1 zero_lt_one
    (fun f => by simpa only [one_mul] using norm_relativeSeriesEvaluation_le K A s f)
    a).trans_eq (one_mul _)

@[simp] theorem relativeSeriesMap_baseMap (a : A) :
    relativeSeriesMap K A s (baseMap K A s ∅ a) = constantAlgHom s K A a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [baseMap_presentationMap, relativeSeriesMap_presentationMap,
    relativeSeriesEvaluation_appendLeft]

@[simp] theorem relativeSeriesMap_newCoordinate (j : Fin m) :
    relativeSeriesMap K A s (newCoordinate K A s ∅ j) = X s A j := by
  change relativeSeriesMap K A s (presentationMap K (algebra K A s ∅)
    (X (A.polyradius.append s) K (Fin.natAdd A.arity j))) = _
  rw [relativeSeriesMap_presentationMap, relativeSeriesEvaluation_X,
    relativeSeriesTuple_natAdd]

end Adjoin
end PresentedAffinoidAlgebra
end Langlands.Analytic
