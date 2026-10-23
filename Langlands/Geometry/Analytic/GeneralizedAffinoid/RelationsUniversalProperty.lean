import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelationsStatement
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation

/-! # The coordinate universal property of weighted relation quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (B : Type v) [NormedCommRing B] [NormedAlgebra K B]

/-- Coordinate images of every bounded map satisfy the weighted monomial bound. -/
theorem hasBoundedMonomials_coordinate (A : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K A B) :
    HasBoundedMonomials A.polyradius B (fun i => φ (coordinate K A i)) :=
  hasBoundedMonomials_map_X A.polyradius K B (φ.comp (presentationMap K A))

/-- A bounded map on any presentation agrees with evaluation on projected series. -/
theorem map_presentation_eq_evaluate (A : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K A B) (f : GeneralizedTateAlgebra A.polyradius K) :
    φ (presentationMap K A f) =
      evaluate A.polyradius K B (fun i => φ (coordinate K A i)) f :=
  map_eq_evaluate A.polyradius K B (φ.comp (presentationMap K A)) f

/-- Coordinates determine a bounded map, with no target completeness assumption. -/
theorem hom_ext_coordinate (A : PresentedAffinoidAlgebra K)
    (φ ψ : BoundedAlgHom K A B)
    (h : ∀ i, φ (coordinate K A i) = ψ (coordinate K A i)) : φ = ψ := by
  have hcomp : φ.comp (presentationMap K A) = ψ.comp (presentationMap K A) :=
    GeneralizedTateAlgebra.hom_ext A.polyradius K B _ _ h
  apply hom_ext_presentation K B A φ ψ
  intro f
  exact congrArg (fun η : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) B =>
    η f) hcomp

variable (n : ℕ) (r : PositivePolyradius (Fin n))
  (relations : Set (GeneralizedTateAlgebra r K))

/-- Every relation vanishes at the coordinate images of a bounded quotient map. -/
theorem evaluate_relation_coordinate
    (φ : BoundedAlgHom K (ofRelations K n r relations) B)
    {f : GeneralizedTateAlgebra r K} (hf : f ∈ relations) :
    evaluate r K B (fun i => φ (coordinate K (ofRelations K n r relations) i)) f = 0 := by
  calc
    _ = φ (presentationMap K (ofRelations K n r relations) f) :=
      (map_presentation_eq_evaluate K B (ofRelations K n r relations) φ f).symm
    _ = 0 := by
      rw [presentationMap_relation K n r relations hf]
      exact map_zero φ.toAlgHom

section CompleteTarget

variable [IsUltrametricDist B] [CompleteSpace B]

/-- Weighted evaluation descended through the closed ideal of relations. -/
def evaluateRelations (b : Fin n → B) (hb : HasBoundedMonomials r B b)
    (hrel : ∀ f ∈ relations, evaluate r K B b f = 0) :
    BoundedAlgHom K (ofRelations K n r relations) B :=
  descendRelations K n r relations B (evaluateHom r K B b hb) hrel

@[simp]
theorem evaluateRelations_presentationMap
    (b : Fin n → B) (hb : HasBoundedMonomials r B b)
    (hrel : ∀ f ∈ relations, evaluate r K B b f = 0)
    (f : GeneralizedTateAlgebra r K) :
    evaluateRelations K B n r relations b hb hrel
      (presentationMap K (ofRelations K n r relations) f) = evaluate r K B b f :=
  rfl

@[simp]
theorem evaluateRelations_coordinate
    (b : Fin n → B) (hb : HasBoundedMonomials r B b)
    (hrel : ∀ f ∈ relations, evaluate r K B b f = 0) (i : Fin n) :
    evaluateRelations K B n r relations b hb hrel
      (coordinate K (ofRelations K n r relations) i) = b i :=
  evaluate_X r K B b i

/-- The single descended map preserves every admissible positive monomial constant. -/
theorem norm_evaluateRelations_le
    (b : Fin n → B) (hb : HasBoundedMonomials r B b)
    (hrel : ∀ f ∈ relations, evaluate r K B b f = 0)
    (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : Fin n →₀ ℕ,
      ‖StrictTateAlgebra.monomialValue (Fin n) B b d‖ ≤ C * r.weight d)
    (a : ofRelations K n r relations) :
    ‖evaluateRelations K B n r relations b hb hrel a‖ ≤ C * ‖a‖ :=
  norm_descendRelations_le K n r relations B (evaluateHom r K B b hb) hrel
    C hCpos (evaluate_norm_le_bound r K B b C hCpos hC) a

/-- The explicit bounded coordinate solutions are exactly the uniquely represented ones. -/
theorem boundedSolution_iff_existsUnique (b : Fin n → B) :
    (HasBoundedMonomials r B b ∧ ∀ f ∈ relations, evaluate r K B b f = 0) ↔
      ∃! φ : BoundedAlgHom K (ofRelations K n r relations) B,
        ∀ i, φ (coordinate K (ofRelations K n r relations) i) = b i := by
  constructor
  · rintro ⟨hb, hrel⟩
    refine ⟨evaluateRelations K B n r relations b hb hrel,
      evaluateRelations_coordinate K B n r relations b hb hrel, ?_⟩
    intro φ hφ
    apply hom_ext_coordinate K B (ofRelations K n r relations)
    intro i
    exact (hφ i).trans
      (evaluateRelations_coordinate K B n r relations b hb hrel i).symm
  · rintro ⟨φ, hφ, _⟩
    have hcoords : (fun i : Fin n =>
        φ (coordinate K (ofRelations K n r relations) i)) = b := funext hφ
    constructor
    · exact (congrArg (HasBoundedMonomials r B) hcoords).mp
        (hasBoundedMonomials_coordinate K B (ofRelations K n r relations) φ)
    · intro f hf
      exact (congrArg (fun b : Fin n → B => evaluate r K B b f = 0) hcoords).mp
        (evaluate_relation_coordinate K B n r relations φ hf)

end CompleteTarget

/-- All three clauses of the unchanged relation-quotient universal property. -/
theorem relationsUniversalProperty : RelationsUniversalPropertyStatement.{u, v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ n r relations B _ _ _ _ b hb hrel
    exact ⟨evaluateRelations K B n r relations b hb hrel,
      evaluateRelations_presentationMap K B n r relations b hb hrel,
      evaluateRelations_coordinate K B n r relations b hb hrel,
      norm_evaluateRelations_le K B n r relations b hb hrel⟩
  · intro K _ _ n r relations B _ _
    exact ⟨hasBoundedMonomials_coordinate K B (ofRelations K n r relations),
      hom_ext_coordinate K B (ofRelations K n r relations)⟩
  · intro K _ _ n r relations B _ _ _ _ b
    exact boundedSolution_iff_existsUnique K B n r relations b

end Langlands.Analytic.PresentedAffinoidAlgebra
