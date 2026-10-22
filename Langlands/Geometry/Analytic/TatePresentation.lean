import Langlands.Geometry.Analytic.TatePresentation.Statement
import Langlands.Geometry.Analytic.BoundedQuotient
import Langlands.Geometry.Analytic.TateUniversal

/-! # Bounded maps from actual Tate relation quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

open StrictTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

variable (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
  (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

/-- Evaluate relations at a bounded-monomial tuple and descend through their
actual closed ideal when the relations vanish. -/
def liftRelations (b : Fin n → B) (hb : HasBoundedMonomials (Fin n) B b)
    (hrel : ∀ f ∈ relations, evaluate (Fin n) K B b f = 0) :
    BoundedAlgHom K (ofRelations K n relations) B := by
  let φ := evaluateHom (Fin n) K B b hb
  have hspan : ∀ f ∈ Ideal.span relations, φ f = 0 := by
    have h : Ideal.span relations ≤ RingHom.ker φ.toAlgHom.toRingHom :=
      Ideal.span_le.mpr hrel
    exact h
  letI := (ofRelations K n relations).ideal_closed
  exact BoundedAlgHom.liftQuotient K (ofRelations K n relations).ideal φ
    (φ.annihilates_closure (Ideal.span relations) hspan)

@[simp]
theorem liftRelations_presentationMap (b : Fin n → B)
    (hb : HasBoundedMonomials (Fin n) B b)
    (hrel : ∀ f ∈ relations, evaluate (Fin n) K B b f = 0)
    (f : StrictTateAlgebra (Fin n) K) :
    liftRelations K n relations B b hb hrel
      (presentationMap K (ofRelations K n relations) f) =
        evaluate (Fin n) K B b f := rfl

theorem liftRelations_coordinate (b : Fin n → B)
    (hb : HasBoundedMonomials (Fin n) B b)
    (hrel : ∀ f ∈ relations, evaluate (Fin n) K B b f = 0) (i : Fin n) :
    liftRelations K n relations B b hb hrel
      (coordinate K (ofRelations K n relations) i) = b i := by
  change evaluate (Fin n) K B b (X (Fin n) K i) = b i
  exact evaluate_X (Fin n) K B b i

variable [CompleteSpace K]

omit [IsUltrametricDist B] [CompleteSpace B] in
/-- Bounded maps out of the presentation are determined by the coordinate
images, using surjectivity of the actual quotient projection. -/
theorem hom_ext_coordinates (φ ψ : BoundedAlgHom K (ofRelations K n relations) B)
    (h : ∀ i, φ (coordinate K (ofRelations K n relations) i) =
      ψ (coordinate K (ofRelations K n relations) i)) : φ = ψ := by
  have hmaps : φ.comp (presentationMap K (ofRelations K n relations)) =
      ψ.comp (presentationMap K (ofRelations K n relations)) :=
    StrictTateAlgebra.hom_ext (Fin n) K B _ _ h
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (ofRelations K n relations) x
  exact congrArg (fun χ => χ f) hmaps

/-- Solutions of the relations in a complete ultrametric normed algebra are
represented by the actual closed-ideal Tate quotient, for bounded morphisms. -/
def homEquivSolutions :
    BoundedAlgHom K (ofRelations K n relations) B ≃
      {b : Fin n → B // HasBoundedMonomials (Fin n) B b ∧
        ∀ f ∈ relations, evaluate (Fin n) K B b f = 0} where
  toFun φ := ⟨fun i => φ (coordinate K (ofRelations K n relations) i),
    hasBoundedMonomials_map_X (Fin n) K B
      (φ.comp (presentationMap K (ofRelations K n relations))),
    fun f hf => by
      have h := (map_eq_evaluate (Fin n) K B
        (φ.comp (presentationMap K (ofRelations K n relations))) f).symm
      change evaluate (Fin n) K B
        (fun i => φ (coordinate K (ofRelations K n relations) i)) f =
          φ (presentationMap K (ofRelations K n relations) f) at h
      rw [h, presentationMap_relation K n relations hf]
      exact map_zero φ.toAlgHom⟩
  invFun b := liftRelations K n relations B b.val b.property.1 b.property.2
  left_inv φ := hom_ext_coordinates K n relations B _ _ fun i =>
    liftRelations_coordinate K n relations B _ _ _ i
  right_inv b := by
    apply Subtype.ext
    funext i
    exact liftRelations_coordinate K n relations B b.val b.property.1 b.property.2 i

/-- Bounded solutions are represented by the actual closed relation quotient,
with precisely the completeness hypotheses stated in each clause. -/
theorem relationsUniversalProperty : RelationsUniversalPropertyStatement.{u, v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ n relations B _ _ _ _ b hb hrel
    exact ⟨liftRelations K n relations B b hb hrel,
      liftRelations_presentationMap K n relations B b hb hrel,
      liftRelations_coordinate K n relations B b hb hrel⟩
  · intro K _ _ _ n relations B _ _ φ ψ h
    exact hom_ext_coordinates K n relations B φ ψ h
  · intro K _ _ _ n relations B _ _ _ _ b
    constructor
    · rintro ⟨φ, hφ, _⟩
      have hs := (homEquivSolutions K n relations B φ).property
      have hcoords : (fun i => φ (coordinate K (ofRelations K n relations) i)) = b :=
        funext hφ
      change HasBoundedMonomials (Fin n) B
        (fun i => φ (coordinate K (ofRelations K n relations) i)) ∧
        (∀ f ∈ relations, evaluate (Fin n) K B
          (fun i => φ (coordinate K (ofRelations K n relations) i)) f = 0) at hs
      rw [← hcoords]
      exact hs
    · rintro ⟨hb, hrel⟩
      refine ⟨liftRelations K n relations B b hb hrel,
        liftRelations_coordinate K n relations B b hb hrel, ?_⟩
      intro ψ hψ
      exact hom_ext_coordinates K n relations B _ _ fun i =>
        (hψ i).trans (liftRelations_coordinate K n relations B b hb hrel i).symm

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
