import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.BoundedQuotient

/-! # Closed relation presentations with arbitrary positive polyradii -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (n : ℕ) (r : PositivePolyradius (Fin n))
  (relations : Set (GeneralizedTateAlgebra r K))

/-- The actual weighted Tate quotient by the closure of the generated relations. -/
def ofRelations : PresentedAffinoidAlgebra K where
  arity := n
  polyradius := r
  ideal := (Ideal.span relations).closure
  ideal_closed := isClosed_closure

theorem relation_mem {f : GeneralizedTateAlgebra r K} (hf : f ∈ relations) :
    f ∈ (ofRelations K n r relations).ideal :=
  subset_closure (Ideal.subset_span hf)

@[simp]
theorem presentationMap_relation {f : GeneralizedTateAlgebra r K} (hf : f ∈ relations) :
    presentationMap K (ofRelations K n r relations) f = 0 :=
  (presentationMap_eq_zero_iff K _ f).mpr (relation_mem K n r relations hf)

/-- A closed-ideal presentation is recovered by using all its ideal elements
as relations; no new choice of carrier or norm is made. -/
theorem ofRelations_ideal (A : PresentedAffinoidAlgebra K) :
    ofRelations K A.arity A.polyradius A.ideal = A := by
  cases A with
  | mk arity polyradius ideal ideal_closed =>
    simp only [ofRelations, Ideal.span_eq, Ideal.closure_eq_of_isClosed ideal ideal_closed]

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]

/-- Descend a supplied bounded homomorphism which annihilates the relations.
Continuity proves that it also annihilates their closed generated ideal. -/
def descendRelations (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (hrel : ∀ f ∈ relations, φ f = 0) :
    BoundedAlgHom K (ofRelations K n r relations) B := by
  have hspan : ∀ f ∈ Ideal.span relations, φ f = 0 :=
    (Ideal.span_le.mpr hrel : Ideal.span relations ≤ RingHom.ker φ.toAlgHom.toRingHom)
  letI := (ofRelations K n r relations).ideal_closed
  exact BoundedAlgHom.liftQuotient K (ofRelations K n r relations).ideal φ
    (φ.annihilates_closure (Ideal.span relations) hspan)

@[simp]
theorem descendRelations_presentationMap
    (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (hrel : ∀ f ∈ relations, φ f = 0) (f : GeneralizedTateAlgebra r K) :
    descendRelations K n r relations B φ hrel
      (presentationMap K (ofRelations K n r relations) f) = φ f := rfl

theorem descendRelations_comp_presentationMap
    (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (hrel : ∀ f ∈ relations, φ f = 0) :
    (descendRelations K n r relations B φ hrel).comp
      (presentationMap K (ofRelations K n r relations)) = φ :=
  BoundedAlgHom.ext fun _ => rfl

/-- Descent preserves each supplied positive bound for the actual quotient norm. -/
theorem norm_descendRelations_le
    (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (hrel : ∀ f ∈ relations, φ f = 0) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ f, ‖φ f‖ ≤ C * ‖f‖) (a : ofRelations K n r relations) :
    ‖descendRelations K n r relations B φ hrel a‖ ≤ C * ‖a‖ := by
  let := (ofRelations K n r relations).ideal_closed
  exact BoundedAlgHom.quotient_norm_bound (ofRelations K n r relations).ideal
    (descendRelations K n r relations B φ hrel).toAlgHom.toRingHom C hC hbound a

/-- Surjectivity determines a bounded homomorphism by its values on presented series. -/
theorem hom_ext_presentation (A : PresentedAffinoidAlgebra K)
    (φ ψ : BoundedAlgHom K A B)
    (h : ∀ f, φ (presentationMap K A f) = ψ (presentationMap K A f)) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  exact h f

/-- Maps out of the constructed quotient are exactly bounded Tate maps
annihilating the supplied relations. Neither target nor coefficient completeness
is needed for this quotient construction. -/
def homEquivAnnihilating :
    BoundedAlgHom K (ofRelations K n r relations) B ≃
      {φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B //
        ∀ f ∈ relations, φ f = 0} where
  toFun ψ := ⟨ψ.comp (presentationMap K (ofRelations K n r relations)),
    fun f hf => by
      change ψ.toAlgHom (presentationMap K (ofRelations K n r relations) f) = 0
      rw [presentationMap_relation K n r relations hf, map_zero]⟩
  invFun φ := descendRelations K n r relations B φ.val φ.property
  left_inv ψ := hom_ext_presentation K B _ _ _ fun _ => rfl
  right_inv φ := Subtype.ext (BoundedAlgHom.ext fun _ => rfl)

end Langlands.Analytic.PresentedAffinoidAlgebra
