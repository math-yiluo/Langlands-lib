import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Langlands.Geometry.Analytic.BoundedQuotient.Statement

/-! # Bounded algebra maps out of closed-ideal quotients -/

noncomputable section

universe u v w

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w}
  [NormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- A continuous algebra map annihilating an ideal also annihilates its
topological closure. -/
theorem annihilates_closure (φ : BoundedAlgHom K A B) (I : Ideal A)
    (hI : ∀ a ∈ I, φ a = 0) : ∀ a ∈ I.closure, φ a = 0 := by
  have hclosed : IsClosed {a : A | φ a = 0} :=
    isClosed_eq φ.continuous continuous_const
  exact fun a ha => closure_minimal hI hclosed ha

variable (K) (I : Ideal A) [IsClosed (I : Set A)]

/-- The quotient algebra map is contractive for the quotient norm. -/
def quotientMap : BoundedAlgHom K A (A ⧸ I) where
  toAlgHom := Ideal.Quotient.mkₐ K I
  bounded := ⟨1, zero_lt_one, fun a => by
    rw [one_mul]
    exact Ideal.Quotient.norm_mk_le I a⟩

/-- Every positive bound on representatives is a bound for the quotient norm. -/
theorem quotient_norm_bound (f : A ⧸ I →+* B) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ a, ‖f (Ideal.Quotient.mk I a)‖ ≤ C * ‖a‖) (x : A ⧸ I) :
    ‖f x‖ ≤ C * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := Ideal.Quotient.norm_mk_lt x (div_pos hε hCpos)
  calc
    ‖f (Ideal.Quotient.mk I a)‖ ≤ C * ‖a‖ := hC a
    _ ≤ C * (‖Ideal.Quotient.mk I a‖ + ε / C) :=
      mul_le_mul_of_nonneg_left ha.le hCpos.le
    _ = C * ‖Ideal.Quotient.mk I a‖ + ε := by
      rw [mul_add, mul_div_cancel₀ _ hCpos.ne']

/-- Descent to the actual algebra quotient, retaining a norm bound.
The bound is proved with representatives arbitrarily close to the quotient norm. -/
def liftQuotient (φ : BoundedAlgHom K A B) (hI : ∀ a ∈ I, φ a = 0) :
    BoundedAlgHom K (A ⧸ I) B where
  toAlgHom := Ideal.Quotient.liftₐ I φ.toAlgHom hI
  bounded := by
    obtain ⟨C, hCpos, hC⟩ := φ.bounded
    exact ⟨C, hCpos,
      quotient_norm_bound I (Ideal.Quotient.liftₐ I φ.toAlgHom hI).toRingHom C hCpos hC⟩

@[simp]
theorem liftQuotient_mk (φ : BoundedAlgHom K A B) (hI : ∀ a ∈ I, φ a = 0) (a : A) :
    liftQuotient K I φ hI (Ideal.Quotient.mk I a) = φ a := rfl

theorem liftQuotient_comp_quotientMap (φ : BoundedAlgHom K A B)
    (hI : ∀ a ∈ I, φ a = 0) :
    (liftQuotient K I φ hI).comp (quotientMap K I) = φ :=
  ext fun _ => rfl

/-- A map out of the quotient is determined by its composite with the quotient map. -/
theorem quotient_hom_ext (φ ψ : BoundedAlgHom K (A ⧸ I) B)
    (h : ∀ a, φ (Ideal.Quotient.mk I a) = ψ (Ideal.Quotient.mk I a)) : φ = ψ := by
  apply ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact h a

/-- Bounded maps out of the quotient are exactly bounded maps annihilating
the actual ideal. No quotient-map output is assumed. -/
def quotientHomEquiv :
    BoundedAlgHom K (A ⧸ I) B ≃
      {φ : BoundedAlgHom K A B // ∀ a ∈ I, φ a = 0} where
  toFun ψ := ⟨ψ.comp (quotientMap K I), fun a ha => by
    change ψ.toAlgHom (Ideal.Quotient.mk I a) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]⟩
  invFun φ := liftQuotient K I φ.val φ.property
  left_inv ψ := quotient_hom_ext K I _ _ fun _ => rfl
  right_inv φ := Subtype.ext (ext fun _ => rfl)

end Langlands.Analytic.BoundedAlgHom

namespace Langlands.Analytic

/-- Unique bounded quotient descent preserves every positive norm bound. -/
theorem boundedQuotientProperties : BoundedQuotientStatement := by
  intro K A B _ _ _ _ _
  refine ⟨fun φ I hI => BoundedAlgHom.annihilates_closure φ I hI, ?_⟩
  intro I _
  constructor
  · intro φ hI
    refine ⟨BoundedAlgHom.liftQuotient K I φ hI, fun _ => rfl, ?_⟩
    intro ψ hψ
    exact BoundedAlgHom.quotient_hom_ext K I _ _ hψ
  · intro φ ψ hψ C hC hbound
    apply BoundedAlgHom.quotient_norm_bound I ψ.toRingHom C hC
    intro a
    rw [show ψ.toRingHom (Ideal.Quotient.mk I a) = φ a from hψ a]
    exact hbound a

end Langlands.Analytic
