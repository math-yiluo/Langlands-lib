import Langlands.Representation.Induction.TransversalConjugationStatements
import Langlands.Representation.Induction.ConjugateParabolic

/-! # Conjugation of compact induction (Renard III.2.4) -/

noncomputable section

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {P Q : Subgroup G} {σ : Representation R P V} {τ : Representation R Q V}

/-- The quotient map induced by the inverse of the translating element. -/
private def translateLeftQuotient (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) : LeftQuotient P → LeftQuotient Q :=
  Quotient.map' (fun x => a⁻¹ * x) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have hm := (e ⟨y * x⁻¹, h⟩).property
    rw [he] at hm
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hm)

private theorem continuous_translateLeftQuotient (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) :
    Continuous (translateLeftQuotient a e he) :=
  (continuous_const.mul continuous_id).quotient_map' _

omit [IsTopologicalGroup G] in
/-- Translation takes projected nonzero support exactly to its quotient image. -/
private theorem quotientSupport_translate (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) :
    quotientSupport Q (eval Q τ (translateSmoothFunction a e he hστ f)) =
      translateLeftQuotient a e he '' quotientSupport P (eval P σ f) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨quotientMap P (a * x), ⟨a * x, hx, rfl⟩, ?_⟩
    change quotientMap Q (a⁻¹ * (a * x)) = quotientMap Q x
    rw [inv_mul_cancel_left]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨a⁻¹ * x, ?_, rfl⟩
    change eval P σ f (a * (a⁻¹ * x)) ≠ 0
    simpa only [Function.mem_support, mul_inv_cancel_left] using hx

/-- The published smooth translation restricted to compact support modulo the subgroup. -/
private def translateCompactFunction (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : CompactFunctions P σ) : CompactFunctions Q τ :=
  ⟨translateSmoothFunction a e he hστ f.val, by
    change IsCompact (quotientSupport Q (eval Q τ _))
    rw [quotientSupport_translate]
    exact f.property.image (continuous_translateLeftQuotient a e he)⟩

/-- Renard III.2.4, compact induction, with its specified translation formula. -/
theorem compactConjugateInduced : CompactConjugateInducedStatement.{uR, uG, uV} := by
  intro R G V _ _ _ _ _ _ P Q σ τ c e he hστ
  have he' : ∀ p : P, (e p : G) = c⁻¹⁻¹ * p * c⁻¹ := by
    simpa only [inv_inv] using he
  have heSymm : ∀ q : Q, (e.symm q : G) = c⁻¹ * q * c := by
    intro q
    have h := he (e.symm q)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp [mul_assoc]
  have hτσ : ∀ q : Q, σ (e.symm q) = τ q := by
    intro q
    rw [← hστ, MulEquiv.apply_symm_apply]
  let A : (compactInduced P σ).Equiv (compactInduced Q τ) :=
    { toFun := translateCompactFunction c⁻¹ e he' hστ
      invFun := translateCompactFunction c e.symm heSymm hτσ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := by
        intro f
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P σ f.val (c⁻¹ * (c * x)) = eval P σ f.val x
        rw [inv_mul_cancel_left]
      right_inv := by
        intro f
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval Q τ f.val (c * (c⁻¹ * x)) = eval Q τ f.val x
        rw [mul_inv_cancel_left]
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P σ f.val (c⁻¹ * x * g) = eval P σ f.val (c⁻¹ * (x * g))
        rw [mul_assoc] }
  exact ⟨A, fun _ _ => rfl⟩

end Langlands.Induction
