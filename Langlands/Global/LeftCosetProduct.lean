import Langlands.Global.LeftCosetMeasure

/-! # A left quotient with an unquotiented direct factor -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Topology

namespace Langlands.Global.LeftCosetSpace

universe u v w

variable {A : Type u} {N : Type v} {G : Type w} [Group A] [Group N] [Group G]
  [TopologicalSpace A] [TopologicalSpace N] [TopologicalSpace G]
  (E : A × N ≃ₜ* G) (H : Subgroup N) (Γ : Subgroup G)
  (hΓ : ∀ p, E p ∈ Γ ↔ p.1 = 1 ∧ p.2 ∈ H)

include hΓ in
private theorem mk_product_iff (x y : A × N) :
    mk Γ (E x) = mk Γ (E y) ↔ (x.1, mk H x.2) = (y.1, mk H y.2) := by
  rw [mk_eq_mk_iff, ← map_inv E, ← map_mul E, hΓ, Prod.mk.injEq, mk_eq_mk_iff]
  change (y.1 * x.1⁻¹ = 1 ∧ y.2 * x.2⁻¹ ∈ H) ↔ _
  rw [mul_inv_eq_one, eq_comm (a := y.1)]

variable [IsTopologicalGroup N]

/-- Under `E`, quotienting on the left by `{1} × H` leaves the `A` coordinate unchanged. -/
def productHomeomorph : LeftCosetSpace Γ ≃ₜ A × LeftCosetSpace H where
  toFun := Quotient.lift (fun g => ((E.symm g).1, mk H (E.symm g).2)) (by
    intro g g' h
    apply (mk_product_iff E H Γ hΓ (E.symm g) (E.symm g')).mp
    rw [E.apply_symm_apply, E.apply_symm_apply]
    exact Quotient.sound h)
  invFun p := mk Γ (E (p.1, p.2.out))
  left_inv q := by
    obtain ⟨g, rfl⟩ := mk_surjective Γ q
    change mk Γ (E ((E.symm g).1, (mk H (E.symm g).2).out)) = mk Γ g
    conv_rhs => rw [← E.apply_symm_apply g]
    exact (mk_product_iff E H Γ hΓ _ _).mpr
      (Prod.ext rfl (Quotient.out_eq (mk H (E.symm g).2)))
  right_inv p := by
    change ((E.symm (E (p.1, p.2.out))).1, mk H (E.symm (E (p.1, p.2.out))).2) = p
    rw [E.symm_apply_apply]
    exact Prod.ext rfl (Quotient.out_eq p.2)
  continuous_toFun := (continuous_iff Γ).mpr
    ((continuous_fst.comp E.symm.continuous).prodMk
      ((continuous_mk H).comp (continuous_snd.comp E.symm.continuous)))
  continuous_invFun := by
    refine ((IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_mk H)).isQuotientMap.continuous_iff).mpr ?_
    have hcomp : (fun p : A × LeftCosetSpace H => mk Γ (E (p.1, p.2.out))) ∘
        Prod.map id (mk H) = (mk Γ) ∘ E := by
      funext p
      exact (mk_product_iff E H Γ hΓ _ _).mpr (Prod.ext rfl (Quotient.out_eq (mk H p.2)))
    rw [hcomp]
    exact (continuous_mk Γ).comp E.continuous

@[simp] theorem productHomeomorph_mk (p : A × N) :
    productHomeomorph E H Γ hΓ (mk Γ (E p)) = (p.1, mk H p.2) := by
  change ((E.symm (E p)).1, mk H (E.symm (E p)).2) = _
  rw [E.symm_apply_apply]

@[simp] theorem productHomeomorph_symm_apply (p : A × N) :
    (productHomeomorph E H Γ hΓ).symm (p.1, mk H p.2) = mk Γ (E p) :=
  (productHomeomorph E H Γ hΓ).symm_apply_eq.mpr (productHomeomorph_mk E H Γ hΓ p).symm

variable [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace G]

/-- Measurability for the inherited quotient sigma algebras, without a Borel comparison. -/
theorem measurable_productHomeomorph (hE : Measurable (E.symm : G → A × N)) :
    Measurable (productHomeomorph E H Γ hΓ) :=
  measurable_from_quotient.mpr
    ((measurable_fst.comp hE).prodMk ((measurable_mk H).comp (measurable_snd.comp hE)))

end Langlands.Global.LeftCosetSpace
