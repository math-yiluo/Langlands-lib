import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Integration over nested discrete left quotients -/

noncomputable section
set_option autoImplicit false

universe u

open Function MeasureTheory Set Topology
open scoped ENNReal

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ Λ : Subgroup H)

/-- Right multiplication by `x` identifies equality of the indicated cosets in `H`
with equality modulo the pullback of `Γ` in `Λ`. -/
theorem mk_mul_subtype_eq_iff (a b : Λ) (x : H) :
    mk Γ (a.val * x) = mk Γ (b.val * x) ↔
      mk (Γ.comap Λ.subtype) a = mk (Γ.comap Λ.subtype) b := by
  rw [mk_eq_mk_iff, mk_eq_mk_iff]
  change (b.val * x) * (a.val * x)⁻¹ ∈ Γ ↔ b.val * a.val⁻¹ ∈ Γ
  simp [mul_inv_rev, mul_assoc]

/-- Translated coset representatives index distinct points of the finer quotient. -/
theorem injective_mk_cosetRepresentative_mul (x : H) :
    Injective (fun c : LeftCosetSpace (Γ.comap Λ.subtype) => mk Γ (c.out.val * x)) := by
  intro a b hab
  exact (Quotient.out_eq a).symm.trans
    (((mk_mul_subtype_eq_iff Γ Λ a.out b.out x).mp hab).trans (Quotient.out_eq b))

section Integral

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

private theorem fundamentalDomain_injOn_mk (hΛ : IsDiscrete (Λ : Set H)) :
    (fundamentalDomain Λ hΛ).InjOn (mk Λ) := by
  intro x hx y hy he
  let a : Λ := ⟨y * x⁻¹, (mk_eq_mk_iff Λ x y).mp he⟩
  have ha : a.val * x = y := by simp [a, mul_assoc]
  have ha' : a.val * x ∈ fundamentalDomain Λ hΛ := ha ▸ hy
  have hone : (1 : Λ).val * x ∈ fundamentalDomain Λ hΛ := by simpa using hx
  have eq : a = 1 := (fundamentalDomain_unique Λ hΛ x).unique ha' hone
  simpa [eq] using ha

/-- Integration on the finer discrete quotient is integration of the sum over the left cosets
of the smaller subgroup in the larger, on a fundamental domain for the larger subgroup. -/
def NestedLeftCosetIntegralStatement : Prop :=
  ∀ (hle : Γ ≤ Λ) (hΛ : IsDiscrete (Λ : Set H)) (m : Measure H) [m.IsMulLeftInvariant],
  ∀ (f : LeftCosetSpace Γ → ℝ≥0∞), Measurable f →
    ∫⁻ z, f z ∂discreteQuotientMeasure Γ (hΛ.mono hle) m =
      ∫⁻ x in fundamentalDomain Λ hΛ,
        ∑' c : LeftCosetSpace (Γ.comap Λ.subtype), f (mk Γ (c.out.val * x)) ∂m

theorem nestedLeftCosetIntegral : NestedLeftCosetIntegralStatement Γ Λ := by
  intro hle hΛ m _ f hf
  let D := fundamentalDomain Λ hΛ
  let I := LeftCosetSpace (Γ.comap Λ.subtype)
  let : Countable Λ := countable_of_isDiscrete Λ hΛ
  let : Countable I := (mk_surjective (Γ.comap Λ.subtype)).countable
  let U (c : I) := (fun y : H => c.out.val * y) '' D
  have hD : MeasurableSet D := measurableSet_fundamentalDomain Λ hΛ
  have hU (c : I) : MeasurableSet (U c) :=
    (measurableEmbedding_mulLeft c.out.val).measurableSet_image.mpr hD
  have hpair {a b : I} {x y : H} (hx : x ∈ D) (hy : y ∈ D)
      (he : mk Γ (a.out.val * x) = mk Γ (b.out.val * y)) : a = b ∧ x = y := by
    have hq := (mk_eq_mk_iff Λ _ _).mpr (hle ((mk_eq_mk_iff Γ _ _).mp he))
    rw [mk_subgroup_mul Λ a.out, mk_subgroup_mul Λ b.out] at hq
    have hxy := fundamentalDomain_injOn_mk Λ hΛ hx hy hq
    subst y
    exact ⟨injective_mk_cosetRepresentative_mul Γ Λ x he, rfl⟩
  have hdisj : Pairwise (fun a b : I => Disjoint (U a) (U b)) := by
    intro a b hab
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hab (hpair hx hy (congrArg (mk Γ) he.symm)).1
  have hfund : IsFundamentalDomain Γ (⋃ c : I, U c) m := by
    apply IsFundamentalDomain.mk' (MeasurableSet.iUnion hU).nullMeasurableSet
    intro x
    obtain ⟨a, ha, _⟩ := fundamentalDomain_unique Λ hΛ x
    let b : Λ := a⁻¹
    let c : I := mk (Γ.comap Λ.subtype) b
    have hbx : b.val * (a.val * x) = x := by simp [b, ← mul_assoc]
    have hc := (mk_mul_subtype_eq_iff Γ Λ b c.out (a.val * x)).mpr (Quotient.out_eq c).symm
    rw [hbx] at hc
    let dlt : Γ := ⟨(c.out.val * (a.val * x)) * x⁻¹, (mk_eq_mk_iff Γ _ _).mp hc⟩
    have hdlt : dlt.val * x = c.out.val * (a.val * x) := by simp [dlt, mul_assoc]
    have hmem : dlt.val * x ∈ ⋃ c : I, U c := by
      rw [hdlt]
      exact mem_iUnion.mpr ⟨c, a.val * x, ha, rfl⟩
    refine ⟨dlt, hmem, ?_⟩
    intro e he
    obtain ⟨c', y, hy, hy'⟩ := mem_iUnion.mp he
    change c'.out.val * y = e.val * x at hy'
    have heq : mk Γ (c'.out.val * y) = mk Γ (c.out.val * (a.val * x)) := by
      rw [hy', mk_subgroup_mul, ← hdlt, mk_subgroup_mul]
    obtain ⟨rfl, rfl⟩ := hpair hy ha heq
    exact Subtype.ext (mul_right_cancel (hy'.symm.trans hdlt.symm))
  rw [discreteQuotientMeasure_eq Γ (hΛ.mono hle) m hfund, quotientMeasure,
    lintegral_map hf (measurable_mk Γ), lintegral_iUnion hU hdisj]
  have hterm (c : I) : Measurable (fun x : H => f (mk Γ (c.out.val * x))) :=
    (hf.comp (measurable_mk Γ)).comp (measurable_const.mul measurable_id)
  rw [lintegral_tsum (fun c : I => (hterm c).aemeasurable)]
  congr 1
  funext c
  exact ((measurePreserving_mul_left m c.out.val).setLIntegral_comp_emb
    (measurableEmbedding_mulLeft _) (f ∘ mk Γ) D).symm

end Integral

end Langlands.Global.LeftCosetSpace
