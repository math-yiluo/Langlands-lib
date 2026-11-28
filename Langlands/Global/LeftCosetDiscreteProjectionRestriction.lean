import Langlands.Global.LeftCosetClosedQuotientMeasure
import Langlands.Global.LeftCosetHaarMeasure

/-! # Exact measure on an injective restriction of a discrete quotient projection -/

noncomputable section

open MeasureTheory Set Topology Function
open scoped Pointwise

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))

/-- A measurable transversal patch injects into the quotient without changing its measure. -/
theorem discreteQuotientMeasure_mk_image_eq_of_injOn (dh : Measure H) [dh.IsMulLeftInvariant]
    {S : Set H} (hS : MeasurableSet S) (hinj : InjOn (mk Γ) S) :
    discreteQuotientMeasure Γ hΓ dh (mk Γ '' S) = dh S := by
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  let D := fundamentalDomain Γ hΓ
  have hD := measurableSet_fundamentalDomain Γ hΓ
  have hs : Pairwise (Disjoint on fun g : Γ => (g • S) ∩ D) := by
    intro g g' hne
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have hg : g⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem.mp hx.1
    have hg' : g'⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem.mp hx'.1
    have he : mk Γ (g⁻¹ • x) = mk Γ (g'⁻¹ • x) :=
      (mk_subgroup_mul Γ g⁻¹ x).trans (mk_subgroup_mul Γ g'⁻¹ x).symm
    have hmul : (g⁻¹ : Γ).val * x = (g'⁻¹ : Γ).val * x := hinj hg hg' he
    exact hne (inv_injective (Subtype.ext (mul_right_cancel hmul)))
  rw [discreteQuotientMeasure, quotientMeasure_apply Γ dh D (measurableSet_image_mk Γ hS),
    preimage_image_mk Γ, iUnion_inter,
    measure_iUnion hs (fun g => (hS.const_smul g).inter hD)]
  exact ((isFundamentalDomain Γ hΓ dh).measure_eq_tsum S).symm

private theorem injOn_mk_fundamentalDomain : InjOn (mk Γ) (fundamentalDomain Γ hΓ) := by
  intro x hx y hy he
  let g : Γ := ⟨y * x⁻¹, (mk_eq_mk_iff Γ x y).mp he⟩
  have heq : g.val * x = y := by simp [g, mul_assoc]
  have hg : g.val * x ∈ fundamentalDomain Γ hΓ := heq.symm ▸ hy
  have h1 : (1 : Γ).val * x ∈ fundamentalDomain Γ hΓ := by simpa using hx
  have h := (fundamentalDomain_unique Γ hΓ x).unique hg h1
  rw [h] at heq
  simpa using heq

variable {Γ hΓ}

/-- A projection between discrete quotients preserves the restricted measures on a
measurable region where it is injective. -/
def DiscreteProjectionRestrictionStatement
    {Λ : Subgroup H} (hle : Γ ≤ Λ) (hΛ : IsDiscrete (Λ : Set H))
    (dh : Measure H) [dh.IsMulLeftInvariant]
    (hΓ : IsDiscrete (Γ : Set H)) : Prop :=
  ∀ A : Set (LeftCosetSpace Γ), MeasurableSet A → InjOn (projectionOfLE hle) A →
      MeasurePreserving (projectionOfLE hle)
        ((discreteQuotientMeasure Γ hΓ dh).restrict A)
        ((discreteQuotientMeasure Λ hΛ dh).restrict (projectionOfLE hle '' A))

/-- Lift the region to the smaller subgroup's fundamental domain and use injectivity
there to compute its measure on the larger quotient. -/
theorem measurePreserving_projectionOfLE_restrict
    {Λ : Subgroup H} (hle : Γ ≤ Λ) (hΛ : IsDiscrete (Λ : Set H))
    (dh : Measure H) [dh.IsMulLeftInvariant] (hΓ : IsDiscrete (Γ : Set H)) :
    DiscreteProjectionRestrictionStatement hle hΛ dh hΓ := by
  intro A hA hinj
  let D := fundamentalDomain Γ hΓ
  have hD := measurableSet_fundamentalDomain Γ hΓ
  let f := projectionOfLE hle
  have hf : Measurable f := measurable_projectionOfLE hle
  refine ⟨hf, ?_⟩
  ext B hB
  let S := (mk Γ ⁻¹' (f ⁻¹' B ∩ A)) ∩ D
  have hS : MeasurableSet S := ((measurable_mk Γ) ((hf hB).inter hA)).inter hD
  have hSinj : InjOn (mk Λ) S := by
    intro x hx y hy heq
    exact injOn_mk_fundamentalDomain Γ hΓ hx.2 hy.2 (hinj hx.1.2 hy.1.2 heq)
  have hBimage : mk Λ '' S = B ∩ f '' A := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.1.1, mk Γ x, hx.1.2, rfl⟩
    · rintro ⟨hBq, y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := mk_surjective Γ y
      obtain ⟨g, hg, _⟩ := fundamentalDomain_unique Γ hΓ x
      have he : mk Γ (g.val * x) = mk Γ x := mk_subgroup_mul Γ g x
      refine ⟨g.val * x, ⟨?_, hg⟩, congrArg f he⟩
      change mk Γ (g.val * x) ∈ f ⁻¹' B ∩ A
      rw [he]
      exact ⟨hBq, hy⟩
  rw [Measure.map_apply hf hB, Measure.restrict_apply (hf hB), Measure.restrict_apply hB,
    discreteQuotientMeasure, quotientMeasure_apply Γ dh D ((hf hB).inter hA),
    ← hBimage, discreteQuotientMeasure_mk_image_eq_of_injOn Λ hΛ dh hS hSinj]

end Langlands.Global.LeftCosetSpace
