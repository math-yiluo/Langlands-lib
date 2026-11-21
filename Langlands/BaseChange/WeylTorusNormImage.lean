import Langlands.BaseChange.RegularCentralizer
import Langlands.BaseChange.WeylIntegrationData

/-! Centralizers and membership in the norm image of a rational Weyl torus. -/

namespace Langlands.BaseChange.WeylTorus

open Langlands.JacquetLanglands

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

/-- The rational points of a Weyl torus commute. -/
theorem val_commute (T : WeylTorus F n) (x y : T.val) : Commute x.val y.val := by
  obtain ⟨a, ha, hT⟩ := T.property
  exact congrArg Subtype.val
    (glCentralizer_mul_comm ha ⟨x.val, hT.symm ▸ x.property⟩
      ⟨y.val, hT.symm ▸ y.property⟩)

/-- Every regular point of a Weyl torus has that torus as its centralizer. -/
theorem glCentralizer_eq (T : WeylTorus F n) {γ : T.val}
    (hγ : γ ∈ T.regularPoints) : glCentralizer γ.val = T.val := by
  obtain ⟨a, _, hT⟩ := T.property
  have ha : a ∈ T.val := hT ▸ (by
    rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] : a ∈ glCentralizer a)
  have hle : T.val ≤ glCentralizer γ.val := by
    intro x hx
    rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact (T.val_commute ⟨x, hx⟩ γ).eq
  refine le_antisymm ?_ hle
  intro x hx
  rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (glCentralizer_mul_comm hγ ⟨x, hx⟩ ⟨a, hle ha⟩)

/-- Over a finite reduced algebra, the centralizer of the base change of a regular
torus point is the extended torus. -/
theorem points_eq_centralizer [Module.Finite F E] [IsReduced E] (T : WeylTorus F n)
    {γ : T.val} (hγ : γ ∈ T.regularPoints) :
    T.points E = Subgroup.centralizer {baseChange F E n γ.val} := by
  ext δ
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hδ
    exact (Subgroup.mem_centralizer_iff.mp hδ _ ⟨γ.val, γ.property, rfl⟩).symm
  · intro hδ
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (commute_of_commute_baseChange hγ
      ((T.val_commute ⟨t, ht⟩ γ).map (baseChange F E n)) hδ).eq

/-- A lift with exact norm at a regular torus point belongs to the extended torus. -/
theorem mem_points_of_cyclicNorm_eq (T : WeylTorus F n) {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) {γ : T.val} (hγ : γ ∈ T.regularPoints)
    {δ : GeneralLinear n E} (hδ : cyclicNorm σ l δ = baseChange F E n γ.val) :
    δ ∈ T.points E := by
  let _ : Module.Finite F E := hσ.1
  let _ : IsReduced E := hσ.2.2.1
  rw [T.points_eq_centralizer hγ, Subgroup.mem_centralizer_singleton_iff]
  have h := entrywiseAut_cyclicNorm σ l δ
  rw [hδ, entrywiseAut_baseChange, hσ.pow_eq_one, entrywiseAut_one_apply] at h
  exact eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using h)

/-- A regular torus point belongs to the torus norm image exactly when it is an
ambient norm. -/
theorem mem_normImage_iff_isNorm (T : WeylTorus F n) {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) {γ : T.val} (hγ : γ ∈ T.regularPoints) :
    γ ∈ T.normImage σ l ↔ IsNorm σ l γ.val := by
  constructor
  · rintro ⟨δ, hδ⟩
    exact ⟨δ.val, 1, by simpa only [inv_one, one_mul, mul_one] using hδ⟩
  · rintro ⟨δ, x, hx⟩
    let δ' := x⁻¹ * δ * entrywiseAut σ n x
    have hδ' : cyclicNorm σ l δ' = baseChange F E n γ.val := by
      simpa only [δ', cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply] using hx
    exact ⟨⟨δ', T.mem_points_of_cyclicNorm_eq hσ hγ hδ'⟩, hδ'⟩

end Langlands.BaseChange.WeylTorus
