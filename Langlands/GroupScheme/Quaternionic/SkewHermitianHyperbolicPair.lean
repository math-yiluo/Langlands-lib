import Langlands.GroupScheme.Quaternionic.AntihermitianForm
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Hyperbolic pairs in skew-hermitian division spaces -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.AntihermitianForm

variable {F : Type u} {D : Type v} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D}
  {V : Type w} [AddCommGroup V] [Module F V] [Module D V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V)

private theorem sub_right (x y z : V) : B x (y - z) = B x y - B x z :=
  (B.toBilin x).map_sub y z

variable [Invertible (2 : F)]

/-- Every nonzero isotropic vector in a separating pairing has an isotropic
  partner with pairing value one. -/
theorem exists_hyperbolicPartner (hB : B.toBilin.SeparatingLeft)
    {x : V} (hx : x ≠ 0) (hxx : B x x = 0) : ∃ y, B x y = 1 ∧ B y y = 0 := by
  obtain ⟨z, hz⟩ : ∃ z, B x z ≠ 0 := by
    by_contra! h
    exact hx (hB x h)
  obtain ⟨y, hxy⟩ : ∃ y, B x y = 1 := by
    refine ⟨τ ((B x z)⁻¹) • z, ?_⟩
    rw [B.smul_right, τ.apply_apply, mul_inv_cancel₀ hz]
  have hyx : B y x = -1 := by rw [B.skew x y, hxy, τ.map_one]
  have hyy : τ (B y y) = -(B y y) := by
    simpa only [neg_neg] using (congrArg Neg.neg (B.skew y y)).symm
  let d := (⅟ (2 : F)) • B y y
  have hd : τ d = -d := by
    change τ ((⅟ (2 : F)) • B y y) = -((⅟ (2 : F)) • B y y)
    rw [τ.map_smul, hyy, smul_neg]
  have hadd : d + d = B y y := invOf_two_smul_add_invOf_two_smul F _
  refine ⟨y - d • x, ?_, ?_⟩
  · rw [B.sub_right, B.smul_right, hxx, zero_mul, sub_zero, hxy]
  · simp only [B.sub_left, B.sub_right, B.smul_left, B.smul_right,
      hxx, hxy, hyx, zero_mul, mul_zero, neg_one_mul, sub_zero, hd, neg_neg]
    change B y y - d - d * 1 = 0
    rw [mul_one, ← hadd]
    abel

/-- A skew hyperbolic pair yields two orthogonal lines with opposite nonzero values. -/
theorem exists_opposite_diagonal_pair (hτ : ∃ a, τ a ≠ a)
    (hB : B.toBilin.SeparatingLeft) {x : V} (hx : x ≠ 0) (hxx : B x x = 0) :
    ∃ u v, B u u ≠ 0 ∧ B v u = 0 ∧ B v v = -(B u u) := by
  obtain ⟨y, hxy, hyy⟩ := B.exists_hyperbolicPartner hB hx hxx
  obtain ⟨a, ha⟩ := hτ
  let t := a - τ a
  have ht : τ t = -t := by
    change τ (a - τ a) = -(a - τ a)
    rw [τ.map_sub, τ.apply_apply, neg_sub]
  have ht0 : t ≠ 0 := fun h => ha (sub_eq_zero.mp h).symm
  have hyx : B y x = -1 := by rw [B.skew x y, hxy, τ.map_one]
  have hpair (a b : D) : B (x + a • y) (x + b • y) = τ b - a := by
    rw [B.add_left, B.add_right, B.add_right, B.smul_right, B.smul_left, B.smul_left,
      B.smul_right, hxx, hxy, hyx, hyy, zero_add, one_mul, zero_mul, mul_zero, add_zero,
      mul_neg, mul_one, sub_eq_add_neg]
  refine ⟨x + t • y, x + (-t) • y, ?_, ?_, ?_⟩
  · rw [hpair, ht]
    have h2 : (2 : F) ≠ 0 := Invertible.ne_zero _
    have hne : t + t ≠ 0 := by
      simpa only [two_smul] using smul_ne_zero h2 ht0
    simpa only [← neg_add, sub_eq_add_neg, neg_ne_zero] using hne
  · rw [hpair, ht, sub_self]
  · rw [hpair, hpair, τ.map_neg, ht, neg_neg]
    abel

/-- A separating isotropic rank-three pairing has an orthogonal basis with opposite
  nonzero values on its first two lines. -/
theorem exists_rankThree_basis_of_isotropic [FiniteDimensional D V]
    (hτ : ∃ a, τ a ≠ a) (hB : B.toBilin.SeparatingLeft) (hr : Module.finrank D V = 3)
    {x : V} (hx : x ≠ 0) (hxx : B x x = 0) :
    ∃ b : Module.Basis (Fin 3) D V,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧
        B (b 0) (b 0) ≠ 0 ∧ B (b 1) (b 1) = -(B (b 0) (b 0)) := by
  obtain ⟨u, v, hu, hvu, hvv⟩ := B.exists_opposite_diagonal_pair hτ hB hx hxx
  let W := B.orthogonalLine u
  let C := B.pullback W.subtype
  let v' : W := ⟨v, hvu⟩
  have hv' : C v' v' ≠ 0 := by
    change B v v ≠ 0
    exact hvv ▸ neg_ne_zero.mpr hu
  let U := C.orthogonalLine v'
  let e₁ := B.splitLine u hu
  let e₂ := C.splitLine v' hv'
  have h₁ := e₁.finrank_eq
  have h₂ := e₂.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self, hr] at h₁ h₂
  change 1 + Module.finrank D W = 3 at h₁
  change 1 + Module.finrank D U = Module.finrank D W at h₂
  let e : (D × (D × U)) ≃ₗ[D] V :=
    ((LinearEquiv.refl D D).prodCongr e₂).trans e₁
  let a := Module.Basis.singleton (Fin 1) D
  let c := (Module.finBasis D U).reindex (finCongr (show Module.finrank D U = 1 by omega))
  let d := (a.prod (a.prod c)).map e
  let p : Fin 1 ⊕ (Fin 1 ⊕ Fin 1) ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let b := d.reindex p
  have hp0 : p.symm 0 = Sum.inl 0 := by
    apply p.injective
    rw [p.apply_symm_apply]
    rfl
  have hp1 : p.symm 1 = Sum.inr (Sum.inl 0) := by
    apply p.injective
    rw [p.apply_symm_apply]
    rfl
  have hp2 : p.symm 2 = Sum.inr (Sum.inr 0) := by
    apply p.injective
    rw [p.apply_symm_apply]
    rfl
  let w : W := (c 0 : U)
  have hb0 : b 0 = u := by
    simp [b, d, a, e, e₁, e₂, hp0]
    change (1 : D) • u + ((0 : W) : V) = u
    simp
  have hb1 : b 1 = v := by
    simp [b, d, a, e, e₁, e₂, v', hp1]
    change (0 : D) • u + v = v
    simp
  have hb2 : b 2 = (w : V) := by
    simp [b, d, a, e, e₁, e₂, w, hp2]
    change (0 : D) • u + (w : V) = w
    simp
  have hwu : B (w : V) u = 0 := w.property
  have hwv : B (w : V) v = 0 := (c 0).property
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hb0.symm ▸ hb1.symm ▸ (by rw [B.skew v u, hvu, τ.map_zero, neg_zero] : B u v = 0)
    · exact hb0.symm ▸ hb2.symm ▸ (by rw [B.skew (w : V) u, hwu, τ.map_zero, neg_zero] : B u w = 0)
    · exact hb1.symm ▸ hb0.symm ▸ hvu
    · exact (hij rfl).elim
    · exact hb1.symm ▸ hb2.symm ▸ (by rw [B.skew (w : V) v, hwv, τ.map_zero, neg_zero] : B v w = 0)
    · exact hb2.symm ▸ hb0.symm ▸ hwu
    · exact hb2.symm ▸ hb1.symm ▸ hwv
    · exact (hij rfl).elim
  · simpa only [hb0] using hu
  · simpa only [hb0, hb1] using hvv

/-- An isotropic left-separating antihermitian pairing of rank three over a division
  algebra admits an orthogonal basis with opposite nonzero values on two lines. -/
def RankThreeIsotropicBasisStatement : Prop :=
  ∀ (F : Type u) (D : Type v) [Field F] [DivisionRing D] [Algebra F D]
    [Invertible (2 : F)] (τ : FirstKindInvolution F D) (V : Type w) [AddCommGroup V]
    [Module F V] [Module D V] [IsScalarTower F D V] [FiniteDimensional D V]
    (B : AntihermitianForm τ V), (∃ a, τ a ≠ a) → B.toBilin.SeparatingLeft →
    Module.finrank D V = 3 → (∃ x, x ≠ 0 ∧ B x x = 0) →
    ∃ b : Module.Basis (Fin 3) D V,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧
        B (b 0) (b 0) ≠ 0 ∧ B (b 1) (b 1) = -(B (b 0) (b 0))

theorem rankThreeIsotropicBasis : RankThreeIsotropicBasisStatement.{u, v, w} := by
  intro F D _ _ _ _ τ V _ _ _ _ _ B hτ hB hr ⟨x, hx, hxx⟩
  exact B.exists_rankThree_basis_of_isotropic hτ hB hr hx hxx

end Langlands.GroupScheme.Quaternionic.AntihermitianForm
