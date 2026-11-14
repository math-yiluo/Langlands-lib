import Langlands.Representation.KFiniteDual
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction
import Langlands.Global.ArchimedeanCompact
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The `U(n)`-finite contragredient of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module

For an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on `V`, the `U(n)`-finite
linear functionals on `V` form an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ', π')`,
with `ρ'(k) w = w ∘ ρ(k)⁻¹` and `π'(Y) w = -(w ∘ π(Y))`. The evaluation pairing proves
`ComplexContragredientStatement`.
-/

noncomputable section

open scoped TensorProduct Matrix MonoidAlgebra

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexContragredient

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.KFiniteDual

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

section Algebra

/-- Conjugating back by `k⁻¹` undoes the conjugation by `k`. -/
theorem inv_conj_conj (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ((k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        ((k : Matrix (Fin n) (Fin n) ℂ) * X * star (k : Matrix (Fin n) (Fin n) ℂ)) *
        star ((k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = X := by
  have h1 : star (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self k
  change star (k : Matrix (Fin n) (Fin n) ℂ) *
      ((k : Matrix (Fin n) (Fin n) ℂ) * X * star (k : Matrix (Fin n) (Fin n) ℂ)) *
      star (star (k : Matrix (Fin n) (Fin n) ℂ)) = X
  rw [star_star]
  calc star (k : Matrix (Fin n) (Fin n) ℂ) *
        ((k : Matrix (Fin n) (Fin n) ℂ) * X * star (k : Matrix (Fin n) (Fin n) ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ) =
      (star (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)) * X *
        (star (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]

/-- `ρ(k)⁻¹ π(k X k*) = π(X) ρ(k)⁻¹`. -/
theorem rho_inv_pi (hgk : IsComplexGKModule n ρ π) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    ρ k⁻¹ (π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X *
        star (k : Matrix (Fin n) (Fin n) ℂ))) v) = π (1 ⊗ₜ X) (ρ k⁻¹ v) := by
  rw [hgk.2.2.2 k⁻¹, inv_conj_conj]

/-- The derivative at `0` of a curve in `U(n)` through `1` is skew-Hermitian. -/
theorem star_eq_neg_of_hasDerivAt (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0)
    (i j : Fin n) : star (X j i) = -X i j := by
  have hd : HasDerivAt
      (fun t => ∑ l, star ((γ t : Matrix (Fin n) (Fin n) ℂ) l i) *
        (γ t : Matrix (Fin n) (Fin n) ℂ) l j)
      (∑ l, (star (X l i) * (γ 0 : Matrix (Fin n) (Fin n) ℂ) l j +
        star ((γ 0 : Matrix (Fin n) (Fin n) ℂ) l i) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ => ((hγ l i).star).mul (hγ l j)
  have hc : (fun t => ∑ l, star ((γ t : Matrix (Fin n) (Fin n) ℂ) l i) *
      (γ t : Matrix (Fin n) (Fin n) ℂ) l j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
    funext t
    rw [← Matrix.UnitaryGroup.star_mul_self (γ t), Matrix.mul_apply]
    rfl
  rw [hc] at hd
  have h := (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).unique hd
  rw [h0] at h
  simp [Matrix.one_apply, Finset.sum_add_distrib] at h
  rw [show star (X j i) = (starRingEnd ℂ) (X j i) from rfl]
  linear_combination -h

/-- The derivative of `t ↦ (ρ'(γ t) w)(p)` for the dual action. -/
theorem hasDerivAt_dual (hgk : IsComplexGKModule n ρ π)
    (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0)
    (w : Module.Dual ℂ V) (p : V) :
    HasDerivAt (fun t => ρ.dual (γ t) w p) (-(w (π (1 ⊗ₜ X) p))) 0 := by
  let γ' : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => (γ t)⁻¹
  have h0' : γ' 0 = 1 := by simp [γ', h0]
  have hγ' : ∀ i j, HasDerivAt (fun t => (γ' t : Matrix (Fin n) (Fin n) ℂ) i j) ((-X) i j) 0 := by
    intro i j
    have h := (hγ j i).star
    rw [star_eq_neg_of_hasDerivAt γ X h0 hγ i j] at h
    exact h
  have hd := hgk.2.2.1 γ' (-X) h0' hγ' p w
  rw [TensorProduct.tmul_neg, map_neg, LinearMap.neg_apply, map_neg] at hd
  exact hd

end Algebra

section DualAction

/-- `ρ'(k)(w ∘ π(1 ⊗ X)) = ρ'(k)(w) ∘ π(1 ⊗ k X k*)`. -/
theorem dual_dualMap_one_tmul (hgk : IsComplexGKModule n ρ π)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (w : Module.Dual ℂ V) :
    ρ.dual k ((π (1 ⊗ₜ X)).dualMap w) =
      (π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X *
        star (k : Matrix (Fin n) (Fin n) ℂ)))).dualMap (ρ.dual k w) := by
  apply LinearMap.ext
  intro v
  rw [dual_apply_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, dual_apply_apply,
    rho_inv_pi hgk]

/-- `w ∘ π(1 ⊗ X)` is finite when `w` is. -/
theorem isFiniteVector_dualMap_one_tmul (hgk : IsComplexGKModule n ρ π)
    (X : Matrix (Fin n) (Fin n) ℂ) {w : Module.Dual ℂ V}
    (hw : FiniteVectors.IsFiniteVector ρ.dual w) :
    FiniteVectors.IsFiniteVector ρ.dual ((π (1 ⊗ₜ X)).dualMap w) := by
  let O := FiniteVectors.orbitSpan ρ.dual w
  have : FiniteDimensional ℂ O := hw
  let e := Module.finBasis ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
  let Ψ : (Fin (Module.finrank ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) → O) →ₗ[ℂ]
      Module.Dual ℂ V :=
    ∑ b, (π (e b)).dualMap ∘ₗ O.subtype ∘ₗ LinearMap.proj b
  have hΨ : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (u : Module.Dual ℂ V), u ∈ O →
      (π (1 ⊗ₜ Z)).dualMap u ∈ LinearMap.range Ψ := by
    intro Z u hu
    refine ⟨fun b => e.repr (1 ⊗ₜ Z) b • ⟨u, hu⟩, ?_⟩
    apply LinearMap.ext
    intro v
    simp [Ψ, LinearMap.sum_apply]
    conv_rhs => rw [← e.sum_repr (1 ⊗ₜ Z)]
    rw [map_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  have hle : FiniteVectors.orbitSpan ρ.dual ((π (1 ⊗ₜ X)).dualMap w) ≤ LinearMap.range Ψ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change ρ.dual k ((π (1 ⊗ₜ X)).dualMap w) ∈ _
    rw [dual_dualMap_one_tmul hgk]
    exact hΨ _ _ (FiniteVectors.action_mem_orbitSpan _ k w)
  exact Submodule.finiteDimensional_of_le hle

/-- `w ∘ π(Y)` is finite when `w` is. -/
theorem dualMap_mem_kDual (hgk : IsComplexGKModule n ρ π)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) {w : Module.Dual ℂ V} (hw : w ∈ kDual ρ) :
    (π Y).dualMap w ∈ kDual ρ := by
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have hcX : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h : (π (c ⊗ₜ[ℝ] X)).dualMap w = c • (π (1 ⊗ₜ[ℝ] X)).dualMap w := by
      apply LinearMap.ext
      intro v
      rw [hcX]
      simp
    rw [h]
    exact Submodule.smul_mem _ c (isFiniteVector_dualMap_one_tmul hgk X hw)
  | add Y₁ Y₂ h₁ h₂ =>
    have h : (π (Y₁ + Y₂)).dualMap w = (π Y₁).dualMap w + (π Y₂).dualMap w := by
      apply LinearMap.ext
      intro v
      simp
    rw [h]
    exact Submodule.add_mem _ h₁ h₂

variable (hgk : IsComplexGKModule n ρ π)

/-- The endomorphism `w ↦ -(w ∘ π(Y))` of the finite dual. -/
def dualEnd (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (kDual ρ) :=
  (-(π Y).dualMap).restrict fun w hw => by
    rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (dualMap_mem_kDual hgk Y hw)

theorem dualEnd_apply_apply (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (w : kDual ρ) (v : V) :
    ((dualEnd hgk Y w : kDual ρ) : Module.Dual ℂ V) v = -((w : Module.Dual ℂ V) (π Y v)) :=
  rfl

/-- `Y ↦ π'(Y)` as a linear map. -/
def dualLinear : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ[ℂ] Module.End ℂ (kDual ρ) where
  toFun := dualEnd hgk
  map_add' Y₁ Y₂ := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [dualEnd_apply_apply, LinearMap.add_apply, Submodule.coe_add, map_add]
    ring
  map_smul' c Y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [dualEnd_apply_apply, LinearMap.smul_apply, Submodule.coe_smul, map_smul,
      RingHom.id_apply, smul_eq_mul]
    ring

/-- The Lie algebra action `π'(Y) w = -(w ∘ π(Y))` on the finite dual. -/
def dualLie : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (kDual ρ) :=
  { dualLinear hgk with
    map_lie' := by
      intro x y
      rw [LinearMap.toFun_eq_coe]
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      change -((w : Module.Dual ℂ V) (π ⁅x, y⁆ v)) = _
      rw [LieHom.map_lie]
      simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
        Submodule.coe_sub, map_sub]
      change _ = -(((dualLinear hgk y w : kDual ρ) : Module.Dual ℂ V) (π x v)) -
        -(((dualLinear hgk x w : kDual ρ) : Module.Dual ℂ V) (π y v))
      change _ = -(-((w : Module.Dual ℂ V) (π y (π x v)))) -
        -(-((w : Module.Dual ℂ V) (π x (π y v))))
      ring }

theorem dualLie_apply_apply (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (w : kDual ρ) (v : V) :
    ((dualLie hgk Y w : kDual ρ) : Module.Dual ℂ V) v = -((w : Module.Dual ℂ V) (π Y v)) :=
  rfl

/-- Clause 3 of `IsComplexGKModule` for the finite dual. -/
theorem hasDerivAt_kDual (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0)
    (w : kDual ρ) (ℓ : kDual ρ →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => ℓ (kDualRep ρ (γ t) w)) (ℓ (dualLie hgk (1 ⊗ₜ X) w)) 0 := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (kDualRep ρ) w) :=
    isFiniteVector_kDualRep w
  let S := FiniteVectors.orbitSpan (kDualRep ρ) w ⊔ Submodule.span ℂ {dualLie hgk (1 ⊗ₜ X) w}
  let e : V → (kDual ρ →ₗ[ℂ] ℂ) := fun v => Module.Dual.eval ℂ V v ∘ₗ (kDual ρ).subtype
  obtain ⟨m, p, a, h⟩ := exists_sum_of_separating_family e S
    (fun s _ hs => Subtype.ext (LinearMap.ext fun v => hs v)) ℓ
  have hfun : (fun t => ℓ (kDualRep ρ (γ t) w)) =
      fun t => ∑ i, a i * ρ.dual (γ t) (w : Module.Dual ℂ V) (p i) := by
    funext t
    rw [h _ (Submodule.mem_sup_left (FiniteVectors.action_mem_orbitSpan _ (γ t) w))]
    rfl
  have hval : ℓ (dualLie hgk (1 ⊗ₜ X) w) =
      ∑ i, a i * -((w : Module.Dual ℂ V) (π (1 ⊗ₜ X) (p i))) := by
    rw [h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
    rfl
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_dual hgk γ X h0 hγ w (p i)).const_mul (a i)

/-- Clause 4 of `IsComplexGKModule` for the finite dual. -/
theorem kDualRep_dualLie (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (w : kDual ρ) :
    kDualRep ρ k (dualLie hgk (1 ⊗ₜ X) w) =
      dualLie hgk (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X *
        (star k : Matrix (Fin n) (Fin n) ℂ))) (kDualRep ρ k w) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  rw [coe_kDualRep_apply, dual_apply_apply, dualLie_apply_apply, dualLie_apply_apply,
    coe_kDualRep_apply, dual_apply_apply]
  congr 1
  exact congrArg (w : Module.Dual ℂ V) (rho_inv_pi hgk k X v).symm

theorem isComplexGKModule_kDual : IsComplexGKModule n (kDualRep ρ) (dualLie hgk) :=
  ⟨isFiniteVector_kDualRep, continuous_kDualRep hgk.2.1, hasDerivAt_kDual hgk,
    kDualRep_dualLie hgk⟩

/-- The finite dual of an irreducible admissible module is irreducible. -/
theorem isIrreducible_kDual (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) :
    IsIrreducibleGKModule (kDualRep ρ) (dualLie hgk) := by
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ] ρ.asModule :=
    isSemisimpleModule hgk.1 hgk.2.1
  have hblock := finiteDimensional_block hgk.1 hgk.2.1 hadm
  refine ⟨?_, ?_⟩
  · have := hirr.1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨ℓ, hℓ, hℓv⟩ := exists_isFiniteVector_apply_ne_zero hblock hv
    refine ⟨⟨⟨ℓ, hℓ⟩, 0, fun h => hℓv ?_⟩⟩
    have h' := congrArg (fun w : kDual ρ => (w : Module.Dual ℂ V) v) h
    simpa using h'
  · intro W₀ hW₀ρ hW₀π
    let A : Submodule ℂ V := (W₀.map (kDual ρ).subtype).dualCoannihilator
    have hAρ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ v ∈ A, ρ k v ∈ A := by
      intro k v hv
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      rintro _ ⟨w, hw, rfl⟩
      have h1 := hv _ ⟨_, hW₀ρ k⁻¹ w hw, rfl⟩
      change (ρ.dual k⁻¹ (w : Module.Dual ℂ V)) v = 0 at h1
      rw [dual_inv_apply_apply] at h1
      exact h1
    have hAπ : ∀ (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ v ∈ A, π Y v ∈ A := by
      intro Y v hv
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      rintro _ ⟨w, hw, rfl⟩
      have h1 := hv _ ⟨_, hW₀π Y w hw, rfl⟩
      change -((w : Module.Dual ℂ V) (π Y v)) = 0 at h1
      exact neg_eq_zero.mp h1
    rcases hirr.2 A hAρ hAπ with hA | hA
    · right
      let W' : Subrepresentation ρ.dual :=
        { toSubmodule := W₀.map (kDual ρ).subtype
          apply_mem_toSubmodule := by
            rintro k _ ⟨w, hw, rfl⟩
            exact ⟨_, hW₀ρ k w hw, rfl⟩ }
      have hW' : ∀ x ∈ W', FiniteVectors.IsFiniteVector ρ.dual x := by
        rintro _ ⟨w, -, rfl⟩
        exact w.2
      have hsep : ∀ v : V, (∀ x ∈ W', x v = 0) → v = 0 := by
        intro v hv
        have hvA : v ∈ A := (Submodule.mem_dualCoannihilator _).mpr hv
        rw [hA] at hvA
        exact (Submodule.mem_bot ℂ).mp hvA
      rw [eq_top_iff]
      rintro w -
      obtain ⟨w', hw', hw'w⟩ := mem_of_separating hblock W' hW' hsep w.2
      have hw'eq : w' = w := Subtype.ext hw'w
      rw [← hw'eq]
      exact hw'
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      have hv : v ∈ A := hA ▸ Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator _).mp hv _ ⟨w, hw, rfl⟩

end DualAction

/-- `ComplexContragredientStatement` holds: the finite dual with the evaluation pairing. -/
theorem complexContragredientStatement : ComplexContragredientStatement.{uV} := by
  intro n V _ _ ρ π hgk hirr hadm
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ] ρ.asModule :=
    isSemisimpleModule hgk.1 hgk.2.1
  have hblock := finiteDimensional_block hgk.1 hgk.2.1 hadm
  refine ⟨kDual ρ, inferInstance, inferInstance, kDualRep ρ, dualLie hgk,
    isComplexGKModule_kDual hgk, isIrreducible_kDual hgk hirr hadm,
    admissible_kDual hgk.1 hgk.2.1 hadm, (kDual ρ).subtype, ?_, ?_, ?_, ?_⟩
  · intro k w v
    change (ρ.dual k (w : Module.Dual ℂ V)) (ρ k v) = (w : Module.Dual ℂ V) v
    rw [dual_apply_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  · intro Y w v
    change -((w : Module.Dual ℂ V) (π Y v)) + (w : Module.Dual ℂ V) (π Y v) = 0
    exact neg_add_cancel _
  · intro v hv
    by_contra hne
    obtain ⟨ℓ, hℓ, hℓv⟩ := exists_isFiniteVector_apply_ne_zero hblock hne
    exact hℓv (hv ⟨ℓ, hℓ⟩)
  · intro ℓ hℓ
    exact exists_eq_eval hgk.1 hgk.2.1 hadm hℓ

end Langlands.Archimedean.ComplexContragredient
