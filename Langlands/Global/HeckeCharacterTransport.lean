import Langlands.Global.HeckeCharacter
import Langlands.Global.AdelicFunctoriality.Isomorphism

/-! # Arithmetic transport of actual Hecke characters -/

noncomputable section
universe uK uL uM

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open NumberField AdelicFunctoriality

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Pull back along the actual continuous arithmetic equivalence of idele classes. -/
def comap (e : K ≃+* L) (χ : HeckeCharacter L) : HeckeCharacter K :=
  χ.comp (ContinuousMonoidHom.toContinuousMonoidHom (ideleClassEquiv e))

@[simp] theorem comap_apply (e : K ≃+* L) (χ : HeckeCharacter L) (x : IdeleClasses K) :
    comap e χ x = χ (ideleClassEquiv e x) := rfl

@[simp] theorem comap_refl (χ : HeckeCharacter K) :
    comap (RingEquiv.refl K) χ = χ := by
  ext x
  simp only [comap_apply, ideleClassEquiv_refl, ContinuousMulEquiv.refl_apply]

/-- Pullback reverses the direction of a composite field isomorphism. -/
theorem comap_trans (e : K ≃+* L) (f : L ≃+* M) (χ : HeckeCharacter M) :
    comap (e.trans f) χ = comap e (comap f χ) := by
  ext x
  simp only [comap_apply, ideleClassEquiv_trans, ContinuousMulEquiv.trans_apply]

@[simp] theorem comap_one (e : K ≃+* L) : comap e (1 : HeckeCharacter L) = 1 := by
  ext x
  rfl

@[simp] theorem comap_mul (e : K ≃+* L) (χ ψ : HeckeCharacter L) :
    comap e (χ * ψ) = comap e χ * comap e ψ := by
  ext x
  rfl

@[simp] theorem comap_inv (e : K ≃+* L) (χ : HeckeCharacter L) :
    comap e χ⁻¹ = (comap e χ)⁻¹ := by
  ext x
  rfl

@[simp] theorem comap_pow (e : K ≃+* L) (χ : HeckeCharacter L) (n : ℕ) :
    comap e (χ ^ n) = comap e χ ^ n := by
  induction n with
  | zero => simp only [pow_zero, comap_one]
  | succ n ih => rw [pow_succ, comap_mul, ih, pow_succ]

@[simp] theorem comap_symm_comap (e : K ≃+* L) (χ : HeckeCharacter L) :
    comap e.symm (comap e χ) = χ := by
  rw [← comap_trans, RingEquiv.symm_trans_self, comap_refl]

@[simp] theorem comap_comap_symm (e : K ≃+* L) (χ : HeckeCharacter K) :
    comap e (comap e.symm χ) = χ := by
  rw [← comap_trans, RingEquiv.self_trans_symm, comap_refl]

/-- Arithmetic pullback is a multiplicative equivalence of the actual character groups. -/
def comapEquiv (e : K ≃+* L) : HeckeCharacter L ≃* HeckeCharacter K where
  toFun := comap e
  invFun := comap e.symm
  left_inv := comap_symm_comap e
  right_inv := comap_comap_symm e
  map_mul' := comap_mul e

@[simp] theorem comapEquiv_apply (e : K ≃+* L) (χ : HeckeCharacter L) :
    comapEquiv e χ = comap e χ := rfl

@[simp] theorem comapEquiv_symm_apply (e : K ≃+* L) (χ : HeckeCharacter K) :
    (comapEquiv e).symm χ = comap e.symm χ := rfl

/-- Formula on actual idele representatives, before passing to their classes. -/
@[simp] theorem comap_onIdeles (e : K ≃+* L) (χ : HeckeCharacter L) (x : Ideles K) :
    (comap e χ).onIdeles x = χ.onIdeles (ideleEquiv e x) := rfl

/-- Finite local characters transform by the actual completed-field isomorphism. -/
theorem comap_finiteComponent (e : K ≃+* L) (χ : HeckeCharacter L) (v : FinitePlace L)
    (x : (FiniteCompletion K (finitePlaceEquiv e v))ˣ) :
    (comap e χ).finiteComponent (finitePlaceEquiv e v) x =
      χ.finiteComponent v (Units.mapEquiv (finiteCompletionEquiv e v).toMulEquiv x) :=
  congrArg χ (ideleClassEquiv_ofAdicCompletion e v x)

/-- Infinite local characters transform by the actual archimedean completion map. -/
theorem comap_infiniteComponent (e : K ≃+* L) (χ : HeckeCharacter L) (v : InfinitePlace L)
    (x : (InfiniteCompletion K (infinitePlaceEquiv e v))ˣ) :
    (comap e χ).infiniteComponent (infinitePlaceEquiv e v) x =
      χ.infiniteComponent v (Units.mapEquiv (infiniteCompletionEquiv e v).toMulEquiv x) :=
  congrArg χ (ideleClassEquiv_ofCompletion e v x)

/-- Arithmetic transport preserves and reflects unitarity on actual complex values. -/
@[simp] theorem isUnitary_comap_iff (e : K ≃+* L) (χ : HeckeCharacter L) :
    (comap e χ).IsUnitary ↔ χ.IsUnitary := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := (ideleClassEquiv e).surjective y
    exact h x
  · intro h x
    exact h (ideleClassEquiv e x)

/-- The same positive exponent witnesses finite order before and after pullback. -/
@[simp] theorem hasFiniteOrder_comap_iff (e : K ≃+* L) (χ : HeckeCharacter L) :
    (comap e χ).HasFiniteOrder ↔ χ.HasFiniteOrder := by
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, (comapEquiv e).injective ?_⟩
    simpa only [comapEquiv_apply, comap_pow, comap_one] using h
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [← comap_pow, h, comap_one]⟩

private theorem completion_units_integral_iff (e : K ≃+* L) (v : FinitePlace L)
    (x : (FiniteCompletion K (finitePlaceEquiv e v))ˣ) :
    Units.mapEquiv (finiteCompletionEquiv e v).toMulEquiv x ∈
        (Submonoid.ofClass (v.adicCompletionIntegers L)).units ↔
      x ∈ (Submonoid.ofClass ((finitePlaceEquiv e v).adicCompletionIntegers K)).units := by
  simp only [Submonoid.mem_units_iff]
  change (finiteCompletionEquiv e v x.val ∈ v.adicCompletionIntegers L ∧
      finiteCompletionEquiv e v x.inv ∈ v.adicCompletionIntegers L) ↔
    (x.val ∈ (finitePlaceEquiv e v).adicCompletionIntegers K ∧
      x.inv ∈ (finitePlaceEquiv e v).adicCompletionIntegers K)
  simp only [finiteCompletionEquiv_integral]

/-- Unramifiedness is invariant at the exactly corresponding finite places. -/
@[simp] theorem isUnramifiedAt_comap_iff (e : K ≃+* L) (χ : HeckeCharacter L)
    (v : FinitePlace L) :
    (comap e χ).IsUnramifiedAt (finitePlaceEquiv e v) ↔ χ.IsUnramifiedAt v := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (Units.mapEquiv (finiteCompletionEquiv e v).toMulEquiv).surjective y
    rw [← comap_finiteComponent]
    exact h x ((completion_units_integral_iff e v x).mp hy)
  · intro h x hx
    rw [comap_finiteComponent]
    exact h _ ((completion_units_integral_iff e v x).mpr hx)

/-- The actual automorphism group acts on characters by inverse arithmetic pullback. -/
def galoisAut : (K ≃ₐ[ℚ] K) →* (HeckeCharacter K ≃* HeckeCharacter K) where
  toFun σ := comapEquiv σ.toRingEquiv.symm
  map_one' := by
    apply MulEquiv.ext
    intro χ
    exact comap_refl χ
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro χ
    change comap (σ * τ).toRingEquiv.symm χ =
      comap σ.toRingEquiv.symm (comap τ.toRingEquiv.symm χ)
    have h : (σ * τ).toRingEquiv.symm =
        σ.toRingEquiv.symm.trans τ.toRingEquiv.symm := rfl
    rw [h, comap_trans]

@[simp] theorem galoisAut_apply (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K)
    (x : IdeleClasses K) :
    galoisAut σ χ x = χ (ideleClassAut (σ⁻¹) x) := rfl

/-- An installable multiplicative left action, without a global action instance. -/
@[instance_reducible]
def galoisAction : MulDistribMulAction (K ≃ₐ[ℚ] K) (HeckeCharacter K) where
  __ := MulAction.compHom (HeckeCharacter K) galoisAut
  smul_one σ := map_one (galoisAut σ)
  smul_mul σ χ ψ := map_mul (galoisAut σ) χ ψ

@[simp] theorem isUnitary_galoisAut_iff (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) :
    (galoisAut σ χ).IsUnitary ↔ χ.IsUnitary :=
  isUnitary_comap_iff σ.toRingEquiv.symm χ

@[simp] theorem hasFiniteOrder_galoisAut_iff (σ : K ≃ₐ[ℚ] K) (χ : HeckeCharacter K) :
    (galoisAut σ χ).HasFiniteOrder ↔ χ.HasFiniteOrder :=
  hasFiniteOrder_comap_iff σ.toRingEquiv.symm χ

section CM

variable [IsCMField K]

/-- Pullback by the actual arithmetic CM involution. -/
def complexConj (χ : HeckeCharacter K) : HeckeCharacter K :=
  comap (IsCMField.complexConj K).toRingEquiv χ

/-- This is the exact evaluation convention of the existing CM character statements. -/
@[simp] theorem complexConj_apply (χ : HeckeCharacter K) (x : IdeleClasses K) :
    χ.complexConj x = χ (ideleClassComplexConj x) := rfl

@[simp] theorem complexConj_complexConj (χ : HeckeCharacter K) :
    χ.complexConj.complexConj = χ := by
  apply ContinuousMonoidHom.ext
  intro x
  exact congrArg χ (ideleClassComplexConj_involutive x)

@[simp] theorem complexConj_mul (χ ψ : HeckeCharacter K) :
    (χ * ψ).complexConj = χ.complexConj * ψ.complexConj :=
  comap_mul _ χ ψ

@[simp] theorem complexConj_inv (χ : HeckeCharacter K) :
    χ⁻¹.complexConj = χ.complexConj⁻¹ := comap_inv _ χ

/-- Since arithmetic CM conjugation is involutive, the inverse-action convention
reduces to direct CM pullback. -/
@[simp] theorem galoisAut_complexConj (χ : HeckeCharacter K) :
    galoisAut ((IsCMField.complexConj K).restrictScalars ℚ) χ = χ.complexConj := by
  have h : (IsCMField.complexConj K).toRingEquiv.symm =
      (IsCMField.complexConj K).toRingEquiv := by
    apply RingEquiv.ext
    intro x
    apply (IsCMField.complexConj K).injective
    exact ((IsCMField.complexConj K).apply_symm_apply x).trans
      (IsCMField.complexConj_apply_apply K x).symm
  change comap (IsCMField.complexConj K).toRingEquiv.symm χ = χ.complexConj
  rw [h]
  rfl

@[simp] theorem isUnitary_complexConj_iff (χ : HeckeCharacter K) :
    χ.complexConj.IsUnitary ↔ χ.IsUnitary := isUnitary_comap_iff _ χ

@[simp] theorem hasFiniteOrder_complexConj_iff (χ : HeckeCharacter K) :
    χ.complexConj.HasFiniteOrder ↔ χ.HasFiniteOrder := hasFiniteOrder_comap_iff _ χ

end CM
end Langlands.Global.HeckeCharacter
