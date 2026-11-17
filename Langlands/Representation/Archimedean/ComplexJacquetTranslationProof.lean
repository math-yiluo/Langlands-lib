import Langlands.Representation.Archimedean.ComplexJacquetTranslationLift
import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentRoute

/-!
# Translation of Jacquet functionals by exterior powers

Proof of `ComplexJacquetTranslationStatement`. A nonzero Jacquet functional `ℓ` on `X(d)` with
exponents `(a, b)` gives functionals `ℓ_S(h) = ℓ((lift_S h)_{T₀})` on the shifted modules
`X(d + e_S)`, where `T₀` is the set of the last `k` positions. Some `ℓ_S` is nonzero; for one of
minimal weight, `ℓ_S` is a Jacquet functional with exponents shifted by the indicator of `T₀`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Manifold ComplexConjugate TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.JacquetTranslation

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n k : ℕ}

/-- The Lie algebra action on `U(n)`-finite principal-series functions is the right
derivative. -/
theorem coe_lie (d : Fin n → ComplexCharacterData) (X : Matrix (Fin n) (Fin n) ℂ) (v : KX d) :
    ((complexStandardLie n (List.ofFn d) (1 ⊗ₜ X) v : KX d) :
      Langlands.GeneralLinear n ℂ → ℂ) = rightDerivative (matrixModel ℂ n) X v := by
  rw [complexStandardLie, principalSeriesLie, kFiniteLie_one_tmul_apply_coe]

theorem smooth_of_KX {d : Fin n → ComplexCharacterData} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ KX d) : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f :=
  hf.1.1

/-- The functional `ℓ_S(h) = ℓ((lift_S h)_{T₀})` on the shifted module. -/
def ellS (anti : Bool) (d : Fin n → ComplexCharacterData) (hk : k ≤ n) (ℓ : KX d →ₗ[ℂ] ℂ)
    (S : Sub n k) : KX (shiftChar anti d (S : Finset (Fin n))) →ₗ[ℂ] ℂ where
  toFun h := ℓ ⟨lift anti d S h (lowSub n k hk), lift_mem anti d S h.2 _⟩
  map_add' h₁ h₂ := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact lift_add anti d S h₁.2 h₂.2 _
  map_smul' c h := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_smul]
    exact lift_smul anti d S c h.2 _

theorem ellS_apply (anti : Bool) (d : Fin n → ComplexCharacterData) (hk : k ≤ n)
    (ℓ : KX d →ₗ[ℂ] ℂ) (S : Sub n k) (h : KX (shiftChar anti d (S : Finset (Fin n)))) :
    ellS anti d hk ℓ S h = ℓ ⟨lift anti d S h (lowSub n k hk), lift_mem anti d S h.2 _⟩ :=
  rfl

/-- `ℓ` on the `T₀`-entry of a tuple is the sum of the `ℓ_S` on its components. -/
theorem ell_decomp (anti : Bool) {d : Fin n → ComplexCharacterData} (hk : k ≤ n)
    (ℓ : KX d →ₗ[ℂ] ℂ) {G : Sub n k → Langlands.GeneralLinear n ℂ → ℂ} (hG : ∀ T, G T ∈ KX d)
    (hc : Sub n k → Langlands.GeneralLinear n ℂ → ℂ)
    (hcmem : ∀ S : Sub n k, hc S ∈ KX (shiftChar anti d (S : Finset (Fin n))))
    (hcG : ∀ (S : Sub n k) κ, hc S (Unitary.toUnits κ) = piS anti G S (Unitary.toUnits κ)) :
    ℓ ⟨G (lowSub n k hk), hG _⟩ = ∑ S, ellS anti d hk ℓ S ⟨hc S, hcmem S⟩ := by
  have hs := eq_sum_lift anti d hG hc hcmem hcG (lowSub n k hk)
  have he : (⟨G (lowSub n k hk), hG _⟩ : KX d) =
      ∑ S, (⟨lift anti d S (hc S) (lowSub n k hk), lift_mem anti d S (hcmem S) _⟩ : KX d) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hs
  rw [he, map_sum]
  rfl

/-- Some `ℓ_S` is nonzero. -/
theorem exists_ellS_ne_zero (anti : Bool) {d : Fin n → ComplexCharacterData} (hk : k ≤ n)
    {ℓ : KX d →ₗ[ℂ] ℂ} (hℓ : ℓ ≠ 0) : ∃ S : Sub n k, ellS anti d hk ℓ S ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hℓ
  ext f
  rw [LinearMap.zero_apply]
  let F : Sub n k → Langlands.GeneralLinear n ℂ → ℂ :=
    fun T => if T = lowSub n k hk then (f : Langlands.GeneralLinear n ℂ → ℂ) else 0
  have hF : ∀ T, F T ∈ KX d := by
    intro T
    by_cases hT : T = lowSub n k hk
    · simp only [F, if_pos hT]; exact f.2
    · simp only [F, if_neg hT]; exact Submodule.zero_mem _
  choose hc hcmem hcF using fun S => exists_component anti d hF S
  have h1 := ell_decomp anti hk ℓ hF hc hcmem hcF
  have hf : (⟨F (lowSub n k hk), hF _⟩ : KX d) = f := by
    apply Subtype.ext
    simp only [F, if_pos rfl]
  rw [hf] at h1
  rw [h1]
  simp [hcon]

/-- The value of `phi` on a diagonal matrix unit. -/
theorem phi_single_diag (anti : Bool) (j r : Fin n) (z : ℂ) :
    phi anti (Matrix.single j j z) r r = if j = r then fac anti z else 0 := by
  by_cases h : j = r
  · subst h; cases anti <;> simp [phi, fac]
  · cases anti <;> simp [phi, h]

theorem single_upper (j : Fin n) (z : ℂ) :
    ∀ i i' : Fin n, i' < i → Matrix.single j j z i i' = 0 := by
  intro i i' h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact lt_irrefl _ h

/-- The key identity: for an upper triangular direction `X` and a functional `ℓ_S` of minimal
weight among the nonzero ones,
`ℓ_S(X h) = ℓ(X (lift_S h)_{T₀}) + (∑_{r ∈ T₀} φ(X)_{r r}) ℓ_S(h)`. -/
theorem key (anti : Bool) {d : Fin n → ComplexCharacterData} (hk : k ≤ n)
    (ℓ : KX d →ₗ[ℂ] ℂ) (S : Sub n k)
    (hmin : ∀ U : Sub n k, wt U < wt S → ellS anti d hk ℓ U = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i j, j < i → X i j = 0)
    (h : KX (shiftChar anti d (S : Finset (Fin n)))) :
    ellS anti d hk ℓ S
        (complexStandardLie n (List.ofFn (shiftChar anti d (S : Finset (Fin n)))) (1 ⊗ₜ X) h) =
      ℓ (complexStandardLie n (List.ofFn d) (1 ⊗ₜ X)
          ⟨lift anti d S h (lowSub n k hk), lift_mem anti d S h.2 _⟩) +
        (∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti X r r) *
          ellS anti d hk ℓ S h := by
  classical
  set F := lift anti d S (h : Langlands.GeneralLinear n ℂ → ℂ) with hFdef
  have hF : ∀ T, F T ∈ KX d := lift_mem anti d S h.2
  have hFs : ∀ T, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (F T) := fun T => smooth_of_KX (hF T)
  have hG : ∀ T, act anti X F T ∈ KX d := act_mem anti X hF
  choose hc hcmem hcG using fun U => exists_component anti d hG U
  have h1 := ell_decomp anti hk ℓ hG hc hcmem hcG
  -- the components of `F` of weight at least `wt S`
  have hpiF : ∀ U : Sub n k, wt S ≤ wt U →
      piS anti F U = if U = S then (h : Langlands.GeneralLinear n ℂ → ℂ) else 0 := by
    intro U hU
    funext g
    rw [piS_lift anti d S h.2 U hU g]
    split_ifs <;> rfl
  -- the components of the derived tuple
  have hcS : hc S = rightDerivative (matrixModel ℂ n) X (h : Langlands.GeneralLinear n ℂ → ℂ) := by
    refine eq_of_eq_unitary (hcmem S).1
      (rightDerivative_mem_kFiniteFunctions_principalSeries _ _ h.2 X).1 (fun κ => ?_)
    rw [hcG, piS_act anti X hFs, hpiF S le_rfl, if_pos rfl]
  have hcU : ∀ U : Sub n k, wt S ≤ wt U → U ≠ S → hc U = 0 := by
    intro U hU hne
    refine eq_of_eq_unitary (hcmem U).1 (Submodule.zero_mem _) (fun κ => ?_)
    rw [hcG, piS_act anti X hFs, hpiF U hU, if_neg hne,
      ComplexStrictLanglandsQuotient.rightDerivative_zero]
  have h2 : ∑ U, ellS anti d hk ℓ U ⟨hc U, hcmem U⟩ = ellS anti d hk ℓ S ⟨hc S, hcmem S⟩ := by
    refine Finset.sum_eq_single S (fun U _ hne => ?_) (fun h => absurd (Finset.mem_univ S) h)
    by_cases hU : wt U < wt S
    · rw [hmin U hU, LinearMap.zero_apply]
    · have h0 : (⟨hc U, hcmem U⟩ : KX (shiftChar anti d (U : Finset (Fin n)))) = 0 :=
        Subtype.ext (hcU U (not_lt.mp hU) hne)
      rw [h0, map_zero]
  have h3 : (⟨hc S, hcmem S⟩ : KX (shiftChar anti d (S : Finset (Fin n)))) =
      complexStandardLie n (List.ofFn (shiftChar anti d (S : Finset (Fin n)))) (1 ⊗ₜ X) h := by
    apply Subtype.ext
    rw [coe_lie]
    exact hcS
  rw [h2, h3] at h1
  rw [← h1]
  -- the `T₀`-entry of the derived tuple
  have h4 : (⟨act anti X F (lowSub n k hk), hG _⟩ : KX d) =
      complexStandardLie n (List.ofFn d) (1 ⊗ₜ X) ⟨F (lowSub n k hk), hF _⟩ +
        (∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti X r r) •
          (⟨F (lowSub n k hk), hF _⟩ : KX d) := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, coe_lie]
    funext g
    simp only [act, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Dco_low anti hk _ hX]
    simp
  rw [h4, map_add, map_smul, smul_eq_mul]
  rfl

/-- The translated Jacquet functional, for a fixed side. -/
theorem exists_translate (anti : Bool) {d : Fin n → ComplexCharacterData}
    {ℓ : KX d →ₗ[ℂ] ℂ} {a b : Fin n → ℂ} (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b)
    (hk : k ≤ n) :
    ∃ S : Sub n k, ellS anti d hk ℓ S ≠ 0 ∧
      IsComplexJacquetFunctional n
        (complexStandardLie n (List.ofFn (shiftChar anti d (S : Finset (Fin n)))))
        (ellS anti d hk ℓ S)
        (fun j => a j + if n ≤ (j : ℕ) + k then 1 else 0)
        (fun j => b j + Complex.I * ((eps anti : ℤ) : ℂ) * if n ≤ (j : ℕ) + k then 1 else 0) := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_ellS_ne_zero anti hk hℓ
  obtain ⟨S, hS, hSmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun S : Sub n k => ellS anti d hk ℓ S ≠ 0) wt
    ⟨S₀, by simp [hS₀]⟩
  have hSne : ellS anti d hk ℓ S ≠ 0 := by simpa using hS
  have hmin : ∀ U : Sub n k, wt U < wt S → ellS anti d hk ℓ U = 0 := by
    intro U hU
    by_contra hne
    have := hSmin U (by simp [hne])
    omega
  have hsum : ∀ (j : Fin n) (z : ℂ),
      ∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti (Matrix.single j j z) r r =
        (if n ≤ (j : ℕ) + k then 1 else 0) * fac anti z := by
    intro j z
    simp only [phi_single_diag, Finset.sum_ite_eq, mem_lowSub]
    split_ifs <;> simp
  refine ⟨S, hSne, fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · have hX' : ∀ i j, j < i → X i j = 0 := fun i j h => hX i j h.le
    rw [key anti hk ℓ S hmin hX' v, hJ.1 X hX]
    have h0 : ∑ r ∈ ((lowSub n k hk : Sub n k) : Finset (Fin n)), phi anti X r r = 0 := by
      refine Finset.sum_eq_zero (fun r _ => ?_)
      cases anti <;> simp [phi, hX r r le_rfl]
    rw [h0, zero_mul, add_zero]
  · rw [key anti hk ℓ S hmin (single_upper j 1) v, (hJ.2 j _).1, hsum, ← ellS_apply]
    have hf : fac anti 1 = 1 := by cases anti <;> simp [fac]
    rw [hf]
    ring
  · rw [key anti hk ℓ S hmin (single_upper j Complex.I) v, (hJ.2 j _).2, hsum, ← ellS_apply]
    have hf : fac anti Complex.I = Complex.I * ((eps anti : ℤ) : ℂ) := by
      cases anti <;> simp [fac, eps]
    rw [hf]
    ring

end Langlands.Archimedean.JacquetTranslation

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean JacquetTranslation

/-- **Translation of Jacquet functionals by exterior powers.** -/
theorem complexJacquetTranslation : ComplexJacquetTranslationStatement := by
  intro n d ℓ a b hℓ hJ k ε hk hε
  have main : ∀ anti : Bool, ε = eps anti → ∃ (S : Finset (Fin n))
      (d' : Fin n → ComplexCharacterData)
      (ℓ' : kFiniteFunctions (complexStandardModule n (List.ofFn d')) (unitaryCompact ℂ n)
        →ₗ[ℂ] ℂ),
      S.card = k ∧
      (∀ j, (d' j).weight = (d j).weight + if j ∈ S then ε else 0) ∧
      (∀ j, (d' j).exponent = (d j).exponent + if j ∈ S then (1 / 2 : ℂ) else 0) ∧
      ℓ' ≠ 0 ∧
      IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d')) ℓ'
        (fun j => a j + if n ≤ (j : ℕ) + k then 1 else 0)
        (fun j => b j + Complex.I * (ε : ℂ) * if n ≤ (j : ℕ) + k then 1 else 0) := by
    intro anti hεa
    obtain ⟨S, hS, hJ'⟩ := exists_translate anti hℓ hJ hk
    refine ⟨(S : Finset (Fin n)), shiftChar anti d (S : Finset (Fin n)), ellS anti d hk ℓ S,
      S.prop, fun j => ?_, fun j => shiftChar_exponent anti d _ j, hS, ?_⟩
    · rw [shiftChar_weight, hεa]
    · rw [hεa]
      exact hJ'
  rcases hε with rfl | rfl
  · exact main false (by simp [eps])
  · exact main true (by simp [eps])

end Langlands.Archimedean
