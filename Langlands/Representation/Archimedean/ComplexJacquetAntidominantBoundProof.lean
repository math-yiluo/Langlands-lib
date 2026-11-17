import Langlands.Representation.Archimedean.ComplexSphericalJacquetNormalized
import Langlands.Representation.Archimedean.ComplexJacquetTranslationProof
import Langlands.Representation.Archimedean.ComplexStandardHomTransposeProof
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexJacquetCasselmanOsborneProof

/-!
# The weight bound for antidominant Jacquet exponents

Proof of `ComplexJacquetAntidominantBoundStatement`.

* **Spherical case** (`weight_eq_zero_of_spherical`): a nonzero Jacquet functional on `X(d)` with
  exponents `(a, 0)` and `Re a_j + 2j` strictly increasing forces all weights of `d` to vanish.
  Frobenius reciprocity gives a nonzero map `X(d) → X(c)` with `l(c) = 0` and `Re t(c)` strictly
  increasing; its transpose `T' : X(c⁻¹) → X(d⁻¹)` is nonzero, so its kernel is a proper
  `(𝔤, K)`-submodule of the strictly dominant `X(c⁻¹)` and lies in the kernel of the Jacquet
  integral. The spherical vector of `X(c⁻¹)` has nonzero Jacquet integral, so its image under
  `T'` is a nonzero `U(n)`-fixed vector of `X(d⁻¹)`, and all weights of `d` vanish.
* **General case**: translating by holomorphic exterior powers (`complexJacquetTranslation`)
  moves the weights `w ≤ 0` of the exponents to `0`, while the weights of `d` grow by a
  nonnegative vector of total `∑ |w_j|`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace JacquetAntidominantBound

open LocalFactor.Archimedean ComplexPartialJacquet ComplexGramFormula
  ComplexPrincipalSeriesExtension

variable {n : ℕ}

/-- The `U(n)`-finite functions of the standard module of `d`. -/
abbrev KX (d : Fin n → ComplexCharacterData) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)

theorem toUnits_of_mem {g : Langlands.GeneralLinear n ℂ} (hg : g ∈ unitaryCompact ℂ n) :
    g = Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩ : Matrix.unitaryGroup (Fin n) ℂ) :=
  Units.ext rfl

theorem complexPositionWeight_eq_zero :
    ∀ (ds : List ComplexCharacterData), (∀ d ∈ ds, d.weight = 0) →
      ∀ l, ComplexStrictLanglandsQuotient.complexPositionWeight ds l = 0
  | [], _, _ => rfl
  | d :: _, h, 0 => h d (List.mem_cons_self ..)
  | _ :: ds, h, l + 1 =>
      complexPositionWeight_eq_zero ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) l

theorem borelFactor_of_norm_one (l : ℤ) (α : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    borelFactor l α z = z ^ l := by
  simp [borelFactor, hz]

/-- On a nonzero `U(n)`-fixed vector, the character at unitary diagonal matrices is trivial. -/
theorem character_eq_one_of_fixed {d : Fin n → ComplexCharacterData} (F : KX d) (hF : F ≠ 0)
    (hFK : ∀ κ, complexStandardRep n (List.ofFn d) κ F = F) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d))
      (fun i => phaseUnit (a i)) = 1 := by
  have hval : ∀ k ∈ unitaryCompact ℂ n,
      (F : Langlands.GeneralLinear n ℂ → ℂ) k = (F : Langlands.GeneralLinear n ℂ → ℂ) 1 := by
    intro k hk
    have h := congrArg (fun G : KX d => (G : Langlands.GeneralLinear n ℂ → ℂ) 1)
      (hFK ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩)
    simp only [ComplexPermutation.complexStandardRep_apply_apply, one_mul] at h
    rw [← h, ← toUnits_of_mem hk]
  have hF1 : (F : Langlands.GeneralLinear n ℂ → ℂ) 1 ≠ 0 := by
    intro h0
    apply hF
    apply Subtype.ext
    exact ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn F.2.1
      (fun k hk => by rw [hval k hk, h0])
  have h1 := F.2.1.2 (fun i => phaseUnit (a i)) 1 (Unitary.toUnits 1)
  rw [← ComplexPartialJacquet.phaseMatrix_toUnits, mul_one, map_one,
    hval _ (ComplexPermutation.toUnits_mem_unitaryCompact (phaseMatrix a))] at h1
  exact mul_right_cancel₀ hF1 (by rw [one_mul]; exact h1.symm)

/-- A unit complex number whose `l`-th power is `-1`, for `l ≠ 0`. -/
theorem exists_unit_zpow_eq_neg_one {l : ℤ} (hl : l ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ l = -1 := by
  refine ⟨Complex.exp (((Real.pi / l : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_int_mul]
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have : (l : ℂ) * (((Real.pi / l : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- If the character is trivial at all unitary diagonal matrices, all weights vanish. -/
theorem weight_eq_zero_of_character {d : Fin n → ComplexCharacterData}
    (h : ∀ a : Fin n → ℂˣ, principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d))
      (fun i => phaseUnit (a i)) = 1) (j : Fin n) : (d j).weight = 0 := by
  by_contra hj
  obtain ⟨z, hz1, hzl⟩ := exists_unit_zpow_eq_neg_one hj
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    exact zero_ne_one hz1
  set a : Fin n → ℂˣ := Pi.mulSingle j (Units.mk0 z hz0) with hadef
  have hphase : ∀ i, ((phaseUnit (a i) : ℂˣ) : ℂ) = ((a i : ℂˣ) : ℂ) := by
    intro i
    rw [phaseUnit_val]
    by_cases hi : i = j
    · subst hi
      simp [hadef, hz1]
    · simp [hadef, Pi.mulSingle_eq_of_ne hi]
  have hP := h a
  rw [principalSeriesCharacter_ofFn, Finset.prod_eq_single j] at hP
  · rw [borelFactor_of_norm_one _ _ (norm_phaseUnit _), hphase] at hP
    simp only [hadef, Pi.mulSingle_eq_same, Units.val_mk0, hzl] at hP
    norm_num at hP
  · intro i _ hij
    rw [borelFactor_of_norm_one _ _ (norm_phaseUnit _), hphase]
    simp [hadef, Pi.mulSingle_eq_of_ne hij]
  · simp

/-- A nonzero intertwining map out of a strictly dominant principal series with zero weights
forces the weights of the target to vanish: the spherical vector is not in its kernel. -/
theorem weight_eq_zero_of_intertwining {ci di : Fin n → ComplexCharacterData}
    (hcw : ∀ i, (ci i).weight = 0)
    (hdom : ∀ l : ℕ, l + 1 < n → (complexPositionExponent (List.ofFn ci) (l + 1)).re <
      (complexPositionExponent (List.ofFn ci) l).re)
    (T' : KX ci →ₗ[ℂ] KX di) (hT'0 : T' ≠ 0)
    (hT' : IsComplexStandardIntertwining n (complexStandardRep n (List.ofFn di))
      (complexStandardLie n (List.ofFn di)) (List.ofFn ci) T') (j : Fin n) :
    (di j).weight = 0 := by
  have hχ := ComplexStrictLanglandsQuotient.isPhasePower (List.ofFn ci)
  have hph : ∀ (l : ℕ) (z : ℂˣ), complexPositionCharacter (List.ofFn ci) l (phaseUnit z) = 1 := by
    intro l z
    rw [ComplexStrictLanglandsQuotient.complexPositionCharacter_phase,
      complexPositionWeight_eq_zero _ (fun x hx => ?_) l, zpow_zero]
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hcw i
  -- the spherical vector
  obtain ⟨φ, hφ, hφ1⟩ := complexPrincipalSeriesExtension n (List.ofFn ci)
    (fun _ => (1 : ℂ)) continuous_const
    (by
      have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
          fun x : Matrix.unitaryGroup (Fin n) ℂ =>
            (fun _ : Matrix.unitaryGroup (Fin n) ℂ => (1 : ℂ)) (x * k)) ≤
            ℂ ∙ (fun _ : Matrix.unitaryGroup (Fin n) ℂ => (1 : ℂ)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨k, rfl⟩
          exact Submodule.mem_span_singleton_self _)
      exact Submodule.finiteDimensional_of_le hle)
    (fun a κ => by
      rw [mul_one]
      simp [principalSeriesCharacter, hph, norm_phaseUnit])
  -- the kernel of `T'` lies in the kernel of the Jacquet integral
  have hΛ := complexJacquetKernel n (complexPositionCharacter (List.ofFn ci))
    (complexPositionExponent (List.ofFn ci)) hχ.eq hχ.one hχ.norm_phase hdom
    ((LinearMap.ker T').map (KX ci).subtype)
    (by
      rintro _ ⟨f, -, rfl⟩
      exact f.2)
    (by
      rintro k hk _ ⟨f, hf, rfl⟩
      refine ⟨complexStandardRep n (List.ofFn ci) (ComplexPermutation.toUnitary ⟨k, hk⟩) f, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
        rw [hT'.map_rep, hf, map_zero]
      · show ((complexStandardRep n (List.ofFn ci) (ComplexPermutation.toUnitary ⟨k, hk⟩) f :
            KX ci) : Langlands.GeneralLinear n ℂ → ℂ) = Whittaker.rightTranslation ℂ _ k f
        rw [principalSeriesRep_apply_coe, ComplexPermutation.toUnits_toUnitary])
    (by
      rintro X _ ⟨f, hf, rfl⟩
      refine ⟨complexStandardLie n (List.ofFn ci) (1 ⊗ₜ X) f, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
        rw [hT'.map_lie, hf, map_zero]
      · exact principalSeriesLie_one_tmul_apply_coe ℂ n _ X f)
    (by
      obtain ⟨f, hf⟩ : ∃ f, T' f ≠ 0 := by
        by_contra h
        push Not at h
        exact hT'0 (LinearMap.ext h)
      refine ⟨f, f.2, fun hmem => hf ?_⟩
      obtain ⟨g, hg, hgf⟩ := hmem
      have hgf' : g = f := Subtype.ext hgf
      rw [← hgf']
      exact hg)
  have hφΛ := ComplexSphericalJacquetNormalized.jacquet_ne_zero_of_spherical n _ _ hχ hdom hph φ hφ
    (fun k hk => by
      rw [toUnits_of_mem hk]
      exact hφ1 _)
  have hTφ : T' ⟨φ, hφ⟩ ≠ 0 := fun h0 => hφΛ (hΛ φ ⟨⟨φ, hφ⟩, h0, rfl⟩)
  -- the spherical vector is `U(n)`-fixed, hence so is its image
  have hφK : ∀ κ, complexStandardRep n (List.ofFn ci) κ ⟨φ, hφ⟩ = ⟨φ, hφ⟩ := by
    intro κ
    apply Subtype.ext
    refine JacquetTranslation.eq_of_eq_unitary
      (complexStandardRep n (List.ofFn ci) κ ⟨φ, hφ⟩).2.1 hφ.1 (fun κ' => ?_)
    rw [ComplexPermutation.complexStandardRep_apply_apply, ← map_mul]
    change φ (Unitary.toUnits (κ' * κ)) = φ (Unitary.toUnits κ')
    rw [hφ1, hφ1]
  have hFK : ∀ κ, complexStandardRep n (List.ofFn di) κ (T' ⟨φ, hφ⟩) = T' ⟨φ, hφ⟩ := by
    intro κ
    rw [← hT'.map_rep, hφK]
  exact weight_eq_zero_of_character
    (fun a' => character_eq_one_of_fixed (T' ⟨φ, hφ⟩) hTφ hFK a') j

/-- **Spherical case.** A nonzero Jacquet functional on `X(d)` with exponents `(a, 0)` and
`Re a_j + 2j` strictly increasing forces all weights of `d` to vanish. -/
theorem weight_eq_zero_of_spherical {d : Fin n → ComplexCharacterData} {ℓ : KX d →ₗ[ℂ] ℂ}
    {a b : Fin n → ℂ} (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b)
    (hb : ∀ j, b j = 0)
    (ha : ∀ i j : Fin n, i < j → (a i).re + 2 * ((i : ℕ) : ℝ) < (a j).re + 2 * ((j : ℕ) : ℝ))
    (j : Fin n) : (d j).weight = 0 := by
  obtain ⟨c, hca, hcb, B, hB0, hB⟩ := complexJacquetFrobenius n _
    (complexStandardRep n (List.ofFn d)) (complexStandardLie n (List.ofFn d))
    (isComplexGKModule_complexStandardModule n _) ℓ a b hℓ hJ
  have hcw : ∀ i, (complexCharacterDataInv (c i)).weight = 0 := by
    intro i
    have h := hcb i
    rw [hb i] at h
    have h0 : ((c i).weight : ℂ) = 0 := (mul_eq_zero.1 h).resolve_left Complex.I_ne_zero
    simp only [complexCharacterDataInv, neg_eq_zero]
    exact_mod_cast h0
  obtain ⟨T', hT'0, hT'⟩ := ComplexStandardHomTransposeProof.complexStandardHomTranspose n d c B
    hB0 (ComplexPermutation.intertwining_of_embedding hB)
  have hdom : ∀ l : ℕ, l + 1 < n →
      (complexPositionExponent (List.ofFn fun i => complexCharacterDataInv (c i)) (l + 1)).re <
        (complexPositionExponent (List.ofFn fun i => complexCharacterDataInv (c i)) l).re := by
    intro l hl
    have h1 := ComplexBlockLanglandsQuotient.complexPositionExponent_ofFn
      (fun i => complexCharacterDataInv (c i)) ⟨l + 1, hl⟩
    have h2 := ComplexBlockLanglandsQuotient.complexPositionExponent_ofFn
      (fun i => complexCharacterDataInv (c i)) ⟨l, by omega⟩
    simp only at h1 h2
    rw [h1, h2]
    simp only [complexCharacterDataInv, Complex.neg_re]
    have hal := ha ⟨l, by omega⟩ ⟨l + 1, hl⟩ (by simp [Fin.lt_def])
    have r1 := congrArg Complex.re (hca ⟨l + 1, hl⟩)
    have r2 := congrArg Complex.re (hca ⟨l, by omega⟩)
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im, Complex.one_re, zero_mul,
      sub_zero] at r1 r2
    simp only at hal
    push_cast at r1 r2 hal
    linarith
  have hw := weight_eq_zero_of_intertwining hcw hdom T' hT'0 hT' j
  simp only [complexCharacterDataInv, neg_eq_zero] at hw
  exact hw

/-- **Nonpositive weights.** Under the hypotheses of the bound, every weight of `d` is `≤ 0`.
Induction on `∑_j (-w_j)`: holomorphic translation by `Λ^k`, where the last `k` positions are
those with `w_j < 0`, raises these `w_j` by one and the weights of `d` by a `0/1` vector. -/
theorem weight_nonpos : ∀ (N : ℕ) {d : Fin n → ComplexCharacterData} {ℓ : KX d →ₗ[ℂ] ℂ}
    {a b : Fin n → ℂ} {w : Fin n → ℤ}, ℓ ≠ 0 →
    IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
    (∀ j, b j = Complex.I * (w j : ℂ)) → (∀ j, w j ≤ 0) → (∀ i j : Fin n, i ≤ j → w j ≤ w i) →
    (∀ i j : Fin n, i < j → (a i).re + 2 * ((i : ℕ) : ℝ) < (a j).re + 2 * ((j : ℕ) : ℝ)) →
    ∑ j, -w j = (N : ℤ) → ∀ j, (d j).weight ≤ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro d ℓ a b w hℓ hJ hb hw hmono ha hN j
  classical
  by_cases hex : ∃ i, w i < 0
  · set U := Finset.univ.filter (fun i => w i < 0) with hUdef
    have hU : U.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp [hUdef, hi]⟩
    set j₀ := U.min' hU with hj₀def
    have hj₀neg : w j₀ < 0 := by
      have := Finset.min'_mem U hU
      simpa [hUdef] using this
    have hj₀ : ∀ i, w i < 0 ↔ j₀ ≤ i := by
      intro i
      constructor
      · intro hi
        exact Finset.min'_le U i (by simp [hUdef, hi])
      · intro hi
        exact lt_of_le_of_lt (hmono j₀ i hi) hj₀neg
    set k := n - (j₀ : ℕ) with hkdef
    have hk : k ≤ n := Nat.sub_le _ _
    have hlam : ∀ i : Fin n, (n ≤ (i : ℕ) + k ↔ w i < 0) := by
      intro i
      rw [hj₀, Fin.le_def]
      have := j₀.isLt
      omega
    obtain ⟨S, d', ℓ', -, hwt, -, hℓ', hJ'⟩ :=
      complexJacquetTranslation n d ℓ a b hℓ hJ k 1 hk (Or.inl rfl)
    set w' : Fin n → ℤ := fun i => w i + if n ≤ (i : ℕ) + k then 1 else 0 with hw'def
    have hw'le : ∀ i, w' i ≤ 0 := by
      intro i
      simp only [hw'def]
      split_ifs with h
      · have := (hlam i).1 h
        omega
      · have := hw i
        omega
    have hmono' : ∀ i i' : Fin n, i ≤ i' → w' i' ≤ w' i := by
      intro i i' hii'
      have hm := hmono i i' hii'
      have hii'v : (i : ℕ) ≤ (i' : ℕ) := hii'
      simp only [hw'def]
      by_cases h1 : n ≤ (i : ℕ) + k <;> by_cases h2 : n ≤ (i' : ℕ) + k
      · simp only [h1, h2, ite_true]; omega
      · exfalso; omega
      · have hi0 : w i = 0 := le_antisymm (hw i) (not_lt.mp (fun h => h1 ((hlam i).2 h)))
        have hi'0 : w i' < 0 := (hlam i').1 h2
        simp only [h1, h2, ite_true, ite_false]
        omega
      · simp only [h1, h2, ite_false]; omega
    have hb' : ∀ i, b i + Complex.I * ((1 : ℤ) : ℂ) * (if n ≤ (i : ℕ) + k then 1 else 0) =
        Complex.I * (w' i : ℂ) := by
      intro i
      rw [hb i]
      simp only [hw'def]
      split_ifs <;> push_cast <;> ring
    have ha' : ∀ i i' : Fin n, i < i' →
        (a i + if n ≤ (i : ℕ) + k then 1 else 0).re + 2 * ((i : ℕ) : ℝ) <
          (a i' + if n ≤ (i' : ℕ) + k then 1 else 0).re + 2 * ((i' : ℕ) : ℝ) := by
      intro i i' hii'
      have h := ha i i' hii'
      have hii'v : (i : ℕ) < (i' : ℕ) := hii'
      by_cases h1 : n ≤ (i : ℕ) + k <;> by_cases h2 : n ≤ (i' : ℕ) + k
      · simp only [h1, h2, ite_true, Complex.add_re, Complex.one_re]; linarith
      · exfalso; omega
      · simp only [h1, h2, ite_true, ite_false, Complex.add_re, Complex.one_re,
          Complex.zero_re]; linarith
      · simp only [h1, h2, ite_false, Complex.add_re, Complex.zero_re]; linarith
    have hsum_nonneg : 0 ≤ ∑ i, -w' i :=
      Finset.sum_nonneg fun i _ => by have := hw'le i; omega
    have hsum_lt : ∑ i, -w' i < ∑ i, -w i := by
      apply Finset.sum_lt_sum
      · intro i _
        simp only [hw'def]
        split_ifs <;> omega
      · refine ⟨j₀, Finset.mem_univ _, ?_⟩
        have : n ≤ (j₀ : ℕ) + k := (hlam j₀).2 hj₀neg
        simp only [hw'def, this, ite_true]
        omega
    have hN' : ∑ i, -w' i = (((∑ i, -w' i).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hsum_nonneg).symm
    have hlt : (∑ i, -w' i).toNat < N := by omega
    have hJ'' : IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d')) ℓ'
        (fun i => a i + if n ≤ (i : ℕ) + k then 1 else 0)
        (fun i => Complex.I * (w' i : ℂ)) := by
      have h := hJ'
      simp only [hb'] at h
      exact h
    have hd' := ih _ hlt hℓ' hJ'' (fun i => rfl) hw'le hmono' ha' hN' j
    rw [hwt j] at hd'
    split_ifs at hd' <;> omega
  · push Not at hex
    have hw0 : ∀ i, w i = 0 := fun i => le_antisymm (hw i) (hex i)
    have := weight_eq_zero_of_spherical hℓ hJ (fun i => by rw [hb i, hw0 i]; simp) ha j
    omega

end JacquetAntidominantBound

open LocalFactor.Archimedean JacquetAntidominantBound

/-- **The weight bound for antidominant Jacquet exponents.** -/
theorem complexJacquetAntidominantBound : ComplexJacquetAntidominantBoundStatement := by
  intro n d ℓ a b w hℓ hJ hb hw hmono ha
  have hsum_nonneg : 0 ≤ ∑ j, -w j := Finset.sum_nonneg fun j _ => by have := hw j; omega
  have hle := weight_nonpos (∑ j, -w j).toNat hℓ hJ hb hw hmono ha
    (Int.toNat_of_nonneg hsum_nonneg).symm
  -- `∑_j l(d_j) = ∑_j w_j`, from Casselman–Osborne
  obtain ⟨α, β, hab⟩ := complexJacquetCasselmanOsborne n d ℓ a b hℓ hJ
  have h1 : ∑ j, b j = Complex.I * ∑ i, ((d i).weight : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => (hab j).2), ← Finset.mul_sum, Finset.sum_sub_distrib,
      Equiv.sum_comp α (fun i => (d i).exponent + ((d i).weight : ℂ) / 2),
      Equiv.sum_comp β (fun i => (d i).exponent - ((d i).weight : ℂ) / 2),
      ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ j, b j = Complex.I * ∑ j, (w j : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => hb j), Finset.mul_sum]
  have h3 : ∑ i, ((d i).weight : ℂ) = ∑ j, (w j : ℂ) :=
    mul_left_cancel₀ Complex.I_ne_zero (h1.symm.trans h2)
  have h4 : ∑ i, (d i).weight = ∑ j, w j := by exact_mod_cast h3
  refine le_of_eq ?_
  calc ∑ j, |(d j).weight| = ∑ j, -(d j).weight :=
        Finset.sum_congr rfl fun j _ => abs_of_nonpos (hle j)
    _ = -∑ j, (d j).weight := by rw [Finset.sum_neg_distrib]
    _ = -∑ j, w j := by rw [h4]
    _ = ∑ j, |w j| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => (abs_of_nonpos (hw j)).symm


end Langlands.Archimedean
