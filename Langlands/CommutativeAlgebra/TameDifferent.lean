import Langlands.MathlibBase
import Langlands.LocalFactor.BrauerKernel.Trace

/-!
# Traces on Artinian local algebras and the tame different

Let `B` be a Dedekind domain, finite and torsion-free over a Dedekind domain `A`, with the
fraction field of `B` separable over that of `A`, and let `P` be a maximal ideal of `B` over a
nonzero maximal ideal `p` of `A`, with ramification index `e` and with `B ⧸ P` separable over
`A ⧸ p`. If `e` is nonzero in `A ⧸ p`, the exponent of `P` in the different ideal of `B / A` is
`e - 1` (Serre, *Local Fields*, III §6, Prop. 13).

* `trace_smulEnd_eq_length_nsmul`: over a local `k`-algebra `R`, the `k`-trace of multiplication
  by `r` on an `R`-module finite-dimensional over `k` is its `R`-module length times the trace of
  `r` on the residue field.
* `trace_quotient_pow`: the trace over `A ⧸ p` on `B ⧸ P ^ n` is `n` times the trace on `B ⧸ P`.
* `pow_ramificationIdx_sub_one_dvd_differentIdeal`, `not_pow_ramificationIdx_dvd_differentIdeal`
  and `count_normalizedFactors_differentIdeal`: the tame different.
* `isSeparable_fractionRing` and `count_normalizedFactors_differentIdeal_of_isSeparable`: the
  separability hypothesis on given fraction fields `K` of `A` and `L` of `B`.
-/

noncomputable section

open IsLocalRing Module

namespace Langlands.CommutativeAlgebra.TameDifferent

section Trace

variable (k : Type*) [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- Multiplication by `r : R` on an `R`-module `M`, as a `k`-linear endomorphism. -/
abbrev smulEnd (M : Type*) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (r : R) : M →ₗ[k] M :=
  (LinearMap.lsmul R M r).restrictScalars k

variable {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem trace_smulEnd_eq_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module k M'] [IsScalarTower k R M'] (e : M ≃ₗ[R] M') (r : R) :
    LinearMap.trace k M (smulEnd k M r) = LinearMap.trace k M' (smulEnd k M' r) := by
  rw [← LinearMap.trace_conj' (smulEnd k M r) (e.restrictScalars k)]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply]

theorem trace_smulEnd_eq_add [FiniteDimensional k M] (N : Submodule R M) (r : R) :
    LinearMap.trace k M (smulEnd k M r) =
      LinearMap.trace k N (smulEnd k N r) + LinearMap.trace k (M ⧸ N) (smulEnd k (M ⧸ N) r) := by
  have hW : N.restrictScalars k ≤ (N.restrictScalars k).comap (smulEnd k M r) :=
    fun x hx ↦ N.smul_mem r hx
  rw [Langlands.LocalFactor.BrauerKernel.trace_eq_trace_restrict_add_trace_mapQ
    (N.restrictScalars k) (smulEnd k M r) hW]
  congr 1

theorem trace_smulEnd_bot (r : R) :
    LinearMap.trace k (⊥ : Submodule R M) (smulEnd k (⊥ : Submodule R M) r) = 0 := by
  have : smulEnd k (⊥ : Submodule R M) r = 0 := Subsingleton.elim _ _
  rw [this, map_zero]

theorem trace_smulEnd_quotient_maximalIdeal [IsLocalRing R] (r : R) :
    LinearMap.trace k (R ⧸ maximalIdeal R) (smulEnd k (R ⧸ maximalIdeal R) r) =
      Algebra.trace k (R ⧸ maximalIdeal R) (Ideal.Quotient.mk _ r) := by
  rw [Algebra.trace_apply]
  congr 1

theorem trace_smulEnd_covBy [IsLocalRing R] [FiniteDimensional k M] {p q : Submodule R M}
    (h : p ⋖ q) (r : R) :
    LinearMap.trace k q (smulEnd k q r) = LinearMap.trace k p (smulEnd k p r) +
      Algebra.trace k (R ⧸ maximalIdeal R) (Ideal.Quotient.mk _ r) := by
  let W : Submodule R q := p.comap q.subtype
  have hsimple : IsSimpleModule R (q ⧸ W) := (covBy_iff_quot_is_simple h.le).mp h
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  have : FiniteDimensional k q :=
    Module.Finite.of_injective (q.subtype.restrictScalars k) Subtype.val_injective
  rw [trace_smulEnd_eq_add k W r, trace_smulEnd_eq_of_linearEquiv k
    (Submodule.comapSubtypeEquivOfLe h.le) r, trace_smulEnd_eq_of_linearEquiv k e r,
    trace_smulEnd_quotient_maximalIdeal]

/-- **The trace of multiplication on a module of finite length over a local algebra.** Let `R`
be a local `k`-algebra over a field `k` and `M` an `R`-module that is finite-dimensional over
`k`. Then the trace over `k` of multiplication by `r` on `M` is the length of `M` times the
trace of `r` on the residue field of `R`. -/
theorem trace_smulEnd_eq_length_nsmul [IsLocalRing R] [FiniteDimensional k M] (r : R) :
    LinearMap.trace k M (smulEnd k M r) =
      (Module.length R M).toNat • Algebra.trace k (R ⧸ maximalIdeal R) (Ideal.Quotient.mk _ r) := by
  have hfin : IsFiniteLength R M := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
  rw [← Module.length_compositionSeries s hs₁ hs₂, ENat.toNat_natCast]
  have key : ∀ i : Fin (s.length + 1), LinearMap.trace k (s i) (smulEnd k (s i) r) =
      (i : ℕ) • Algebra.trace k (R ⧸ maximalIdeal R) (Ideal.Quotient.mk _ r) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have : s 0 = ⊥ := hs₁
      rw [Fin.val_zero, zero_nsmul, this, trace_smulEnd_bot]
    | succ i ih =>
      rw [trace_smulEnd_covBy k (s.step i) r, ih, Fin.val_succ, Fin.val_castSucc, succ_nsmul]
  have hlast : s (Fin.last s.length) = ⊤ := hs₂
  rw [← trace_smulEnd_eq_of_linearEquiv k (Submodule.topEquiv (R := R) (M := M)) r,
    ← hlast, key, Fin.val_last]

end Trace

section Dedekind

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain B]
  (p : Ideal A) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p]

/-- **The trace on `B ⧸ P ^ n`.** Let `B` be a Dedekind domain, finite over `A`, and `P` a nonzero
maximal ideal of `B` over a maximal ideal `p` of `A` with `p B ⊆ P ^ n`. Then the trace of the
class of `x` on `B ⧸ P ^ n` over the field `A ⧸ p` is `n` times its trace on `B ⧸ P`. -/
theorem trace_quotient_pow (hP : P ≠ ⊥) (n : ℕ) (hn : p ≤ (P ^ n).comap (algebraMap A B))
    [Module.Finite A B] (x : B) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap hn
    Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ x) =
      n • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ x) := by
  let := Ideal.Quotient.algebraQuotientOfLEComap hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have : Subsingleton (B ⧸ P ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; infer_instance
    rw [zero_nsmul, Algebra.trace_apply,
      show Algebra.lmul (A ⧸ p) (B ⧸ P ^ 0) (Ideal.Quotient.mk _ x) = 0 from Subsingleton.elim _ _,
      map_zero]
  let Sq := Localization.AtPrime P
  have : IsDiscreteValuationRing Sq :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP Sq
  let R := Sq ⧸ maximalIdeal Sq ^ n
  have hmem : ∀ b : B, algebraMap B Sq b ∈ maximalIdeal Sq ^ n ↔ b ∈ P ^ n := fun b ↦ by
    rw [← Ideal.mem_comap, ← Ideal.under_def,
      IsLocalization.AtPrime.under_maximalIdeal_pow P Sq n]
  have hn' : p ≤ (maximalIdeal Sq ^ n).comap (algebraMap A Sq) := fun a ha ↦ by
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A B Sq, hmem]
    exact hn ha
  let : Algebra (A ⧸ p) R := Ideal.Quotient.algebraQuotientOfLEComap hn'
  let φ := IsLocalization.AtPrime.equivQuotMaximalIdealPow P Sq n
  let ψ : (B ⧸ P ^ n) ≃ₐ[A ⧸ p] R :=
    { φ.toRingEquiv with
      commutes' := by
        rintro ⟨a⟩
        change φ (Ideal.Quotient.mk _ (algebraMap A B a)) = Ideal.Quotient.mk _ (algebraMap A Sq a)
        rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
          ← IsScalarTower.algebraMap_apply] }
  have hψ : ψ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap B Sq x) := rfl
  rw [← Algebra.trace_eq_of_algEquiv ψ, hψ]
  -- `R` is a local Artinian `A ⧸ p`-algebra of length `n`.
  have hne : maximalIdeal Sq ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal Sq).ne_top (Ideal.pow_le_self hn0.ne')
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing R := .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite A (B ⧸ P ^ n) := Module.Finite.of_surjective
    ((Ideal.Quotient.mkₐ A (P ^ n)).toLinearMap) (Ideal.Quotient.mkₐ_surjective A _)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ n) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ n)
  have : Module.Finite (A ⧸ p) R := Module.Finite.equiv ψ.toLinearEquiv
  have hlen : (Module.length R R).toNat = n := by
    rw [← Module.length_eq_of_surjective (S := Sq) (R := R) (M := R) Ideal.Quotient.mk_surjective,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  have htr := trace_smulEnd_eq_length_nsmul (A ⧸ p) (M := R)
    (Ideal.Quotient.mk (maximalIdeal Sq ^ n) (algebraMap B Sq x))
  rw [hlen] at htr
  rw [Algebra.trace_apply]
  refine (htr.trans ?_)
  congr 1
  -- The residue field of `R` is `B ⧸ P`.
  let g : B →+* R ⧸ maximalIdeal R :=
    (Ideal.Quotient.mk _).comp ((Ideal.Quotient.mk _).comp (algebraMap B Sq))
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, rfl⟩ := ψ.surjective w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨b, rfl⟩
  have hker : RingHom.ker g = P := by
    have hprime : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
    refine ((Ideal.IsMaximal.eq_of_le ‹P.IsMaximal› hprime.ne_top ?_)).symm
    refine hprime.le_of_pow_le (n := n) fun b hb ↦ ?_
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal Sq ^ n) (algebraMap B Sq b)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem b).mpr hb), map_zero]
  let χ : (B ⧸ P) ≃+* R ⧸ maximalIdeal R :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  refine Algebra.trace_eq_of_algEquiv (A := A ⧸ p) (B := B ⧸ P) (C := R ⧸ maximalIdeal R)
    (AlgEquiv.ofRingEquiv (f := χ) ?_) (Ideal.Quotient.mk P x)
  rintro ⟨a⟩
  change g (algebraMap A B a) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (algebraMap A Sq a))
  simp only [g, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end Dedekind

section Different

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

open UniqueFactorizationMonoid

variable (A : Type*) {B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  {p : Ideal A} [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p]

/-- `P ^ (e - 1)` divides the different, `e` the ramification index of `P` (Mathlib's
`pow_sub_one_dvd_differentIdeal` for the exact power of `P` in `p B`). -/
theorem pow_ramificationIdx_sub_one_dvd_differentIdeal (hp : p ≠ ⊥) :
    P ^ (P.ramificationIdx A - 1) ∣ differentIdeal A B := by
  have hp' : p.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot (S := B) hp
  obtain ⟨Q, -, hpPQ⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hp'] at hpPQ
  exact pow_sub_one_dvd_differentIdeal A P _ hp ⟨Q, hpPQ⟩

/-- **The tame bound** (Serre, *Local Fields*, III §6, Prop. 13). If the ramification index
`e` of `P` over `p` is nonzero in `A ⧸ p` and `B ⧸ P` is separable over `A ⧸ p`, then `P ^ e`
does not divide the different of `B` over `A`. -/
theorem not_pow_ramificationIdx_dvd_differentIdeal (hp : p ≠ ⊥)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ P.ramificationIdx A ∣ differentIdeal A B := by
  set e := P.ramificationIdx A with he_def
  have hp' : p.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot (S := B) hp
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  obtain ⟨Q, hPQ, hpPQ⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hp', ← he_def]
    at hpPQ
  have hcop : IsCoprime (P ^ e) Q := (Ideal.isCoprime_iff_sup_eq.mpr hPQ).pow_left
  have hn : p ≤ (P ^ e).comap (algebraMap A B) := by
    rw [← Ideal.map_le_iff_le_comap, hpPQ]; exact Ideal.mul_le_inf.trans inf_le_left
  let _ : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hn
  let _ : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [← Ideal.map_le_iff_le_comap, hpPQ]; exact Ideal.mul_le_inf.trans inf_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ e) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ e)
  have : Module.Finite (A ⧸ p) (B ⧸ Q) := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let E : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hpPQ).trans (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨z, hz⟩ : ∃ z, Algebra.trace (A ⧸ p) (B ⧸ P) z ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (E.symm (Ideal.Quotient.mk _ x, 0))
  refine not_dvd_differentIdeal_of_intTrace_notMem A (P ^ e) Q hpPQ.symm y ?_ ?_
  · have h2 : (E (Ideal.Quotient.mk _ y)).2 = 0 := by rw [hy, AlgEquiv.apply_symm_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain, hy,
      ← Algebra.trace_eq_of_algEquiv E, AlgEquiv.apply_symm_apply, Algebra.trace_prod_apply,
      map_zero, add_zero, trace_quotient_pow p P hPbot e hn x, nsmul_eq_mul]
    exact mul_ne_zero he hz

/-- **The tame different** (Serre, *Local Fields*, III §6, Prop. 13): under the hypotheses of
`not_pow_ramificationIdx_dvd_differentIdeal`, the exponent of `P` in the different is `e - 1`. -/
theorem count_normalizedFactors_differentIdeal (hp : p ≠ ⊥)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = P.ramificationIdx A - 1 := by
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hPbot inferInstance).irreducible
  have hD : differentIdeal A B ≠ 0 := differentIdeal_ne_bot
  have hmul := emultiplicity_eq_count_normalizedFactors hirr hD
  rw [normalize_eq] at hmul
  have h1 := (pow_dvd_iff_le_emultiplicity).mp
    (pow_ramificationIdx_sub_one_dvd_differentIdeal A P hp)
  have h2 := mt (pow_dvd_iff_le_emultiplicity).mpr
    (not_pow_ramificationIdx_dvd_differentIdeal A P hp he)
  rw [hmul, Nat.cast_le] at h1
  rw [hmul, Nat.cast_le] at h2
  have he0 : P.ramificationIdx A ≠ 0 := by
    rintro h; rw [h, Nat.cast_zero] at he; exact he rfl
  omega

end Different

section FractionField

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

open UniqueFactorizationMonoid

variable (A : Type*) {B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]

/-- If `K` and `L` are fraction fields of `A` and `B` with compatible maps and `L / K` is
separable, then `FractionRing B` is separable over `FractionRing A`. -/
theorem isSeparable_fractionRing [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- **The tame different**, with the separability hypothesis on given fraction fields `K` of `A`
and `L` of `B`: the exponent of `P` in the different of `B / A` is `e - 1` when `e` is nonzero in
`A ⧸ p` and `B ⧸ P` is separable over `A ⧸ p`. -/
theorem count_normalizedFactors_differentIdeal_of_isSeparable [Module.Finite A B]
    [Algebra.IsSeparable K L] {p : Ideal A} [p.IsMaximal] (P : Ideal B) [P.IsMaximal]
    [P.LiesOver p] (hp : p ≠ ⊥) [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = P.ramificationIdx A - 1 := by
  have := isSeparable_fractionRing A (B := B) K L
  exact count_normalizedFactors_differentIdeal A P hp he

end FractionField

end Langlands.CommutativeAlgebra.TameDifferent
