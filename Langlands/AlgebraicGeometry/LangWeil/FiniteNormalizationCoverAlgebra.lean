import Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType

/-! # Algebraic input for finite normalization covers

Generic Noether normalization over a domain, after inverting one element of the base,
gives a finite injective map from a polynomial algebra. Over every prime of the
localized base, going up along it produces a chain of primes of the expected length. -/

universe u

open MvPolynomial

namespace Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction

section Chain

variable {K : Type*} [CommRing K] (d : ℕ) (𝔭 : Ideal K) [𝔭.IsPrime]

/-- Reduce coefficients modulo `𝔭` and kill the coordinates of index below `k`. -/
noncomputable def killMap (k : ℕ) :
    MvPolynomial (ULift.{u} (Fin d)) K →+* MvPolynomial (ULift.{u} (Fin d)) (K ⧸ 𝔭) :=
  eval₂Hom (C.comp (Ideal.Quotient.mk 𝔭)) (fun i => if i.down.val < k then 0 else X i)

lemma killMap_succ (k : ℕ) :
    killMap.{u} d 𝔭 (k + 1) = (eval₂Hom C (fun i : ULift.{u} (Fin d) =>
      if i.down.val < k + 1 then 0 else X i)).comp (killMap.{u} d 𝔭 k) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [killMap]
  · intro i
    by_cases h : i.down.val < k
    · simp [killMap, h]
      omega
    · simp [killMap, h]

omit [𝔭.IsPrime] in
lemma killMap_comp_C (k : ℕ) :
    (killMap.{u} d 𝔭 k).comp C = C.comp (Ideal.Quotient.mk 𝔭) := by
  ext a
  simp [killMap]

omit [𝔭.IsPrime] in
lemma comap_ker_killMap (k : ℕ) :
    (RingHom.ker (killMap.{u} d 𝔭 k)).comap C = 𝔭 := by
  rw [RingHom.comap_ker, killMap_comp_C, RingHom.ker_comp_of_injective _ (C_injective _ _),
    Ideal.mk_ker]

lemma ker_killMap_lt (i : Fin d) :
    RingHom.ker (killMap.{u} d 𝔭 i.val) < RingHom.ker (killMap.{u} d 𝔭 (i.val + 1)) := by
  refine SetLike.lt_iff_le_and_exists.mpr ⟨fun p hp => ?_, X ⟨i⟩, ?_, ?_⟩
  · rw [RingHom.mem_ker] at hp ⊢
    rw [killMap_succ, RingHom.comp_apply, hp, map_zero]
  · simp [killMap, RingHom.mem_ker]
  · have : Nontrivial (K ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
    simp [killMap, RingHom.mem_ker, X_ne_zero]

/-- The chain `𝔭[X] ⊂ 𝔭[X] + (X₀) ⊂ ⋯ ⊂ 𝔭[X] + (X₀, …, X_{d-1})` of primes over `𝔭`. -/
noncomputable def polyChain : LTSeries (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin d)) K)) :=
  LTSeries.mk d (fun k => ⟨RingHom.ker (killMap.{u} d 𝔭 k.val), RingHom.ker_isPrime _⟩)
    (Fin.strictMono_iff_lt_succ.mpr fun i => by
      change RingHom.ker (killMap.{u} d 𝔭 i.val) < RingHom.ker (killMap.{u} d 𝔭 (i.val + 1))
      exact ker_killMap_lt d 𝔭 i)

lemma polyChain_length : (polyChain.{u} d 𝔭).length = d := rfl

lemma comap_polyChain (k : Fin ((polyChain.{u} d 𝔭).length + 1)) :
    PrimeSpectrum.comap C (polyChain.{u} d 𝔭 k) = ⟨𝔭, ‹_›⟩ := by
  ext1
  exact comap_ker_killMap d 𝔭 k.val

end Chain

/-- A finite injective map from a polynomial algebra has, over every prime of the base,
a chain of primes of length equal to the number of variables. -/
theorem exists_ltSeries_fibre {K E : Type*} [CommRing K] [CommRing E] [Algebra K E] {d : ℕ}
    (ψ : MvPolynomial (ULift.{u} (Fin d)) K →ₐ[K] E) (hint : ψ.toRingHom.IsIntegral)
    (hinj : Function.Injective ψ) (𝔭 : PrimeSpectrum K) :
    ∃ L : LTSeries (PrimeSpectrum E), L.length = d ∧
      ∀ i, PrimeSpectrum.comap (algebraMap K E) (L i) = 𝔭 := by
  let := ψ.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (ULift.{u} (Fin d)) K) E := ⟨hint⟩
  let l := polyChain.{u} d 𝔭.asIdeal
  obtain ⟨P, -, hP, hPover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E)
    (RelSeries.head l).asIdeal ⊥ (by
      intro p hp
      have : ψ p = 0 := hp
      rw [hinj (this.trans (map_zero ψ).symm)]
      exact zero_mem _)
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPover.symm⟩
  obtain ⟨L, hlen, -, hmap⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  refine ⟨L, hlen, fun i => ?_⟩
  have hmem : PrimeSpectrum.comap (algebraMap _ E) (L i) ∈ l.toList := by
    rw [← hmap]
    exact List.mem_map_of_mem (RelSeries.mem_toList.mpr ⟨i, rfl⟩)
  obtain ⟨k, hk⟩ := RelSeries.mem_toList.mp hmem
  have hcomp : algebraMap K E = (algebraMap (MvPolynomial (ULift.{u} (Fin d)) K) E).comp C :=
    (ψ.comp_algebraMap).symm
  rw [hcomp, PrimeSpectrum.comap_comp_apply, ← hk]
  exact comap_polyChain d 𝔭.asIdeal k

section Normalization

variable {D C : Type u} [CommRing D] [IsDomain D] [CommRing C] [IsDomain C] [Algebra D C]
  [FaithfulSMul D C]

/-- From generic Noether normalization data `r, z` for `C` over `D`, the coordinates `z`
define a finite injective map from a polynomial algebra over `D[1/r]` to `C[1/r]`. -/
theorem finite_injective_of_generic [Algebra.FiniteType D C] {r : D} (hr : r ≠ 0) {d : ℕ}
    {z : Fin d → C} (hz : AlgebraicIndependent D z)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin D (Set.range z)) (r ^ n • c))
    (D' C' : Type u) [CommRing D'] [CommRing C'] [Algebra D D'] [IsLocalization.Away r D']
    [Algebra C C'] [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C']
    [Algebra D' C'] [Algebra D C'] [IsScalarTower D D' C'] [IsScalarTower D C C'] :
    ∃ ψ : MvPolynomial (ULift.{u} (Fin d)) D' →ₐ[D'] C',
      ψ.toRingHom.Finite ∧ Function.Injective ψ := by
  let B := MvPolynomial (ULift.{u} (Fin d)) D'
  let ψ : B →ₐ[D'] C' := aeval fun i => algebraMap C C' (z i.down)
  have key : ∀ p : MvPolynomial (ULift.{u} (Fin d)) D,
      ψ (MvPolynomial.map (algebraMap D D') p) =
        algebraMap C C' (aeval (z ∘ ULift.down) p) := by
    intro p
    have : ψ.toRingHom.comp (MvPolynomial.map (algebraMap D D')) =
        (algebraMap C C').comp (aeval (z ∘ ULift.down)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change ψ (MvPolynomial.map _ (MvPolynomial.C a)) = algebraMap C C' (aeval _ (MvPolynomial.C a))
        rw [map_C, aeval_C, aeval_C, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      · intro i
        change ψ (MvPolynomial.map _ (X i)) = algebraMap C C' (aeval _ (X i))
        rw [map_X, aeval_X, aeval_X]
        rfl
    exact congr($this p)
  refine ⟨ψ, ?_, ?_⟩
  · let _ : Algebra B C' := ψ.toRingHom.toAlgebra
    have unit : ∀ x : C', ∀ t ∈ Submonoid.powers r,
        IsIntegral B (x * algebraMap C C' (algebraMap D C t)) → IsIntegral B x := by
      intro x t ht hx
      obtain ⟨v, hv⟩ := (IsLocalization.map_units D' ⟨t, ht⟩).exists_left_inv
      refine IsIntegral.of_mul_unit (r := MvPolynomial.C v) ?_ hx
      change ψ (MvPolynomial.C v) * _ = 1
      rw [aeval_C, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply D D' C',
        ← map_mul, hv, map_one]
    have hφ : (algebraMap B C').comp
        (((MvPolynomial.map (algebraMap D D')).comp
          (rename (ULift.up : Fin d → ULift.{u} (Fin d))).toRingHom).comp
            hz.aevalEquiv.symm.toRingEquiv.toRingHom) =
          (algebraMap C C').comp (algebraMap (Algebra.adjoin D (Set.range z)) C) := by
      ext a
      obtain ⟨p, rfl⟩ := hz.aevalEquiv.surjective a
      change ψ _ = _
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply,
        AlgHom.toRingHom_eq_coe]
      rw [key, AlgebraicIndependent.algebraMap_aevalEquiv, aeval_rename]
      rfl
    have hc : ∀ c : C, IsIntegral B (algebraMap C C' c) := by
      intro c
      obtain ⟨n, hn⟩ := hint c
      refine unit _ (r ^ n) ⟨n, rfl⟩ ?_
      rw [← map_mul, mul_comm, ← Algebra.smul_def]
      exact IsIntegral.map_of_comp_eq _ _ hφ hn
    have hInt : ψ.toRingHom.IsIntegral := by
      intro y
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) (S := C') y
      obtain ⟨t, ht, hts⟩ := s.2
      refine unit _ t ht ?_
      rw [hts, IsLocalization.mk'_spec]
      exact hc c
    have hFG : Monoid.FG (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      infer_instance
    have : Algebra.FiniteType C C' := IsLocalization.finiteType_of_monoid_fg
      (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C'
    have : Algebra.FiniteType D C' := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
    have : Algebra.FiniteType D' C' := Algebra.FiniteType.of_restrictScalars_finiteType D D' C'
    have hFT : ψ.toRingHom.FiniteType := by
      refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap D' B) ?_
      rw [show ψ.toRingHom.comp (algebraMap D' B) = algebraMap D' C' from ψ.comp_algebraMap]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    exact RingHom.IsIntegral.to_finite hInt hFT
  · rw [injective_iff_map_eq_zero]
    intro p hp
    let _ := MvPolynomial.algebraMvPolynomial (σ := ULift.{u} (Fin d)) (R := D) (S := D')
    obtain ⟨⟨p₀, s⟩, hps⟩ := IsLocalization.surj
      ((Submonoid.powers r).map (MvPolynomial.C (σ := ULift.{u} (Fin d)))) p
    obtain ⟨t, ht, hts⟩ := s.2
    have hs : IsUnit (MvPolynomial.map (algebraMap D D') s.1 : B) := by
      rw [← hts, map_C]
      exact (IsLocalization.map_units D' ⟨t, ht⟩).map _
    have h0 : algebraMap C C' (aeval (z ∘ ULift.down) p₀) = 0 := by
      rw [← key]
      change ψ (algebraMap _ B p₀) = 0
      rw [← hps, map_mul, hp, zero_mul]
    obtain ⟨⟨m, hm⟩, hm0⟩ :=
      (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid C (Submonoid.powers r))
        C' _).mp h0
    obtain ⟨t', ⟨k, rfl⟩, rfl⟩ := hm
    have hm_ne : algebraMap D C (r ^ k) ≠ 0 := by
      rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective D C)]
      exact pow_ne_zero _ hr
    have hz' : AlgebraicIndependent D (z ∘ ULift.down) := hz.comp _ ULift.down_injective
    have hp₀ : p₀ = 0 := by
      apply algebraicIndependent_iff_injective_aeval.mp hz'
      rw [map_zero]
      exact (mul_eq_zero.mp hm0).resolve_left hm_ne
    change p * MvPolynomial.map (algebraMap D D') s.1 = MvPolynomial.map (algebraMap D D') p₀
      at hps
    rw [hp₀, map_zero, hs.mul_left_eq_zero] at hps
    exact hps

/-- Generic Noether normalization in finite injective form: after inverting one nonzero
element `r` of the base, a polynomial algebra over `D[1/r]` maps finitely and injectively
to `C[1/r]`. -/
theorem exists_away_finite_injective [Algebra.FiniteType D C] :
    ∃ r : D, r ≠ 0 ∧ ∃ (d : ℕ) (ψ : MvPolynomial (ULift.{u} (Fin d)) (Localization.Away r)
      →ₐ[Localization.Away r]
        Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers r))),
      ψ.toRingHom.Finite ∧ Function.Injective ψ := by
  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := D) (C := C)
  exact ⟨r, hr, d, finite_injective_of_generic hr hz hint _ _⟩

end Normalization

end Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction
