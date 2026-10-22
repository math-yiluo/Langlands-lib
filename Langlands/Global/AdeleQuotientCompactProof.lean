import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.ArchimedeanFundamentalSet
import Langlands.Global.AdeleQuotientStatement
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Compactness of the additive adele quotient `𝔸_K / K`

Every adele is the sum of a principal adele and an element of the compact set
`archimedeanFundamentalSet K ×ˢ integralFiniteAdeles K`, so `𝔸_K / K` is compact.
See `AdeleQuotientCompactProof.md`.
-/

noncomputable section

open scoped RestrictedProduct nonZeroDivisors

universe u

namespace Langlands.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

variable (K : Type u) [Field K] [NumberField K]

/-! ### The finite adeles: `𝔸_K^f = K + ∏_v 𝒪_v` -/

section Finite

variable {K}

/-- Global integers approximate a completed local integer to within the valuation of any
nonzero global integer. -/
theorem exists_integer_sub_valued_le (v : FinitePlace K) {c : FiniteCompletion K v}
    (hc : c ∈ v.adicCompletionIntegers K) {δ : NumberField.RingOfIntegers K} (hδ : δ ≠ 0) :
    ∃ r : NumberField.RingOfIntegers K,
      Valued.v (c - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) ≤
        Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) δ) := by
  set δv := algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) δ with hδv_def
  have hδK : algebraMap (NumberField.RingOfIntegers K) K δ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hδ
  have hδv : δv ≠ 0 := by
    rw [hδv_def, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K]
    exact (map_ne_zero_iff _ (algebraMap K (FiniteCompletion K v)).injective).mpr hδK
  let U : Set (FiniteCompletion K v) :=
    (fun y ↦ (y - c) * δv⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (FiniteCompletion K v)) ∩
      (v.adicCompletionIntegers K : Set (FiniteCompletion K v))
  have hU : IsOpen U :=
    ((Valued.isOpen_valuationSubring _).preimage (by fun_prop)).inter
      (Valued.isOpen_valuationSubring _)
  have hcU : c ∈ U := ⟨by simp, hc⟩
  obtain ⟨k, hkU, hkO⟩ := (denseRange_algebraMap K v).exists_mem_open hU ⟨c, hcU⟩
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    exact (mem_adicCompletionIntegers _ _ _).mp hkO
  have hδval : v.valuation K (algebraMap (NumberField.RingOfIntegers K) K δ) ≠ 0 := by
    simpa using hδK
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hk1 (Units.mk0 _ hδval)
  refine ⟨r, ?_⟩
  have h1 : Valued.v (c - algebraMap K (FiniteCompletion K v) k) ≤ Valued.v δv := by
    have h := (mem_adicCompletionIntegers _ _ _).mp hkU
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hδv)),
      one_mul] at h
    rwa [Valuation.map_sub_swap]
  have h2 : Valued.v (algebraMap K (FiniteCompletion K v) k -
      algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) ≤ Valued.v δv := by
    have key : ∀ x : K, Valued.v (algebraMap K (FiniteCompletion K v) x) = v.valuation K x :=
      fun x ↦ valuedAdicCompletion_eq_valuation' v x
    rw [hδv_def, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K,
      IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K (FiniteCompletion K v),
      ← map_sub, key, key, Valuation.map_sub_swap]
    exact hr.le
  calc Valued.v (c - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r)
      = Valued.v ((c - algebraMap K (FiniteCompletion K v) k) +
          (algebraMap K (FiniteCompletion K v) k -
            algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ Valued.v δv := max_le h1 h2

/-- On global integers, the valuation of `K_v` is the `v`-adic valuation of `𝒪_K`. -/
theorem valued_algebraMap_integer (v : FinitePlace K) (r : NumberField.RingOfIntegers K) :
    Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) =
      v.intValuation r :=
  (valuedAdicCompletion_eq_valuation (K := K) v r).trans (valuation_of_algebraMap v r)

/-- Chinese remainder theorem: one global integer approximates given local integers at finitely
many places simultaneously, to within the valuation of a nonzero global integer. -/
theorem exists_integer_forall_sub_valued_le (s : Finset (FinitePlace K))
    (c : ∀ v : FinitePlace K, FiniteCompletion K v)
    (hc : ∀ v ∈ s, c v ∈ v.adicCompletionIntegers K)
    {δ : NumberField.RingOfIntegers K} (hδ : δ ≠ 0) :
    ∃ r : NumberField.RingOfIntegers K, ∀ v ∈ s,
      Valued.v (c v - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) ≤
        Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) δ) := by
  have h₁ : ∀ v ∈ s, ∃ r : NumberField.RingOfIntegers K,
      Valued.v (c v - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) ≤
        Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) δ) :=
    fun v hv ↦ exists_integer_sub_valued_le v (hc v hv) hδ
  choose! ρ hρ using h₁
  choose n hn using fun v : FinitePlace K ↦
    WithZero.exists_exp_neg_natCast_lt (v.intValuation_ne_zero δ hδ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun v : FinitePlace K ↦ v.asIdeal) n (fun v _ ↦ v.prime)
    (fun v _ w _ hvw e ↦ hvw (HeightOneSpectrum.ext e)) (fun v ↦ ρ v)
  refine ⟨r, fun v hv ↦ ?_⟩
  have hsub : Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v)
      (ρ v - r)) ≤ Valued.v (algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) δ) := by
    rw [valued_algebraMap_integer, valued_algebraMap_integer, Valuation.map_sub_swap]
    exact (((intValuation_le_pow_iff_mem v _ _).mpr (hr v hv)).trans_lt (hn v)).le
  calc Valued.v (c v - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r)
      = Valued.v ((c v - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) (ρ v)) +
          algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) (ρ v - r)) := by
        congr 1
        rw [map_sub (algebraMap _ _), sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le (hρ v hv) hsub

/-- Clearing denominators: some nonzero global integer multiplies a finite adele into
`∏_v 𝒪_v`. -/
theorem exists_integer_mul_mem_adicCompletionIntegers (a : FiniteAdeles K) :
    ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧ ∀ v : FinitePlace K,
      algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) d * a v ∈
        v.adicCompletionIntegers K := by
  classical
  set S := (Filter.eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).toFinset
  choose b hb0 hb using fun v : FinitePlace K ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ S, b v, Finset.prod_ne_zero_iff.mpr fun v _ ↦ nonZeroDivisors.ne_zero (hb0 v),
    fun v ↦ ?_⟩
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S b hv, map_mul, mul_comm (algebraMap _ _ (b v)), mul_assoc,
      mul_comm _ (a v)]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (hb v)
  · have ha : a v ∈ v.adicCompletionIntegers K := by
      simpa [S] using hv
    exact mul_mem (coe_mem_adicCompletionIntegers v _) ha

/-- Every finite adele is a principal adele plus an integral one: `𝔸_K^f = K + ∏_v 𝒪_v`. -/
theorem exists_sub_mem_integralFiniteAdeles (a : FiniteAdeles K) :
    ∃ x : K, a - algebraMap K (FiniteAdeles K) x ∈ integralFiniteAdeles K := by
  obtain ⟨d, hd0, hd⟩ := exists_integer_mul_mem_adicCompletionIntegers a
  have hT : {v : FinitePlace K | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)
  obtain ⟨r, hr⟩ := exists_integer_forall_sub_valued_le hT.toFinset
    (fun v ↦ algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) d * a v)
    (fun v _ ↦ hd v) hd0
  refine ⟨algebraMap (NumberField.RingOfIntegers K) K r /
    algebraMap (NumberField.RingOfIntegers K) K d, (mem_integralFiniteAdeles K _).mpr fun v ↦ ?_⟩
  set dv := algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) d with hdv_def
  have hdv : dv ≠ 0 := by
    rw [hdv_def, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K]
    exact (map_ne_zero_iff _ (algebraMap K (FiniteCompletion K v)).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hd0)
  have key : (a - algebraMap K (FiniteAdeles K) (algebraMap (NumberField.RingOfIntegers K) K r /
      algebraMap (NumberField.RingOfIntegers K) K d)) v =
      (dv * a v - algebraMap (NumberField.RingOfIntegers K) (FiniteCompletion K v) r) * dv⁻¹ := by
    change a v - algebraMap K (FiniteCompletion K v) (algebraMap (NumberField.RingOfIntegers K) K r /
      algebraMap (NumberField.RingOfIntegers K) K d) = _
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hdv_def]
    field_simp
  rw [key, mem_adicCompletionIntegers, map_mul, map_inv₀,
    mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hdv)), one_mul]
  by_cases hv : v ∈ hT.toFinset
  · exact hr v hv
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Ideal.dvd_span_singleton] at hv
    have h1 : Valued.v dv = 1 := by
      rw [hdv_def, valued_algebraMap_integer]
      exact le_antisymm (v.intValuation_le_one d)
        (not_lt.mp ((intValuation_lt_one_iff_mem v d).not.mpr hv))
    rw [h1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le ((mem_adicCompletionIntegers _ _ _).mp (hd v))
        ((mem_adicCompletionIntegers _ _ _).mp (coe_mem_adicCompletionIntegers v r)))

end Finite

/-! ### Compactness of `𝔸_K / K` -/

/-- **Compactness of the additive adele quotient** (Cassels, *Global fields*, §14, Theorem;
Weil, *Basic number theory*, IV §2 Theorem 2): `𝔸_K / K` is compact. -/
theorem adeleQuotientCompact : AdeleQuotientCompactStatement K := by
  set C : Set (Adeles K) := archimedeanFundamentalSet K ×ˢ
    (integralFiniteAdeles K : Set (FiniteAdeles K))
  have hC : IsCompact C :=
    (isCompact_archimedeanFundamentalSet K).prod (isCompact_integralFiniteAdeles K)
  have hsurj : QuotientAddGroup.mk '' C = (Set.univ : Set (AdeleQuotient K)) := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles a.2
      obtain ⟨y, hy⟩ := exists_sub_integer_mem_archimedeanFundamentalSet K
        (a.1 - algebraMap K (InfiniteAdeles K) x)
      have hyf : algebraMap K (FiniteAdeles K) (y : K) ∈ integralFiniteAdeles K :=
        (mem_integralFiniteAdeles K _).mpr fun v ↦ coe_mem_adicCompletionIntegers v y
      refine ⟨a - algebraMap K (Adeles K) (x + (y : K)), ⟨?_, ?_⟩, ?_⟩
      · change a.1 - algebraMap K (InfiniteAdeles K) (x + (y : K)) ∈ _
        rwa [map_add, ← sub_sub]
      · change a.2 - algebraMap K (FiniteAdeles K) (x + (y : K)) ∈ integralFiniteAdeles K
        rw [map_add, ← sub_sub]
        exact (integralFiniteAdeles K).sub_mem hx hyf
      · refine QuotientAddGroup.eq.mpr ?_
        rw [neg_sub, sub_add_cancel]
        exact ⟨_, rfl⟩
  exact ⟨hsurj ▸ hC.image QuotientAddGroup.continuous_mk⟩

/-- `adeleQuotientCompact` with its conclusion stated as a `CompactSpace` instance type. -/
theorem compactSpace_adeleQuotient : CompactSpace (AdeleQuotient K) :=
  adeleQuotientCompact K

end Langlands.Global
