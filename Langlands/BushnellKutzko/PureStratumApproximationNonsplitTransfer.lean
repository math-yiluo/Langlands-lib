import Langlands.BushnellKutzko.PureStratumApproximationMoyTransport
import Langlands.BushnellKutzko.PureStratumApproximationSeed

/-! # Nonsplit fundamental strata over the integers of an extension field

The Library's predicates `Stratum.IsSplit` and `Stratum.IsNonsplit` (BK93 (2.3.3), printed p. 58)
are stated for a general integer ring. This module shows that a fundamental stratum over
`𝔬_E = subfieldIntegers F E` that is not split satisfies `IsNonsplit` after transfer to the integer
ring `𝒪[E]` of the local field `E`, so that (2.3.4), printed p. 58, stated for local fields, applies
to it, and transfers the resulting simple stratum back to `𝔬_E`.
-/

noncomputable section

open ValuativeRel Polynomial

namespace Langlands.BushnellKutzko.PureApproximation

universe uO uO' uK uF uE uV

section Reduction

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K] [Algebra O K]

open scoped Classical in
theorem coeff_reduceIntegralPolynomial (hinj : Function.Injective (algebraMap O K))
    (p : Polynomial K) (i : ℕ) :
    (reduceIntegralPolynomial O K p).coeff i =
      if h : ∃ a : O, algebraMap O K a = p.coeff i then
        Ideal.Quotient.mk (Ring.jacobson O) (Classical.choose h)
      else 0 := by
  unfold reduceIntegralPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i ∈ p.support
  · rw [ite_eq_left hi]
  · have h0 : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    have hex : ∃ a : O, algebraMap O K a = p.coeff i := ⟨0, by rw [map_zero, h0]⟩
    have hc : Classical.choose hex = 0 := by
      apply hinj
      rw [Classical.choose_spec hex, h0, map_zero]
    rw [ite_eq_right hi, dite_eq_left hex, hc, map_zero]

/-- The reduction of a monic polynomial is monic of the same degree. -/
theorem reduceIntegralPolynomial_monic (hinj : Function.Injective (algebraMap O K))
    [Nontrivial (O ⧸ Ring.jacobson O)] {p : Polynomial K} (hp : p.Monic) :
    (reduceIntegralPolynomial O K p).Monic ∧
      (reduceIntegralPolynomial O K p).natDegree = p.natDegree := by
  classical
  have hlead : (reduceIntegralPolynomial O K p).coeff p.natDegree = 1 := by
    rw [coeff_reduceIntegralPolynomial hinj]
    have hex : ∃ a : O, algebraMap O K a = p.coeff p.natDegree := ⟨1, by rw [map_one, hp.coeff_natDegree]⟩
    rw [dite_eq_left hex]
    have hc : Classical.choose hex = 1 := by
      apply hinj
      rw [Classical.choose_spec hex, hp.coeff_natDegree, map_one]
    rw [hc, map_one]
  have hdeg : (reduceIntegralPolynomial O K p).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_reduceIntegralPolynomial hinj]
    have h0 : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi)
    have hex : ∃ a : O, algebraMap O K a = p.coeff i := ⟨0, by rw [map_zero, h0]⟩
    rw [dite_eq_left hex]
    have hc : Classical.choose hex = 0 := by
      apply hinj
      rw [Classical.choose_spec hex, h0, map_zero]
    rw [hc, map_zero]
  have hdeg' : p.natDegree ≤ (reduceIntegralPolynomial O K p).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hlead]; exact one_ne_zero)
  have heq := le_antisymm hdeg hdeg'
  refine ⟨?_, heq⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, heq, hlead]

variable {O' : Type uO'} [CommRing O'] [Algebra O' K]

theorem map_jacobson_ringEquiv (φ : O ≃+* O') :
    Ring.jacobson O' = (Ring.jacobson O).map (φ : O →+* O') := by
  rw [← Ideal.jacobson_bot, ← Ideal.jacobson_bot,
    Ideal.map_jacobson_of_bijective (f := (φ : O →+* O')) φ.bijective, Ideal.map_bot]

/-- Reduction commutes with a ring isomorphism of the integer rings compatible with `K`. -/
theorem reduceIntegralPolynomial_ringEquiv (hinj : Function.Injective (algebraMap O K))
    (hinj' : Function.Injective (algebraMap O' K)) (φ : O ≃+* O')
    (hφ : ∀ a, algebraMap O' K (φ a) = algebraMap O K a) (p : Polynomial K) :
    reduceIntegralPolynomial O' K p =
      (reduceIntegralPolynomial O K p).map
        (Ideal.quotientEquiv _ _ φ (map_jacobson_ringEquiv φ) : O ⧸ Ring.jacobson O →+* _) := by
  classical
  ext i
  rw [Polynomial.coeff_map, coeff_reduceIntegralPolynomial hinj',
    coeff_reduceIntegralPolynomial hinj]
  by_cases h : ∃ a : O, algebraMap O K a = p.coeff i
  · have h' : ∃ a : O', algebraMap O' K a = p.coeff i :=
      ⟨φ (Classical.choose h), by rw [hφ, Classical.choose_spec h]⟩
    rw [dite_eq_left h, dite_eq_left h']
    have hc : Classical.choose h' = φ (Classical.choose h) := by
      apply hinj'
      rw [Classical.choose_spec h', hφ, Classical.choose_spec h]
    rw [hc]
    rfl
  · have h' : ¬ ∃ a : O', algebraMap O' K a = p.coeff i := by
      rintro ⟨a, ha⟩
      exact h ⟨φ.symm a, by rw [← hφ, RingEquiv.apply_symm_apply, ha]⟩
    rw [dite_eq_right h, dite_eq_right h', map_zero]

end Reduction

section Factorization

variable {k : Type*} [Field k]

/-- A monic polynomial of positive degree over a field without two distinct monic irreducible
factors is a positive power of a monic irreducible polynomial. -/
theorem exists_eq_pow_of_not_two_factors {f : Polynomial k} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (h : ¬ ∃ p q : Polynomial k, p.Monic ∧ q.Monic ∧ Irreducible p ∧ Irreducible q ∧ p ≠ q ∧
      p ∣ f ∧ q ∣ f) :
    ∃ (p : Polynomial k) (m : ℕ), p.Monic ∧ Irreducible p ∧ 0 < m ∧ f = p ^ m := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  have hmon : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors f, q.Monic := by
    intro q hq
    have hq0 : q ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
    exact Polynomial.monic_normalize hq0
  have hne : UniqueFactorizationMonoid.normalizedFactors f ≠ 0 := by
    intro h0
    have ha := UniqueFactorizationMonoid.prod_normalizedFactors hf0
    rw [h0, Multiset.prod_zero] at ha
    have hu : IsUnit f := ha.isUnit_iff.mp isUnit_one
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hne
  have hall : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors f, q = p := by
    intro q hq
    by_contra hqp
    exact h ⟨q, p, hmon q hq, hmon p hp,
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq,
      UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp, hqp,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp⟩
  have hrep := Multiset.eq_replicate_card.mpr hall
  refine ⟨p, Multiset.card (UniqueFactorizationMonoid.normalizedFactors f), hmon p hp,
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp,
    Multiset.card_pos.mpr hne, ?_⟩
  have ha := UniqueFactorizationMonoid.prod_normalizedFactors hf0
  rw [hrep, Multiset.prod_replicate] at ha
  exact Polynomial.eq_of_monic_of_associated hf ((hmon p hp).pow _) ha.symm

end Factorization

section StratumTransfer

variable {O : Type uO} {O' : Type uO'} {K : Type uK} {V : Type uV} [CommRing O] [CommRing O']
  [Field K] [Algebra O K] [Algebra O' K] [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K V]

/-- A stratum viewed over a second integer ring with the same image in `K`: the same lattices,
integers and element. -/
def transferStratum (S : Stratum O K V) (φ : O ≃+* O')
    (hφ : ∀ a, algebraMap O' K (φ a) = algebraMap O K a) : Stratum O' K V :=
  ⟨S.chain.transfer φ hφ, S.n, S.r, S.b, S.r_lt_n, by
    rw [← LatticeChain.valuation_congr (fun i => (S.chain.transfer_lattice φ hφ i).symm)]
    exact S.valuation_ge⟩

variable (S : Stratum O K V) (φ : O ≃+* O') (hφ : ∀ a, algebraMap O' K (φ a) = algebraMap O K a)

theorem coe_transferStratum_lattice (i : ℤ) :
    ((transferStratum S φ hφ).chain.lattice i : Set V) = S.chain.lattice i := rfl

theorem coset_transferStratum : (transferStratum S φ hφ).coset = S.coset := by
  ext x
  exact (LatticeChain.mem_endFiltration_congr
    (fun i => (S.chain.transfer_lattice φ hφ i).symm)).symm

theorem isFundamental_transferStratum_iff :
    (transferStratum S φ hφ).IsFundamental ↔ S.IsFundamental := by
  unfold Stratum.IsFundamental
  rw [coset_transferStratum]
  rfl

theorem isSimple_transferStratum (hS : S.IsSimple) : (transferStratum S φ hφ).IsSimple := by
  have h : ∀ i, (S.chain.lattice i : Set V) = (transferStratum S φ hφ).chain.lattice i :=
    fun i => (S.chain.transfer_lattice φ hφ i).symm
  obtain ⟨⟨hf, hn⟩, hv⟩ := hS.1
  refine ⟨⟨⟨hf, ?_⟩, ?_⟩, ?_⟩
  · let := hf.toField
    exact fun a => (LatticeChain.mem_stabilizer_congr h).mp (hn a)
  · change (transferStratum S φ hφ).chain.valuation S.b = _
    rw [← LatticeChain.valuation_congr h]
    exact hv
  · change criticalExponent (transferStratum S φ hφ).chain S.b < _
    rw [← LatticeChain.criticalExponent_congr h]
    exact hS.2

/-- The transferred prime element. -/
def transferPrime (π : RingPrimeElement O) : RingPrimeElement O' :=
  ⟨φ π.1, fun h => π.2.1 (φ.injective (h.trans (map_zero φ).symm)), by
    have h : Ideal.span ({π.1} : Set O) = Ring.jacobson O := π.2.2
    calc Ideal.span ({φ π.1} : Set O') = (Ideal.span ({π.1} : Set O)).map (φ : O →+* O') := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
      _ = (Ring.jacobson O).map (φ : O →+* O') := congrArg (Ideal.map (φ : O →+* O')) h
      _ = Ring.jacobson O' := (map_jacobson_ringEquiv φ).symm⟩

variable [IsDomain O] [IsDomain O'] [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']

theorem period_transferStratum :
    (transferStratum S φ hφ).chain.period = S.chain.period := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff φ.toMulEquiv).mpr hϖ
  exact (period_eq_of_coe_lattice_eq S.chain (transferStratum S φ hφ).chain (fun i => rfl) hϖ hϖ'
    (hφ ϖ).symm).symm

theorem fundamentalPolynomial_transferStratum (hinj : Function.Injective (algebraMap O K))
    (hinj' : Function.Injective (algebraMap O' K)) (π : RingPrimeElement O) :
    (transferStratum S φ hφ).fundamentalPolynomial (transferPrime φ π) =
      (S.fundamentalPolynomial π).map
        (Ideal.quotientEquiv _ _ φ (map_jacobson_ringEquiv φ) : O ⧸ Ring.jacobson O →+* _) := by
  have he : (transferStratum S φ hφ).fundamentalElement (transferPrime φ π) =
      S.fundamentalElement π := by
    unfold Stratum.fundamentalElement
    rw [period_transferStratum S φ hφ]
    change (algebraMap O' K (φ π.1) ^ _) • _ = _
    rw [hφ]
    rfl
  unfold Stratum.fundamentalPolynomial
  rw [he]
  exact reduceIntegralPolynomial_ringEquiv hinj hinj' φ hφ _

end StratumTransfer

section Nonsplit

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module E V]

/-- **BK93 (2.3.4) over `𝔬_E`.** A fundamental stratum over `subfieldIntegers F E` that is not
split is contained in a simple stratum over `subfieldIntegers F E`, at the same normalized level,
on a chain containing its lattices. -/
theorem exists_simple_of_not_isSplit (hRef : NonsplitRefinementPremise.{uE, uV})
    (D : Stratum (subfieldIntegers F E) E V) (hfund : D.IsFundamental) (hns : ¬ D.IsSplit) :
    ∃ C : Stratum (subfieldIntegers F E) E V, C.IsSimple ∧ C.r = C.n - 1 ∧
      D.coset ⊆ C.coset ∧ D.n * C.chain.period = C.n * D.chain.period ∧
      ∀ i, ∃ j, (D.chain.lattice i : Set V) = C.chain.lattice j := by
  classical
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  have := D.chain.finiteDimensional
  have := D.chain.nontrivialSpace
  let φ := subfieldIntegerEquiv F E
  have hφ : ∀ a, algebraMap 𝒪[E] E (φ a) = algebraMap (subfieldIntegers F E) E a := fun _ => rfl
  have hφ' : ∀ a, algebraMap (subfieldIntegers F E) E (φ.symm a) = algebraMap 𝒪[E] E a := by
    intro a
    rw [← hφ, RingEquiv.apply_symm_apply]
  have hinj : Function.Injective (algebraMap (subfieldIntegers F E) E) := Subtype.val_injective
  have hinj' : Function.Injective (algebraMap 𝒪[E] E) := Subtype.val_injective
  -- a prime element of `𝔬_E`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  let π : RingPrimeElement (subfieldIntegers F E) :=
    ⟨ϖ, hϖ.ne_zero, by rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  have hmax : (Ring.jacobson (subfieldIntegers F E)).IsMaximal := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal _
  let : Field (subfieldIntegers F E ⧸ Ring.jacobson (subfieldIntegers F E)) :=
    Ideal.Quotient.field _
  -- the polynomial `φ_b` is a power of a monic irreducible polynomial
  have hmon := reduceIntegralPolynomial_monic (O := subfieldIntegers F E) hinj
    (LinearMap.charpoly_monic (D.fundamentalElement π))
  have hφmon : (D.fundamentalPolynomial π).Monic := hmon.1
  have hφdeg : 0 < (D.fundamentalPolynomial π).natDegree := by
    unfold Stratum.fundamentalPolynomial
    rw [hmon.2, LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  obtain ⟨p, m, hpm, hpi, hm, hφp⟩ := exists_eq_pow_of_not_two_factors hφmon hφdeg
    (fun ⟨p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩ =>
      hns ⟨hfund, π, p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩)
  -- transfer to the integer ring of the local field `E`
  let D' := transferStratum D φ hφ
  let ψ := Ideal.quotientEquiv _ _ φ (map_jacobson_ringEquiv φ)
  have hD' : D'.IsNonsplit := by
    refine ⟨(isFundamental_transferStratum_iff D φ hφ).mpr hfund, transferPrime φ π,
      p.map (ψ : _ →+* _), m, hpm.map _, ?_, hm, ?_⟩
    · exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv ψ).toMulEquiv).mpr hpi
    · rw [fundamentalPolynomial_transferStratum D φ hφ hinj hinj', hφp, Polynomial.map_pow]
  obtain ⟨T, hT, hTr, hcos, hslope, hlat⟩ := hRef E V D' hD'
  let C := transferStratum T φ.symm hφ'
  refine ⟨C, isSimple_transferStratum T φ.symm hφ' hT, hTr, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ D'.coset := by rw [coset_transferStratum]; exact hx
    have h := hcos hx'
    rwa [← coset_transferStratum T φ.symm hφ'] at h
  · rw [period_transferStratum T φ.symm hφ']
    rw [period_transferStratum D φ hφ] at hslope
    exact hslope
  · intro i
    obtain ⟨j, hj⟩ := hlat i
    exact ⟨j, congrArg (fun L : Submodule 𝒪[E] V => (L : Set V)) hj⟩

end Nonsplit

end Langlands.BushnellKutzko.PureApproximation
