import Langlands.Correspondence.HenniartNumericalDescentStatement
import Langlands.ClassFieldTheory.Local.NormUnitImageIndexSupport
import Langlands.ClassFieldTheory.Local.UnitNormProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedNormReductionProof
import Langlands.ClassFieldTheory.Local.PrimeRamificationBreakProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentProof
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.Representation.Conductor.FieldEquivTransport

/-!
# Slopes under weak cyclic base change

This module proves `Langlands.Henniart.BaseChangeSlopeStatement` (Henniart 1988,
Proposition 6.7; route note `lem:slopebc`) as `Langlands.Henniart.baseChangeSlope`.

For a cyclic step `M/L` of prime degree `ℓ`, the proof combines the conductor identity
(W4) and the fibre description (W3a)/(W3b) of a weak cyclic base change with the twist
Swan bound and the following facts, proved here from published local results:

* `ℓ = e(M|L) f(M|L)`, so the step is unramified or totally ramified;
* the norm characters `Ξ` form a finite set with at most `ℓ` elements, and any
  nontrivial one generates all of them under powers;
* in the unramified case every element of `Ξ` has Swan exponent `0` and `ψ_{M/L}(x) ≥ x`;
* in the totally ramified case, with lower break `t`, every element of `Ξ` has Swan
  exponent at most `t`, the different exponent is `(t + 1)(ℓ - 1)`, and
  `ψ_{M/L}(x) ≥ x + (ℓ - 1) max(0, x - t)` for `x ≥ 0`;
* Galois conjugation preserves the conductor of a supercuspidal class of `M`.
-/

noncomputable section

/-! ### Herbrand functions -/

namespace Langlands.Ramification.Padic

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- Every lower ramification group is at most as large as `G_0`. -/
theorem lowerGroupOrder_le_zero (i : ℕ) : lowerGroupOrder T K i ≤ lowerGroupOrder T K 0 := by
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  exact Subgroup.card_le_of_le (lowerRamificationGroup_antitone T K (Nat.zero_le i))

/-- On the nonnegative half-line, `φ(u) ≤ u`. -/
theorem herbrandPhi_le_self {u : ℝ} (hu : 0 ≤ u) : herbrandPhi T K u ≤ u := by
  rw [herbrandPhi_floor T K hu]
  have h0 : (0 : ℝ) < lowerGroupOrder T K 0 := by exact_mod_cast lowerGroupOrder_pos T K 0
  rw [div_le_iff₀ h0]
  have hsum : (∑ i ∈ Finset.range ⌊u⌋₊, (lowerGroupOrder T K (i + 1) : ℝ)) ≤
      ⌊u⌋₊ * (lowerGroupOrder T K 0 : ℝ) := by
    have := Finset.sum_le_card_nsmul (Finset.range ⌊u⌋₊)
      (fun i => (lowerGroupOrder T K (i + 1) : ℝ)) (lowerGroupOrder T K 0 : ℝ)
      (fun i _ => by exact_mod_cast lowerGroupOrder_le_zero T K (i + 1))
    simpa [nsmul_eq_mul] using this
  have hfrac : 0 ≤ u - ⌊u⌋₊ := sub_nonneg.mpr (Nat.floor_le hu)
  have hlast : (lowerGroupOrder T K (⌊u⌋₊ + 1) : ℝ) ≤ lowerGroupOrder T K 0 := by
    exact_mod_cast lowerGroupOrder_le_zero T K _
  nlinarith [mul_le_mul_of_nonneg_left hlast hfrac]

/-- On the nonnegative half-line, `v ≤ ψ(v)`. -/
theorem le_herbrandPsi_self {v : ℝ} (hv : 0 ≤ v) : v ≤ herbrandPsi T K v := by
  have hψ : 0 ≤ herbrandPsi T K v := by
    have h := (herbrandPsi_strictMono T K).monotone hv
    rwa [herbrandPsi_zero] at h
  have h := herbrandPhi_le_self T K hψ
  rwa [herbrandPhi_herbrandPsi] at h

/-- With a single lower break at `t` in a group of order `ℓ`, the Herbrand function
is `t + (u - t) / ℓ` from `t` on. -/
theorem herbrandPhi_of_single_break (t ℓ : ℕ)
    (hcard : Nat.card (F.Carrier ≃ₐ[K] F.Carrier) = ℓ)
    (hpat : ∀ i : ℕ, lowerRamificationGroup T K i = if i ≤ t then ⊤ else ⊥)
    {u : ℝ} (hu : (t : ℝ) ≤ u) :
    herbrandPhi T K u = t + (u - t) / ℓ := by
  have hord : ∀ i : ℕ, lowerGroupOrder T K i = if i ≤ t then ℓ else 1 := by
    intro i
    unfold lowerGroupOrder
    rw [hpat i]
    split_ifs
    · rw [Subgroup.card_top, hcard]
    · exact Subgroup.card_bot
  have hu0 : 0 ≤ u := (Nat.cast_nonneg t).trans hu
  have hℓ : 0 < ℓ := by
    have h := lowerGroupOrder_pos T K 0
    simpa [hord 0] using h
  have htm : t ≤ ⌊u⌋₊ := Nat.le_floor hu
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le htm
  rw [herbrandPhi_floor T K hu0, hr, Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range t, (lowerGroupOrder T K (i + 1) : ℝ) = t * ℓ := by
    rw [Finset.sum_congr rfl (g := fun _ => (ℓ : ℝ))]
    · simp
    · intro i hi
      have hi' : i + 1 ≤ t := by simp at hi; omega
      simp [hord, hi']
  have h2 : ∑ i ∈ Finset.range r, (lowerGroupOrder T K (t + i + 1) : ℝ) = r := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro i _
      have hi' : ¬ t + i + 1 ≤ t := by omega
      simp [hord, hi']
  have h3 : (lowerGroupOrder T K (t + r + 1) : ℝ) = 1 := by
    have hi' : ¬ t + r + 1 ≤ t := by omega
    simp [hord, hi']
  have h4 : (lowerGroupOrder T K 0 : ℝ) = ℓ := by
    simp [hord]
  rw [h1, h2, h3, h4]
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp
  ring

end Langlands.Ramification.Padic

/-! ### Characters trivial on a subgroup of prime index -/

namespace Langlands.Henniart.Numerical

/-- Characters of a commutative group trivial on a subgroup of prime index `ℓ` are determined
by their value at one element, and that value is an `ℓ`-th root of unity. -/
theorem exists_eval_determines {G : Type*} [CommGroup G] (N : Subgroup G) (hN : N.index.Prime) :
    ∃ a : G, (∀ χ χ' : G →* ℂˣ, N ≤ χ.ker → N ≤ χ'.ker → χ a = χ' a → χ = χ') ∧
      ∀ χ : G →* ℂˣ, N ≤ χ.ker → χ a ^ N.index = 1 := by
  have : Fact (Nat.card (G ⧸ N)).Prime := ⟨hN⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card rfl
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨a, ?_, ?_⟩
  · intro χ χ' hχ hχ' heq
    refine MonoidHom.ext fun b => ?_
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hq (b : G ⧸ N))
    have hmem : (a ^ j)⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq]
      simpa using hj
    have h1 : χ ((a ^ j)⁻¹ * b) = 1 := hχ hmem
    have h2 : χ' ((a ^ j)⁻¹ * b) = 1 := hχ' hmem
    calc χ b = χ (a ^ j) * χ ((a ^ j)⁻¹ * b) := by rw [← map_mul, mul_inv_cancel_left]
      _ = χ' (a ^ j) * χ' ((a ^ j)⁻¹ * b) := by rw [map_zpow, map_zpow, heq, h1, h2]
      _ = χ' b := by rw [← map_mul, mul_inv_cancel_left]
  · intro χ hχ
    have hpow : a ^ N.index ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_card_eq_one'
    rw [← map_pow]
    exact hχ hpow

universe uK uV

/-- A finite conductor determines the Swan exponent read from it. -/
theorem supercuspidalSwanExponent_eq_of_hasSupercuspidalSwan {p : ℕ} [Fact p.Prime]
    {K : PadicField.{uK} p} {k : ℕ}
    {π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat}
    {s : ℕ} (h : HasSupercuspidalSwan K π s) : supercuspidalSwanExponent K π = s := by
  obtain ⟨a, ha, has⟩ := h
  unfold supercuspidalSwanExponent
  rw [ha]
  exact has

end Langlands.Henniart.Numerical

/-! ### Cyclic steps of prime degree -/

namespace Langlands.Henniart.Numerical.CyclicPrimeStep

open LocalClassField

universe uK uV u

variable {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)

/-- The Galois group of a step is finite. -/
theorem finite_gal : Finite S.Gal := Nat.finite_of_card_ne_zero S.card_prime.ne_zero

/-- `M` is finite-dimensional over `L`. -/
theorem finiteDimensional :
    letI := S.algebra
    FiniteDimensional S.base.Carrier S.top.Carrier :=
  Weil.Local.extensionAlgebra_finiteDimensional S.base S.top S.embedding

/-- The degree `[M : L]` is the order of the Galois group. -/
theorem degree_eq_card : S.degree = Nat.card S.Gal := by
  let := S.algebra
  have := S.finiteDimensional
  have := S.isGalois
  exact (IsGalois.card_aut_eq_finrank _ _).symm

/-- The degree `[M : L]` is prime. -/
theorem degree_prime : S.degree.Prime := S.degree_eq_card ▸ S.card_prime

/-- A step is an abelian Galois extension. -/
theorem isAbelianGalois :
    letI := S.algebra
    IsAbelianGalois S.base.Carrier S.top.Carrier := by
  let := S.algebra
  have := S.isGalois
  have : Fact (Nat.card S.Gal).Prime := ⟨S.card_prime⟩
  have : IsCyclic S.Gal := isCyclic_of_prime_card rfl
  exact { toIsGalois := S.isGalois, toIsMulCommutative := IsCyclic.isMulCommutative }

/-- `e_M = e(M|L) e_L` for the absolute ramification indices. -/
theorem top_ramificationIndex :
    S.top.canonicalTopologicalData.ramificationIndex =
      S.ramificationIndex * S.base.canonicalTopologicalData.ramificationIndex := by
  let := S.algebra
  have := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  have := S.finiteDimensional
  set TL := S.base.canonicalTopologicalData
  set TM := S.top.canonicalTopologicalData
  have h := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap S.base S.top TL TM
    TL.uniformizer
  rw [TL.ord_uniformizer, mul_one] at h
  have hpos : (0 : ℤ) < TL.ramificationIndex := by exact_mod_cast TL.ramificationIndex_pos
  have hM : (0 : ℤ) < TM.ramificationIndex := by exact_mod_cast TM.ramificationIndex_pos
  have h' : (TL.ramificationIndex : ℤ) * TM.ord (S.embedding TL.uniformizer) =
      TM.ramificationIndex := h
  have hord : 0 ≤ TM.ord (S.embedding TL.uniformizer) := by
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    nlinarith
  have he : (S.ramificationIndex : ℤ) = TM.ord (S.embedding TL.uniformizer) := by
    unfold ramificationIndex
    exact Int.toNat_of_nonneg hord
  have : (TM.ramificationIndex : ℤ) = S.ramificationIndex * TL.ramificationIndex := by
    rw [he, ← h', mul_comm]
  exact_mod_cast this

/-- `e(M|L) f(M|L) = [M : L]`. -/
theorem ramificationIndex_mul_residueDegree :
    S.ramificationIndex * S.residueDegree = S.degree := by
  have h := PadicField.ramificationIndex_mul_extensionResidueDegree S.base S.top S.embedding
  rw [top_ramificationIndex] at h
  have hpos := S.base.canonicalTopologicalData.ramificationIndex_pos
  have h' : (S.ramificationIndex * S.residueDegree) *
      S.base.canonicalTopologicalData.ramificationIndex =
      S.degree * S.base.canonicalTopologicalData.ramificationIndex := by
    unfold residueDegree degree
    rw [← h]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h'

/-- A cyclic step of prime degree is unramified or totally ramified. -/
theorem unramified_or_totallyRamified :
    (S.ramificationIndex = 1 ∧ S.residueDegree = S.degree) ∨
      (S.ramificationIndex = S.degree ∧ S.residueDegree = 1) := by
  have h := S.ramificationIndex_mul_residueDegree
  have hp := S.degree_prime
  rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ h) with hf | hf
  · right
    refine ⟨?_, hf⟩
    rw [hf, mul_one] at h
    exact h
  · left
    refine ⟨?_, hf⟩
    rw [hf] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos (h.trans (one_mul _).symm)

/-- `x ≤ ψ_{M/L}(x)` for `x ≥ 0`. -/
theorem le_herbrandPsi {x : ℝ} (hx : 0 ≤ x) : x ≤ S.herbrandPsi x := by
  let := S.algebra
  have := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  exact Ramification.Padic.le_herbrandPsi_self _ _ hx

/-! ### Norm characters -/

section NormCharacters

local instance canonicalPadicTopology (F : PadicField.{u} p) : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The norm subgroup `N_{M/L}(M^×)` has index `[M : L]`. -/
theorem normSubgroup_index :
    letI := S.algebra
    haveI := S.finiteDimensional
    (normSubgroup S.base.Carrier S.top.Carrier).index = S.degree := by
  let := S.algebra
  have := S.finiteDimensional
  have := S.isAbelianGalois
  exact NormUnitImage.normSubgroup_index_eq_finrank S.base S.top

/-- There is a unit `a` of `L` such that a norm character is determined by its value at `a`,
which is a `[M : L]`-th root of unity. -/
theorem exists_eval_normCharacters :
    ∃ a : S.base.Carrierˣ,
      (∀ η ∈ S.normCharacters, ∀ η' ∈ S.normCharacters, η a = η' a → η = η') ∧
        ∀ η ∈ S.normCharacters, η a ^ S.degree = 1 := by
  let := S.algebra
  have := S.finiteDimensional
  have hidx := S.normSubgroup_index
  obtain ⟨a, hinj, hpow⟩ := exists_eval_determines (normSubgroup S.base.Carrier S.top.Carrier)
    (hidx ▸ S.degree_prime)
  refine ⟨a, ?_, ?_⟩
  · intro η hη η' hη' heq
    exact ContinuousMonoidHom.toMonoidHom_injective (hinj _ _ hη hη' heq)
  · intro η hη
    rw [← hidx]
    exact hpow _ hη

/-- The trivial character is a norm character. -/
theorem one_mem_normCharacters :
    (1 : Correspondence.QuasiCharacter S.base) ∈ S.normCharacters := by
  intro x _
  rfl

/-- Powers of norm characters are norm characters. -/
theorem pow_mem_normCharacters {η : Correspondence.QuasiCharacter S.base}
    (hη : η ∈ S.normCharacters) (j : ℕ) : η ^ j ∈ S.normCharacters := by
  intro x hx
  change (η ^ j) x = 1
  rw [ContinuousMonoidHom.pow_apply]
  have : η x = 1 := hη hx
  rw [this, one_pow]

/-- The norm characters form a finite set with at most `[M : L]` elements. -/
theorem normCharacters_finite_ncard :
    S.normCharacters.Finite ∧ S.normCharacters.ncard ≤ S.degree := by
  obtain ⟨a, hinj, hpow⟩ := S.exists_eval_normCharacters
  have : NeZero S.degree := ⟨S.degree_prime.ne_zero⟩
  let t : Set ℂˣ := (rootsOfUnity S.degree ℂ : Set ℂˣ)
  have ht : t.Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity S.degree ℂ))
  have hmaps : ∀ η ∈ S.normCharacters,
      (fun η : Correspondence.QuasiCharacter S.base => η a) η ∈ t := by
    intro η hη
    exact (mem_rootsOfUnity _ _).mpr (hpow η hη)
  have hinjOn : Set.InjOn (fun η : Correspondence.QuasiCharacter S.base => η a)
      S.normCharacters :=
    fun η hη η' hη' h => hinj η hη η' hη' h
  refine ⟨Set.Finite.of_finite_image (ht.subset (Set.image_subset_iff.mpr hmaps)) hinjOn, ?_⟩
  calc S.normCharacters.ncard ≤ t.ncard := Set.ncard_le_ncard_of_injOn _ hmaps hinjOn ht
    _ = Nat.card (rootsOfUnity S.degree ℂ) := (Nat.card_coe_set_eq t).symm
    _ ≤ S.degree := card_rootsOfUnity _ _

/-- A nontrivial norm character generates all of them under powers. -/
theorem exists_pow_eq_of_ne_one {η₀ : Correspondence.QuasiCharacter S.base}
    (hη₀ : η₀ ∈ S.normCharacters) (h₀ : η₀ ≠ 1) {η : Correspondence.QuasiCharacter S.base}
    (hη : η ∈ S.normCharacters) : ∃ j : ℕ, η = η₀ ^ j := by
  obtain ⟨a, hinj, hpow⟩ := S.exists_eval_normCharacters
  have : NeZero S.degree := ⟨S.degree_prime.ne_zero⟩
  have hζ : ((η₀ a : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    apply h₀
    apply hinj η₀ hη₀ 1 S.one_mem_normCharacters
    exact Units.ext h
  have hprim : IsPrimitiveRoot ((η₀ a : ℂˣ) : ℂ) S.degree := by
    rw [IsPrimitiveRoot.iff_orderOf]
    have hdvd : orderOf ((η₀ a : ℂˣ) : ℂ) ∣ S.degree := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← Units.val_pow_eq_pow_val, hpow η₀ hη₀, Units.val_one]
    rcases (Nat.dvd_prime S.degree_prime).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζ
    · exact h
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (ξ := ((η a : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, hpow η hη, Units.val_one])
  refine ⟨j, (hinj η hη (η₀ ^ j) (S.pow_mem_normCharacters hη₀ j) ?_)⟩
  apply Units.ext
  rw [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, hj]

/-- A unit level contained in the norm group bounds the Swan exponent of every norm
character. -/
theorem characterSwanExponent_le_of_unitFiltration_le {n : ℕ}
    (hn : letI := S.algebra
      haveI := S.finiteDimensional
      S.base.canonicalTopologicalData.unitFiltration n ≤ normSubgroup S.base.Carrier S.top.Carrier)
    {η : Correspondence.QuasiCharacter S.base} (hη : η ∈ S.normCharacters) :
    characterSwanExponent S.base η ≤ n - 1 := by
  have hle : S.base.canonicalTopologicalData.unitFiltration n ≤ η.toMonoidHom.ker :=
    hn.trans hη
  have hc := (S.base.canonicalTopologicalData.multiplicativeConductor_le_iff_unitFiltration_le_ker
    η n).mpr hle
  unfold characterSwanExponent
  omega

/-- In an unramified step every norm character has Swan exponent zero. -/
theorem characterSwanExponent_eq_zero_of_unramified
    (hE : S.base.canonicalTopologicalData.ramificationIndex =
      S.top.canonicalTopologicalData.ramificationIndex)
    {η : Correspondence.QuasiCharacter S.base} (hη : η ∈ S.normCharacters) :
    characterSwanExponent S.base η = 0 := by
  let := S.algebra
  have := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  have := S.finiteDimensional
  have hU := unramifiedUnitNorms p S.base S.top S.base.canonicalTopologicalData
    S.top.canonicalTopologicalData hE 0
  have h0 : S.base.canonicalTopologicalData.unitFiltration 0 ≤
      normSubgroup S.base.Carrier S.top.Carrier := by
    rw [← hU]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have := S.characterSwanExponent_le_of_unitFiltration_le h0 hη
  omega

/-- In a totally ramified step with lower break `t`, the norm characters have Swan exponent
at most `t`, the different exponent is `(t + 1)(ℓ - 1)`, and
`ψ_{M/L}(x) ≥ x + (ℓ - 1) max(0, x - t)` for `x ≥ 0`. -/
theorem exists_break_of_totallyRamified
    (hE : S.top.canonicalTopologicalData.ramificationIndex =
      S.degree * S.base.canonicalTopologicalData.ramificationIndex) :
    ∃ t : ℕ,
      (∀ η ∈ S.normCharacters, characterSwanExponent S.base η ≤ t) ∧
      S.differentExponent = (t + 1) * (S.degree - 1) ∧
      ∀ x : ℝ, 0 ≤ x → x + ((S.degree : ℝ) - 1) * max 0 (x - t) ≤ S.herbrandPsi x := by
  let := S.algebra
  have := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  have := S.finiteDimensional
  have := S.isGalois
  obtain ⟨t, hpat, -, -⟩ := primeTotallyRamifiedBreak p S.base S.top S.degree_prime hE
  refine ⟨t, ?_, ?_, ?_⟩
  · intro η hη
    have hred := (primeRamifiedNormReduction p S.base S.top S.degree_prime hE t hpat).1 (t + 1)
      (Nat.lt_succ_self t)
    have h1 : S.base.canonicalTopologicalData.unitFiltration (t + 1) ≤
        normSubgroup S.base.Carrier S.top.Carrier := by
      rw [← hred]
      rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    have := S.characterSwanExponent_le_of_unitFiltration_le h1 hη
    omega
  · have hd := primeRamifiedDifferent p S.base S.top S.degree_prime hE t hpat
    unfold differentExponent
    let TM := S.top.canonicalTopologicalData
    let := TM.topology
    let := TM.valuativeRel
    let := TM.localField
    have hinj : Function.Injective (fun n : ℕ => IsLocalRing.maximalIdeal TM.Integers ^ n) :=
      (Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field _)
        (Ideal.IsMaximal.ne_top inferInstance)).injective
    apply le_antisymm (Nat.sInf_le hd)
    refine le_csInf ⟨(t + 1) * (S.degree - 1), hd⟩ ?_
    intro d hd'
    exact (hinj (hd'.symm.trans hd)).ge
  · intro x hx
    have hcard : Nat.card (S.top.Carrier ≃ₐ[S.base.Carrier] S.top.Carrier) = S.degree :=
      S.degree_eq_card.symm
    change x + _ ≤ Ramification.Padic.herbrandPsi S.top.canonicalTopologicalData S.base.Carrier x
    rcases le_or_gt x t with hxt | hxt
    · rw [max_eq_left (by linarith), mul_zero, add_zero]
      exact Ramification.Padic.le_herbrandPsi_self _ _ hx
    · rw [max_eq_right (by linarith)]
      have hℓ : (0 : ℝ) < S.degree := by exact_mod_cast S.degree_prime.pos
      have hu : (t : ℝ) ≤ (t : ℝ) + S.degree * (x - t) := by nlinarith
      have hφ := Ramification.Padic.herbrandPhi_of_single_break _ _ t S.degree hcard hpat hu
      have hx' : Ramification.Padic.herbrandPhi S.top.canonicalTopologicalData S.base.Carrier
          ((t : ℝ) + S.degree * (x - t)) = x := by
        rw [hφ]
        field_simp
        ring
      rw [← hx', Ramification.Padic.herbrandPsi_herbrandPhi, hx']
      linarith

end NormCharacters

/-! ### Galois conjugation and conductors -/

/-- Galois conjugation does not change the conductor of a supercuspidal class of `M`. -/
theorem conductor_galoisConjugate (g : S.Gal) (k : ℕ)
    (τ : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    conductor S.top (S.galoisConjugate g k τ) = conductor S.top τ := by
  induction τ using Quotient.inductionOn with
  | h A =>
    let := S.top.canonicalTopologicalData.topology
    let := S.top.canonicalTopologicalData.valuativeRel
    let := S.top.canonicalTopologicalData.localField
    exact Conductor.firstFixedLevel_comp_fieldEquiv (S.galoisAutomorphism g).toRingEquiv
      (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv S.top S.top
        (S.galoisAutomorphism g))
      (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv S.top S.top
        (S.galoisAutomorphism g).symm)
      A.obj.representation

/-- Galois conjugation does not change the Swan exponent of a supercuspidal class of `M`. -/
theorem supercuspidalSwanExponent_galoisConjugate (g : S.Gal) (k : ℕ)
    (τ : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    supercuspidalSwanExponent S.top (S.galoisConjugate g k τ) =
      supercuspidalSwanExponent S.top τ := by
  unfold supercuspidalSwanExponent
  rw [S.conductor_galoisConjugate]

end Langlands.Henniart.Numerical.CyclicPrimeStep

/-! ### The slope bound -/

namespace Langlands.Henniart

open Correspondence Numerical

universe uK uV

/-- Henniart (1988), Proposition 6.7, for supercuspidal inputs (route note `lem:slopebc`):
under a weak cyclic base change of prime degree, a supercuspidal class of slope at most `x`
has only constituents of slope at most `ψ_{M/L}(x)`. -/
theorem baseChangeSlope : BaseChangeSlopeStatement.{uK, uV} := by
  classical
  intro hTwist p _ S Ch hW k π x s hs hsx ρ hρ
  obtain ⟨hW1, -, -⟩ := hW k
  obtain ⟨-, -, -, hW3a, hW3b, hW4⟩ := hW1 π
  have hℓ := S.degree_prime
  have hℓpos : (0 : ℤ) < S.degree := by exact_mod_cast hℓ.pos
  obtain ⟨hfin, hcard⟩ := S.normCharacters_finite_ncard
  set Xf := hfin.toFinset with hXf
  have hXcard : Xf.card ≤ S.degree := by
    rw [hXf, ← Set.ncard_eq_toFinset_card _ hfin]
    exact hcard
  have h1X : (1 : QuasiCharacter S.base) ∈ Xf := by
    rw [hXf, Set.Finite.mem_toFinset]
    exact S.one_mem_normCharacters
  -- Swan exponents of the twists `ηπ`
  set g : QuasiCharacter S.base → ℕ :=
    fun η => supercuspidalSwanExponent S.base (supercuspidalCharacterTwist S.base k η π) with hg
  have hgη : ∀ η, g η ≤ max s ((k + 1) * characterSwanExponent S.base η) := by
    intro η
    obtain ⟨s', hs', hle, -⟩ := hTwist p S.base k η π s hs
    rw [hg]
    dsimp only
    rw [supercuspidalSwanExponent_eq_of_hasSupercuspidalSwan hs']
    exact hle
  have hg1 : g 1 = s := by
    rw [hg]
    dsimp only
    have h1 : supercuspidalCharacterTwist S.base k 1 π = π := supercuspidalTwist_one S.base π
    rw [h1, supercuspidalSwanExponent_eq_of_hasSupercuspidalSwan hs]
  -- the conductor identity (W4) as a finite sum
  set tot : ℤ := ((Ch k π).map fun ρ => (supercuspidalSwanExponent S.top ρ.2 : ℤ)).sum
    with htot
  have hW4' : (S.residueDegree : ℤ) * tot =
      ((∑ η ∈ Xf, g η : ℕ) : ℤ) - S.residueDegree * S.wildDifferentExponent * ((k : ℤ) + 1) := by
    rw [htot, hW4, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  have hx : 0 ≤ x := by
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    have : ((k + 1 : ℕ) : ℝ) * x < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast Nat.succ_pos k) hneg'
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  -- the total Swan exponent of `Ch π` is at most `(k + 1) ψ(x)`
  have hsum : (tot : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * S.herbrandPsi x := by
    rcases S.unramified_or_totallyRamified with ⟨he, hf⟩ | ⟨he, hf⟩
    · -- unramified: `f = ℓ`, `c ≥ 0`, and every norm character is unramified
      have hE : S.base.canonicalTopologicalData.ramificationIndex =
          S.top.canonicalTopologicalData.ramificationIndex := by
        rw [S.top_ramificationIndex, he, one_mul]
      have hgs : ∀ η ∈ Xf, g η ≤ s := by
        intro η hη
        rw [hXf, Set.Finite.mem_toFinset] at hη
        have := hgη η
        rwa [S.characterSwanExponent_eq_zero_of_unramified hE hη, mul_zero, max_eq_left
          (Nat.zero_le s)] at this
      have hF : ∑ η ∈ Xf, g η ≤ S.degree * s := by
        calc ∑ η ∈ Xf, g η ≤ Xf.card • s := Finset.sum_le_card_nsmul _ _ _ hgs
          _ ≤ S.degree * s := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right s hXcard
      have hc : 0 ≤ S.wildDifferentExponent := by
        unfold CyclicPrimeStep.wildDifferentExponent
        rw [he]
        push_cast
        linarith [(Nat.cast_nonneg S.differentExponent : (0 : ℤ) ≤ S.differentExponent)]
      rw [hf] at hW4'
      have hF' : ((∑ η ∈ Xf, g η : ℕ) : ℤ) ≤ S.degree * s := by exact_mod_cast hF
      have hk : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
      have hmain : (S.degree : ℤ) * tot ≤ S.degree * s := by
        rw [hW4']
        have := mul_nonneg (mul_nonneg hℓpos.le hc) hk
        linarith
      have htots : tot ≤ s := le_of_mul_le_mul_left hmain hℓpos
      have htots' : (tot : ℝ) ≤ s := by exact_mod_cast htots
      have hψ := S.le_herbrandPsi hx
      nlinarith
    · -- totally ramified: `f = 1`, `c = t (ℓ - 1)`, and `sw(η) ≤ t` on `Ξ`
      have hE : S.top.canonicalTopologicalData.ramificationIndex =
          S.degree * S.base.canonicalTopologicalData.ramificationIndex := by
        rw [S.top_ramificationIndex, he]
      obtain ⟨t, hηt, hd, hψ⟩ := S.exists_break_of_totallyRamified hE
      set M := max s ((k + 1) * t) with hM
      have hgM : ∀ η ∈ Xf, g η ≤ M := by
        intro η hη
        rw [hXf, Set.Finite.mem_toFinset] at hη
        exact (hgη η).trans (max_le_max le_rfl (Nat.mul_le_mul_left _ (hηt η hη)))
      have hF : ∑ η ∈ Xf, g η ≤ s + (S.degree - 1) * M := by
        rw [← Finset.add_sum_erase Xf g h1X, hg1]
        apply Nat.add_le_add_left
        calc ∑ η ∈ Xf.erase 1, g η ≤ (Xf.erase 1).card • M :=
              Finset.sum_le_card_nsmul _ _ _ (fun η hη => hgM η (Finset.mem_of_mem_erase hη))
          _ ≤ (S.degree - 1) * M := by
              rw [smul_eq_mul, Finset.card_erase_of_mem h1X]
              exact Nat.mul_le_mul_right M (Nat.sub_le_sub_right hXcard 1)
      have hc : S.wildDifferentExponent = (t : ℤ) * ((S.degree : ℤ) - 1) := by
        unfold CyclicPrimeStep.wildDifferentExponent
        rw [hd, he]
        have h1 : 1 ≤ S.degree := hℓ.one_lt.le
        push_cast [h1]
        ring
      rw [hf, hc] at hW4'
      have hF' : ((∑ η ∈ Xf, g η : ℕ) : ℤ) ≤ s + ((S.degree : ℤ) - 1) * M := by
        have h1 : 1 ≤ S.degree := hℓ.one_lt.le
        have := (Nat.cast_le (α := ℤ)).mpr hF
        push_cast [h1] at this
        rw [Nat.cast_sum]
        exact this
      have htot1 : tot ≤ s + ((S.degree : ℤ) - 1) * (M - ((k : ℤ) + 1) * t) := by
        rw [Nat.cast_one, one_mul, one_mul] at hW4'
        linarith
      have htot1' : (tot : ℝ) ≤ s + ((S.degree : ℝ) - 1) * (M - ((k : ℝ) + 1) * t) := by
        exact_mod_cast htot1
      have hℓ1 : (0 : ℝ) ≤ (S.degree : ℝ) - 1 := by
        have : (1 : ℝ) ≤ S.degree := by exact_mod_cast hℓ.one_lt.le
        linarith
      have hψx := hψ x hx
      have hkk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hkk] at hsx hn ⊢
      rcases le_total s ((k + 1) * t) with hst | hst
      · have hMv : (M : ℝ) = ((k : ℝ) + 1) * t := by
          rw [hM, max_eq_right hst]; push_cast; ring
        rw [hMv, sub_self, mul_zero, add_zero] at htot1'
        have hmax : 0 ≤ max 0 (x - t) := le_max_left _ _
        have : x ≤ S.herbrandPsi x := by nlinarith
        nlinarith
      · have hMv : (M : ℝ) = s := by rw [hM, max_eq_left hst]
        rw [hMv] at htot1'
        have hst' : ((k : ℝ) + 1) * t ≤ s := by exact_mod_cast hst
        have hxt : (t : ℝ) ≤ x := by nlinarith
        rw [max_eq_right (by linarith)] at hψx
        nlinarith
  -- the structure of `Ch π`: (W3a) or (W3b)
  by_cases hA : ∀ η ∈ S.normCharacters, η ≠ 1 → supercuspidalCharacterTwist S.base k η π ≠ π
  · obtain ⟨⟨τ, hτ⟩, -⟩ := hW3a hA
    rw [hτ, Multiset.mem_singleton] at hρ
    subst hρ
    rw [htot, hτ, Multiset.map_singleton, Multiset.sum_singleton] at hsum
    exact_mod_cast hsum
  · simp only [not_forall, not_not, exists_prop] at hA
    obtain ⟨η₀, hη₀, h₀, hfix⟩ := hA
    have hpow : ∀ j : ℕ, supercuspidalCharacterTwist S.base k (η₀ ^ j) π = π := by
      intro j
      induction j with
      | zero => exact supercuspidalTwist_one S.base π
      | succ j ih =>
        have ih' : supercuspidalTwist S.base (η₀ ^ j) π = π := ih
        have h0 : supercuspidalTwist S.base η₀ π = π := hfix
        show supercuspidalTwist S.base (η₀ ^ (j + 1)) π = π
        rw [pow_succ', ← supercuspidalTwist_twist, ih', h0]
    have hall : ∀ η ∈ S.normCharacters, supercuspidalCharacterTwist S.base k η π = π := by
      intro η hη
      obtain ⟨j, rfl⟩ := S.exists_pow_eq_of_ne_one hη₀ h₀ hη
      exact hpow j
    obtain ⟨hdvd, ⟨k₁, τ₁, hk₁, -, hCh⟩, -⟩ := hW3b hall
    have htotCh : tot = (S.degree : ℤ) * supercuspidalSwanExponent S.top τ₁ := by
      rw [htot, hCh]
      unfold CyclicPrimeStep.galoisOrbit
      rw [Multiset.map_map]
      simp only [Function.comp_def, S.supercuspidalSwanExponent_galoisConjugate]
      have := S.finite_gal
      let : Fintype S.Gal := Fintype.ofFinite _
      rw [Multiset.map_const', Multiset.sum_replicate, Finset.card_val, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_eq_nat_card, ← S.degree_eq_card]
    rw [hCh] at hρ
    unfold CyclicPrimeStep.galoisOrbit at hρ
    obtain ⟨g₀, -, rfl⟩ := Multiset.mem_map.mp hρ
    dsimp only
    rw [S.supercuspidalSwanExponent_galoisConjugate]
    have hkk : k + 1 = (k₁ + 1) * S.degree := by
      rw [hk₁]
      exact (Nat.div_mul_cancel hdvd).symm
    rw [htotCh, hkk] at hsum
    push_cast at hsum ⊢
    have hℓr : (0 : ℝ) < S.degree := by exact_mod_cast hℓ.pos
    have h' : (S.degree : ℝ) * supercuspidalSwanExponent S.top τ₁ ≤
        (S.degree : ℝ) * (((k₁ : ℝ) + 1) * S.herbrandPsi x) := by
      linarith
    exact le_of_mul_le_mul_left h' hℓr

end Langlands.Henniart
