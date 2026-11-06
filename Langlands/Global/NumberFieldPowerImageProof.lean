import Langlands.Global.NumberFieldPowerImageStatement
import Langlands.Global.AdelicUnitSequence
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Proof that power maps have non-open image on number-field adelic units -/

noncomputable section

universe u

open Filter Topology IsDedekindDomain
open scoped RestrictedProduct

namespace Langlands.Global

section Residue

/-- If a prime `ℓ` divides `n` and the number of units of a finite residue field, some
residue class is not an `n`th power. -/
theorem exists_not_pow_mod {B : Type*} [CommRing B] (P : Ideal B) [P.IsMaximal]
    [Finite (B ⧸ P)] {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0) (hℓn : ℓ ∣ n)
    (hcard : ℓ ∣ Nat.card (B ⧸ P) - 1) :
    ∃ c : B, ∀ a : B, a ^ n - c ∉ P := by
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hunits : ℓ ∣ Nat.card (B ⧸ P)ˣ := by rw [Nat.card_units]; exact hcard
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' ℓ hunits
  have hnotinj : ¬ Function.Injective (fun x : (B ⧸ P)ˣ => x ^ ℓ) := by
    intro h
    have h1 : ζ ^ ℓ = (1 : (B ⧸ P)ˣ) ^ ℓ := by rw [one_pow, ← hζ, pow_orderOf_eq_one]
    have h2 : ζ = 1 := h h1
    rw [h2, orderOf_one] at hζ
    exact hℓ.one_lt.ne hζ
  have hnotsurj : ¬ Function.Surjective (fun x : (B ⧸ P)ˣ => x ^ ℓ) :=
    fun hs => hnotinj (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hnotsurj
  obtain ⟨g, hg⟩ := hnotsurj
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (g : B ⧸ P)
  refine ⟨c, fun a ha => ?_⟩
  have h1 : (Ideal.Quotient.mk P a) ^ n = (g : B ⧸ P) := by
    rw [← hc, ← map_pow, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have ha0 : Ideal.Quotient.mk P a ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn] at h1
    exact g.ne_zero h1.symm
  obtain ⟨m, rfl⟩ := hℓn
  apply hg ((Units.mk0 _ ha0) ^ m)
  ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm m ℓ, h1]

end Residue

section Local

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {K : Type*} [Field K] [Algebra B K]
  [IsFractionRing B K] (w : HeightOneSpectrum B)

/-- A global element whose residue class is not an `n`th power is not an `n`th power in
the completion. -/
theorem not_pow_in_adicCompletion {n : ℕ} (hn : n ≠ 0) {c : B}
    (hc : ∀ a : B, a ^ n - c ∉ w.asIdeal) (z : w.adicCompletion K) :
    z ^ n ≠ algebraMap K (w.adicCompletion K) (algebraMap B K c) := by
  intro hz
  let ι := algebraMap K (w.adicCompletion K)
  have hval : ∀ y : K, Valued.v (ι y) = w.valuation K y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (K := K) y
  have hvalB : ∀ b : B, Valued.v (ι (algebraMap B K b)) = w.intValuation b := fun b => by
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
  have hc0 : c ∉ w.asIdeal := by
    have := hc 0
    rwa [zero_pow hn, zero_sub, Ideal.neg_mem_iff] at this
  have hvz : Valued.v z = 1 := by
    have h : Valued.v z ^ n = 1 := by
      rw [← map_pow, hz, hvalB]
      exact (w.intValuation_eq_one_iff_mem_primeCompl c).mpr hc0
    exact (pow_eq_one_iff_of_nonneg zero_le hn).mp h
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
  have hπv : Valued.v (ι π) < 1 := by
    rw [hval, hπ]
    exact WithZero.coe_lt_one.mpr (by decide)
  have hπne : ι π ≠ 0 := by
    intro h
    have := hval π
    rw [h, map_zero, hπ] at this
    exact WithZero.zero_ne_coe this
  let U : Set (w.adicCompletion K) := {y | (z - y) * (ι π)⁻¹ ∈ Valued.v.integer}
  have hU : IsOpen U :=
    (Valued.isOpen_integer (w.adicCompletion K)).preimage
      ((continuous_const.sub continuous_id).mul continuous_const)
  have hzU : z ∈ U := by
    simp only [U, Set.mem_ofPred_eq, sub_self, zero_mul]
    exact zero_mem _
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap K w).exists_mem_open hU ⟨z, hzU⟩
  have hzx : Valued.v (z - ι x) < 1 := by
    have h1 : Valued.v ((z - ι x) * (ι π)⁻¹) ≤ 1 := hx
    have h2 : z - ι x = ((z - ι x) * (ι π)⁻¹) * ι π := by
      rw [mul_assoc, inv_mul_cancel₀ hπne, mul_one]
    rw [h2, map_mul]
    exact (mul_le_of_le_one_left zero_le h1).trans_lt hπv
  have hxv : w.valuation K x ≤ 1 := by
    rw [← hval]
    have : ι x = z - (z - ι x) := by ring
    rw [this]
    exact (Valued.v.map_sub _ _).trans (max_le hvz.le hzx.le)
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hxv 1
  let a' : w.adicCompletion K := ι (algebraMap B K a)
  have ha' : Valued.v (a' - ι x) < 1 := by
    rw [← map_sub, hval]
    exact ha
  have hza : Valued.v (z - a') < 1 := by
    have : z - a' = (z - ι x) - (a' - ι x) := by ring
    rw [this]
    exact (Valued.v.map_sub _ _).trans_lt (max_lt hzx ha')
  have ha'v : Valued.v a' ≤ 1 := by
    rw [hvalB]
    exact w.intValuation_le_one a
  have hsum : Valued.v (∑ i ∈ Finset.range n, z ^ i * a' ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow, hvz, one_pow, one_mul]
    exact pow_le_one₀ zero_le ha'v
  have hdiff : Valued.v (z ^ n - a' ^ n) < 1 := by
    rw [← geom_sum₂_mul, map_mul]
    exact (mul_le_of_le_one_left zero_le hsum).trans_lt hza
  rw [hz] at hdiff
  have hmem : c - a ^ n ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, ← hvalB]
    simpa [a', map_sub, map_pow] using hdiff
  exact hc a (by rw [← neg_sub]; exact w.asIdeal.neg_mem_iff.mpr hmem)

end Local

section Topological

/-- A power map whose image misses a sequence tending to one has non-open image. -/
theorem not_isOpen_range_pow_of_tendsto {G : Type*} [Monoid G] [TopologicalSpace G] (n : ℕ)
    (u : ℕ → G) (hu : Tendsto u atTop (𝓝 1))
    (hnot : ∀ m, u m ∉ Set.range (fun x : G => x ^ n)) :
    ¬ IsOpen (Set.range (fun x : G => x ^ n)) := by
  intro hopen
  have h1 : (1 : G) ∈ Set.range (fun x : G => x ^ n) := ⟨1, one_pow n⟩
  obtain ⟨m, hm⟩ := (hu.eventually (hopen.mem_nhds h1)).exists
  exact hnot m hm

/-- Units converge when their values and inverse values converge. -/
theorem units_tendsto_one {M : Type*} [Monoid M] [TopologicalSpace M] (u : ℕ → Mˣ)
    (h₁ : Tendsto (fun m => (u m : M)) atTop (𝓝 1))
    (h₂ : Tendsto (fun m => ((u m)⁻¹ : Mˣ).val) atTop (𝓝 1)) :
    Tendsto u atTop (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h₁.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp h₂)

end Topological

section Restricted

variable {ι : Type u} {R : ι → Type*} [∀ i, Field (R i)]
    [∀ i, TopologicalSpace (R i)] (A : ∀ i, Subring (R i))
    (a : ∀ i, A i) (ha : ∀ i, (a i : R i) ≠ 0)

open scoped Classical in
omit [∀ i, TopologicalSpace (R i)] in
/-- With integral inverses, the inverse of a one-place unit is the one-place unit of the
inverse values. -/
theorem restrictedUnitAtPlace_inv_val (b : ∀ i, A i) (hb : ∀ i, (b i : R i) ≠ 0)
    (hab : ∀ i, (b i : R i) = (a i : R i)⁻¹) (i : ι) :
    (((restrictedUnitAtPlace A a ha i)⁻¹ : (Πʳ j, [R j, A j])ˣ) : Πʳ j, [R j, A j]) =
      restrictedUnitAtPlace A b hb i := by
  ext j
  rw [restrictedUnitAtPlace_val_apply]
  change (↑((if j = i then Units.mk0 (a j : R j) (ha j) else 1)⁻¹) : R j) = _
  split
  · simp [hab]
  · simp

end Restricted

section NumberField

variable (K : Type u) [Field K] [NumberField K]

open NumberField

/-- Above every large prime `p ≡ 1 [MOD ℓ]` there is a finite place whose residue field
has more than `N` elements and cardinality `≡ 1 [MOD ℓ]`. -/
theorem exists_place_card_modEq_one {ℓ : ℕ} (hℓ : ℓ.Prime) (N : ℕ) :
    ∃ v : FinitePlace K, N < Nat.card (𝓞 K ⧸ v.asIdeal) ∧
      ℓ ∣ Nat.card (𝓞 K ⧸ v.asIdeal) - 1 := by
  obtain ⟨p, hp, hNp, hpmod⟩ := Nat.exists_prime_gt_modEq_one N hℓ.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq : q.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP, hPe⟩ := q.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ _)]
    exact bot_le)
  have hPne : P ≠ ⊥ := by
    intro he
    rw [he, Ideal.under_bot] at hPe
    exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.mp hPe.symm)
  let v : FinitePlace K := ⟨P, hP, hPne⟩
  have : P.LiesOver q := ⟨hPe.symm⟩
  have : P.IsPrime := hP
  have hcard : Nat.card (𝓞 K ⧸ P) = p ^ P.inertiaDeg ℤ := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.natAbs_pow_inertiaDeg (p : ℤ) P]
    simp
  have hP1 : P ≠ ⊤ := hP.ne_top
  have hfin : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hPne
  have hnt : Nontrivial (𝓞 K ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP1
  have hf : P.inertiaDeg ℤ ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcard
    have := Finite.one_lt_card (α := 𝓞 K ⧸ P)
    rw [hcard] at this
    exact lt_irrefl _ this
  refine ⟨v, ?_, ?_⟩
  · change N < Nat.card (𝓞 K ⧸ P)
    rw [hcard]
    exact hNp.trans_le (Nat.le_self_pow hf p)
  · change ℓ ∣ Nat.card (𝓞 K ⧸ P) - 1
    rw [hcard]
    have h := (hpmod.pow (P.inertiaDeg ℤ)).symm
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h

/-- The places with residue cardinality `≡ 1 [MOD ℓ]` form an infinite set. -/
theorem infinite_places_card_modEq_one {ℓ : ℕ} (hℓ : ℓ.Prime) :
    {v : FinitePlace K | ℓ ∣ Nat.card (𝓞 K ⧸ v.asIdeal) - 1}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image (fun v : FinitePlace K => Nat.card (𝓞 K ⧸ v.asIdeal))).bddAbove
  obtain ⟨v, hvN, hv⟩ := exists_place_card_modEq_one K hℓ N
  exact absurd (hN ⟨v, hv, rfl⟩) (not_le.mpr hvN)

end NumberField

section Assembly

variable (K : Type u) [Field K] [NumberField K]

open NumberField

/-- Power maps of exponent at least `2` have non-open image on number-field adelic
units. -/
theorem numberField_units_powerImage_not_open {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsOpen (Set.range (fun x : (Adeles K)ˣ => x ^ n)) := by
  classical
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hn0 : n ≠ 0 := by omega
  let G : Set (FinitePlace K) := {v | ℓ ∣ Nat.card (𝓞 K ⧸ v.asIdeal) - 1}
  have hG : G.Infinite := infinite_places_card_modEq_one K hℓ
  have hres : ∀ v ∈ G, ∃ c : 𝓞 K, ∀ a : 𝓞 K, a ^ n - c ∉ v.asIdeal := by
    intro v hv
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have : v.asIdeal.IsMaximal := v.isMaximal
    exact exists_not_pow_mod v.asIdeal hℓ hn0 hℓn hv
  choose! c hc using hres
  let e : ℕ ↪ FinitePlace K :=
    (Set.Infinite.natEmbedding G hG).trans (Function.Embedding.subtype _)
  have he : ∀ m, e m ∈ G := fun m => (Set.Infinite.natEmbedding G hG m).2
  let ι := fun v : FinitePlace K => algebraMap K (v.adicCompletion K)
  have hvalB : ∀ (v : FinitePlace K) (b : 𝓞 K),
      Valued.v (ι v (algebraMap (𝓞 K) K b)) = v.intValuation b := fun v b => by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (K := K)
      (algebraMap (𝓞 K) K b)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h
    exact h
  have hcv : ∀ v ∈ G, Valued.v (ι v (algebraMap (𝓞 K) K (c v))) = 1 := by
    intro v hv
    rw [hvalB]
    apply (v.intValuation_eq_one_iff_mem_primeCompl (c v)).mpr
    have := hc v hv 0
    rwa [zero_pow hn0, zero_sub, Ideal.neg_mem_iff] at this
  let cv : ∀ v : FinitePlace K, v.adicCompletion K :=
    fun v => if v ∈ G then ι v (algebraMap (𝓞 K) K (c v)) else 1
  have hcvv : ∀ v, Valued.v (cv v) = 1 := by
    intro v
    by_cases hv : v ∈ G
    · simpa [cv, hv] using hcv v hv
    · simp [cv, hv]
  have hcv0 : ∀ v, cv v ≠ 0 := by
    intro v h
    have := hcvv v
    rw [h, map_zero] at this
    exact zero_ne_one this
  let A : ∀ v : FinitePlace K, Subring (v.adicCompletion K) :=
    fun v => (v.adicCompletionIntegers K).toSubring
  let a : ∀ v, A v := fun v =>
    ⟨cv v, (hcvv v).le⟩
  let b : ∀ v, A v := fun v =>
    ⟨(cv v)⁻¹, show Valued.v (cv v)⁻¹ ≤ 1 by rw [map_inv₀, hcvv v, inv_one]⟩
  have ha : ∀ v, (a v : v.adicCompletion K) ≠ 0 := hcv0
  have hb : ∀ v, (b v : v.adicCompletion K) ≠ 0 := fun v => inv_ne_zero (hcv0 v)
  have hab : ∀ v, (b v : v.adicCompletion K) = (a v : v.adicCompletion K)⁻¹ := fun _ => rfl
  let r : ℕ → (FiniteAdeles K)ˣ := fun m => restrictedUnitAtPlace A a ha (e m)
  let u : ℕ → (Adeles K)ˣ := fun m =>
    (MulEquiv.prodUnits : (Adeles K)ˣ ≃* (InfiniteAdeles K)ˣ × (FiniteAdeles K)ˣ).symm
      (1, r m)
  apply not_isOpen_range_pow_of_tendsto n u
  · apply units_tendsto_one
    · exact tendsto_const_nhds.prodMk_nhds (tendsto_restrictedUnitAtPlace_val A a ha e)
    · have hinv : ∀ m, (((u m)⁻¹ : (Adeles K)ˣ) : Adeles K) =
          (1, ((restrictedUnitAtPlace A b hb (e m)).val : FiniteAdeles K)) := by
        intro m
        rw [← restrictedUnitAtPlace_inv_val A a ha b hb hab (e m)]
        rfl
      simp_rw [hinv]
      exact tendsto_const_nhds.prodMk_nhds (tendsto_restrictedUnitAtPlace_val A b hb e)
  · rintro m ⟨y, hy⟩
    have hv := he m
    have h1 : ((u m : Adeles K).2 : FiniteAdeles K) (e m) =
        ι (e m) (algebraMap (𝓞 K) K (c (e m))) := by
      change ((restrictedUnitAtPlace A a ha (e m)).val) (e m) = _
      rw [restrictedUnitAtPlace_val_apply]
      simp [a, cv, hv]
    have h2 : ((u m : Adeles K).2 : FiniteAdeles K) (e m) =
        (((y : Adeles K).2 : FiniteAdeles K) (e m)) ^ n := by
      rw [← hy, Units.val_pow_eq_pow_val]
      exact RestrictedProduct.pow_apply _ ((y : Adeles K).2 : FiniteAdeles K) n (e m)
    exact not_pow_in_adicCompletion (e m) hn0 (hc (e m) hv) _ (h2.symm.trans h1)

end Assembly

section SchemePoints

open CategoryTheory Langlands.AlgebraicGeometry.PointTopology

/-- Non-openness of the power image on units transfers to actual punctured-line points. -/
theorem schemePoints_powerImage_not_open (S : Type u) [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] (n : ℕ) (h : ¬ IsOpen (Set.range (fun x : Sˣ => x ^ n)))
    (R : Type u) [CommRing R] [Algebra R S] :
    ¬ IsOpen (Set.range (α := RingPoint R (affineLinePuncture R) S)
      (fun p : RingPoint R (affineLinePuncture R) S => p ≫ affineLinePuncturePow R n)) := by
  intro hopen
  apply h
  let φ := affineLinePunctureUnitHomeomorph R S
  have hrange : Set.range (fun x : Sˣ => x ^ n) =
      φ.symm ⁻¹' (Set.range (α := RingPoint R (affineLinePuncture R) S)
        (fun p : RingPoint R (affineLinePuncture R) S => p ≫ affineLinePuncturePow R n)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨φ.symm y, φ.injective ?_⟩
      change affineLinePunctureUnitHomeomorph R S (φ.symm y ≫ affineLinePuncturePow R n) =
        φ (φ.symm (y ^ n))
      rw [affineLinePunctureUnitHomeomorph_pow, φ.apply_symm_apply, φ.apply_symm_apply]
    · rintro ⟨p, hp⟩
      refine ⟨φ p, ?_⟩
      change (affineLinePunctureUnitHomeomorph R S p) ^ n = x
      rw [← affineLinePunctureUnitHomeomorph_pow]
      change φ (p ≫ affineLinePuncturePow R n) = x
      rw [show (p ≫ affineLinePuncturePow R n : RingPoint R (affineLinePuncture R) S) =
        φ.symm x from hp, φ.apply_symm_apply]
  rw [hrange]
  exact hopen.preimage φ.symm.continuous

end SchemePoints

/-- Proof of `NumberFieldPowerImageStatement`. -/
theorem numberFieldPowerImage : NumberFieldPowerImageStatement.{u} := by
  intro K _ _ n hn
  exact ⟨numberField_units_powerImage_not_open K hn, fun R _ _ =>
    schemePoints_powerImage_not_open (Adeles K) n (numberField_units_powerImage_not_open K hn) R⟩

end Langlands.Global
