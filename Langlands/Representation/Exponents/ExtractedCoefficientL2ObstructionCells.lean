import Langlands.Representation.Classification.ProductLeviNecessityCells
import Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
import Langlands.Analysis.CountableCellLpProof

/-!
# Countably many disjoint cells below a diagonal uniformizer element of `GL_n`

Let `g ∈ GL_n(F)` be the diagonal matrix with the uniformizer on a set `S` of
coordinates and `1` elsewhere, with `S` and its complement nonempty. For the
abelian unipotent elements `unip S X` (entries at the positions `S × Sᶜ`) with
uniformizer-digit entries of length `m`, the translates
`h₀ · unip S (ϖ ^ t X) · g ^ (m + t) · KP` modulo the centre, for a fixed element
`h₀` and an open subgroup `KP` of the integral subgroup, are pairwise disjoint
over all `m` and all digit tuples. For `m` fixed the unipotent coordinates are
separated by `ProductLeviNecessity.level_of_mk_eq`; different exponents are
separated by a diagonal entry outside `S` and the determinant valuation.
A square-integrable function bounded below by `F0 M` on the translates of
exponent `M` therefore has `∑ m, q ^ (m |S| |Sᶜ|) F0 (m + t) ^ 2 μ(KP) < ∞`
(`Langlands.countableCellLpLower`).
-/

noncomputable section

open scoped BigOperators ENNReal Topology

namespace Langlands.ExtractedCoefficientL2Obstruction

open GeneralLinear MeasureTheory ProductLeviNecessity CartanQuotient.CellCount

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (S : Finset (Fin n))

/-! ### Small unipotent elements -/

/-- Unipotent elements with entries in a small enough lattice lie in a given open
subgroup of `GL_n`. -/
theorem exists_unip_mem :
    letI := T.topology
    ∀ K : OpenSubgroup (GeneralLinear n F.Carrier), ∃ t : ℕ, ∀ X : Pairs S → F.Carrier,
      (∀ x, T.discreteValuation (X x) ≤ 1) →
        unip S (fun x => T.uniformizer ^ t * X x) ∈ K := by
  let := T.topology
  intro K
  have hmem : (unip S : (Pairs S → F.Carrier) → GeneralLinear n F.Carrier) ⁻¹'
      (K : Set (GeneralLinear n F.Carrier)) ∈ 𝓝 (0 : Pairs S → F.Carrier) := by
    refine (continuous_unip T S).continuousAt.preimage_mem_nhds ?_
    rw [unip_zero]
    exact K.isOpen.mem_nhds K.one_mem
  rw [nhds_pi, Filter.mem_pi'] at hmem
  obtain ⟨I, u, hu, hsub⟩ := hmem
  choose e he using fun x => T.exists_additiveLattice_subset (hu x)
  refine ⟨∑ x, (e x).natAbs, fun X hX => hsub fun x _ => he x ?_⟩
  have hle : -(((∑ x, (e x).natAbs : ℕ)) : ℤ) ≤ e x := by
    have h1 : (e x).natAbs ≤ ∑ x, (e x).natAbs :=
      Finset.single_le_sum (f := fun x => (e x).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)
    have h2 := neg_abs_le (e x)
    rw [← Int.natCast_natAbs] at h2
    have h3 : ((e x).natAbs : ℤ) ≤ ((∑ x, (e x).natAbs : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  rw [SetLike.mem_coe, PadicField.TopologicalData.mem_additiveLattice]
  exact (level_uniformizer_pow_mul T _ (hX x)).trans (WithZero.exp_le_exp.mpr hle)

/-! ### The diagonal element and integral matrices -/

theorem pow_val_eq_diagonal {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ) :
    ((g ^ M : GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then
        ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M : F.Carrierˣ) : F.Carrier) else 1) := by
  rw [Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow]
  congr 1
  funext a
  simp only [Pi.pow_apply]
  split_ifs <;> simp

theorem uniformizerUnit_pow_value (M : ℕ) :
    T.discreteValuation ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M : F.Carrierˣ) :
      F.Carrier) = WithZero.exp (-(M : ℤ)) := by
  have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value T (M : ℤ)
  rwa [zpow_natCast] at h

theorem pow_val_le_one {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ) (i j : Fin n) :
    T.discreteValuation (((g ^ M : GeneralLinear n F.Carrier) :
      Matrix (Fin n) (Fin n) F.Carrier) i j) ≤ 1 := by
  rw [pow_val_eq_diagonal T S hg M, Matrix.diagonal_apply]
  split_ifs
  · rw [uniformizerUnit_pow_value]
    exact WithZero.exp_le_one_iff.mpr (by omega)
  · rw [map_one]
  · rw [map_zero]
    exact zero_le

/-- Matrices with integral entries are closed under products. -/
theorem le_one_mul_apply {A A' : Matrix (Fin n) (Fin n) F.Carrier}
    (hA : ∀ i j, T.discreteValuation (A i j) ≤ 1)
    (hA' : ∀ i j, T.discreteValuation (A' i j) ≤ 1) (i j : Fin n) :
    T.discreteValuation ((A * A') i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  refine T.discreteValuation.map_sum_le fun l _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i l) (hA' l j)

theorem valuation_det_eq_one {k : GeneralLinear n F.Carrier}
    (hk : k ∈ CartanQuotient.maximalCompact T n) :
    T.discreteValuation (k : Matrix (Fin n) (Fin n) F.Carrier).det = 1 := by
  have h := CuspidalSupport.LeviAdmissibility.valuation_det_integralRange
    T.discreteValuation hk
  rwa [GeneralLinear.determinant, Matrix.GeneralLinearGroup.val_det_apply] at h

theorem valuation_det_pow {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ) :
    T.discreteValuation ((g ^ M : GeneralLinear n F.Carrier) :
      Matrix (Fin n) (Fin n) F.Carrier).det = WithZero.exp (-((S.card * M : ℕ) : ℤ)) := by
  classical
  rw [pow_val_eq_diagonal T S hg M, Matrix.det_diagonal, map_prod]
  have h : ∀ a, T.discreteValuation (if a ∈ S then
      ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M : F.Carrierˣ) : F.Carrier) else 1) =
        if a ∈ S then WithZero.exp (-(M : ℤ)) else 1 := by
    intro a
    split_ifs
    · exact uniformizerUnit_pow_value T M
    · exact map_one _
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← WithZero.exp_nsmul]
  congr 1
  push_cast
  ring

/-! ### Disjointness across exponents -/

variable {S}

/-- Translated cells of the powers `g ^ M` and `g ^ M'` with the same image modulo
the centre satisfy `M' ≤ M`. -/
theorem le_of_mk_eq (hS : S.Nonempty) {b : Fin n} (hb : b ∉ S) {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) {M M' : ℕ}
    {u u' k k' : GeneralLinear n F.Carrier}
    (hu : u ∈ CartanQuotient.maximalCompact T n) (hu' : u' ∈ CartanQuotient.maximalCompact T n)
    (hk : k ∈ CartanQuotient.maximalCompact T n) (hk' : k' ∈ CartanQuotient.maximalCompact T n)
    (h : (QuotientGroup.mk (u * g ^ M * k) :
        GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) =
      QuotientGroup.mk (u' * g ^ M' * k')) : M' ≤ M := by
  have hs := QuotientGroup.eq.mp h
  set s := (u * g ^ M * k)⁻¹ * (u' * g ^ M' * k') with hs_def
  obtain ⟨z, hz⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hs
  have hcen := Subgroup.mem_center_iff.mp hs k'⁻¹
  have e1 : u' * g ^ M' * k' = u * g ^ M * k * s := by rw [hs_def, mul_inv_cancel_left]
  have he : g ^ M' = (u'⁻¹ * u) * g ^ M * (k * k'⁻¹) * s := by
    calc g ^ M' = u'⁻¹ * (u' * g ^ M' * k') * k'⁻¹ := by group
      _ = u'⁻¹ * (u * g ^ M * k * s) * k'⁻¹ := by rw [e1]
      _ = u'⁻¹ * u * g ^ M * k * (s * k'⁻¹) := by group
      _ = (u'⁻¹ * u) * g ^ M * (k * k'⁻¹) * s := by rw [← hcen]; group
  have hmat := congrArg (fun x : GeneralLinear n F.Carrier =>
    (x : Matrix (Fin n) (Fin n) F.Carrier)) he
  simp only [Units.val_mul, ← hz] at hmat
  have hint : ∀ {x : GeneralLinear n F.Carrier}, x ∈ CartanQuotient.maximalCompact T n →
      ∀ i j, T.discreteValuation ((x : Matrix (Fin n) (Fin n) F.Carrier) i j) ≤ 1 :=
    fun hx => ((mem_maximalCompact_iff (T := T) _).mp hx).1
  -- the diagonal entry outside `S`
  have hz1 : 1 ≤ T.discreteValuation z := by
    have hbb := congrFun (congrFun hmat b) b
    rw [pow_val_eq_diagonal T S hg M', Matrix.diagonal_apply_eq, Matrix.scalar_apply,
      Matrix.mul_diagonal] at hbb
    simp only [hb, ↓reduceIte] at hbb
    have h1 := congrArg T.discreteValuation hbb
    rw [map_one, map_mul] at h1
    have hle := le_one_mul_apply T (le_one_mul_apply T (le_one_mul_apply T
      (hint (inv_mem hu')) (hint hu)) (pow_val_le_one T S hg M))
        (le_one_mul_apply T (hint hk) (hint (inv_mem hk'))) b b
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1
      _ ≤ T.discreteValuation z := mul_le_of_le_one_left' hle
  -- the determinant
  have hdet := congrArg (fun X => T.discreteValuation (Matrix.det X)) hmat
  simp only [Matrix.det_mul, map_mul] at hdet
  rw [valuation_det_pow T S hg M', valuation_det_pow T S hg M,
    valuation_det_eq_one T (inv_mem hu'), valuation_det_eq_one T hu, valuation_det_eq_one T hk,
    valuation_det_eq_one T (inv_mem hk'), Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow, one_mul, one_mul,
    mul_one] at hdet
  have hle : WithZero.exp (-((S.card * M : ℕ) : ℤ)) ≤
      WithZero.exp (-((S.card * M' : ℕ) : ℤ)) := by
    rw [hdet]
    exact le_mul_of_one_le_right' (one_le_pow_of_one_le' hz1 n)
  rw [WithZero.exp_le_exp] at hle
  have hc : 0 < S.card := Finset.card_pos.mpr hS
  have hle' : S.card * M' ≤ S.card * M := by omega
  exact Nat.le_of_mul_le_mul_left hle' hc

/-! ### Disjointness for one exponent -/

variable (S)

/-- Two translated cells of `g ^ M` with the same image modulo the centre have
unipotent coordinates agreeing to level `M`. -/
theorem level_of_mk_eq {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M : ℕ)
    {Y Y' : Pairs S → F.Carrier} {k k' : GeneralLinear n F.Carrier}
    (hk : k ∈ CartanQuotient.maximalCompact T n) (hk' : k' ∈ CartanQuotient.maximalCompact T n)
    (h : (QuotientGroup.mk (unip S Y * g ^ M * k) :
        GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) =
      QuotientGroup.mk (unip S Y' * g ^ M * k')) (x : Pairs S) :
    Level T M (Y' x - Y x) := by
  have hj := QuotientGroup.eq.mp h
  have hd := pow_val_eq_diagonal T S hg M
  set d := g ^ M
  set s := (unip S Y * d * k)⁻¹ * (unip S Y' * d * k') with hs_def
  have hconj := inv_mul_unip_mul S (LocalFactor.PadicAbelian.uniformizerUnit T ^ M) hd (Y' - Y)
  have hU : unip S (fun x => (((LocalFactor.PadicAbelian.uniformizerUnit T ^ M)⁻¹ :
      F.Carrierˣ) : F.Carrier) * (Y' - Y) x) = (k * k'⁻¹) * s := by
    rw [← hconj, ← unip_inv_mul, mul_assoc k, Subgroup.mem_center_iff.mp hj k'⁻¹, hs_def]
    group
  have hint := le_one_of_unip_eq T S (mul_mem hk (inv_mem hk')) hj hU x
  have h0 : Level T 0 (((LocalFactor.PadicAbelian.uniformizerUnit T ^ (-(M : ℤ)) :
      F.Carrierˣ) : F.Carrier) * (Y' x - Y x)) := by
    rw [level_zero_iff, zpow_neg, zpow_natCast]
    simpa using hint
  simpa using (level_uniformizer_mul_iff 0 (M : ℤ) _).mp h0

/-! ### The countable cell sum -/

variable {S}

/-- A square-integrable function on the central quotient bounded below by `F0 M`
on the images of `h₀ * u * g ^ M * k`, with `u, k` in an open subgroup `KP` of the
integral subgroup, has a finite weighted sum
`∑ m, q ^ (m |S| |Sᶜ|) F0 (m + t) ^ 2 μ(KP)` for a fixed `t`, when `g` is diagonal
with the uniformizer on `S` and `1` elsewhere and `S`, `Sᶜ` are nonempty. -/
theorem cells_tsum_lt_top (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {g : GeneralLinear n F.Carrier}
    (hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1))
    (h0 : GeneralLinear n F.Carrier) :
    letI := T.topology
    ∀ (KP : OpenSubgroup (GeneralLinear n F.Carrier)),
      (KP : Set (GeneralLinear n F.Carrier)) ⊆ CartanQuotient.maximalCompact T n →
      ∀ [MeasurableSpace (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
        [BorelSpace (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
        (μ : Measure (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
        [μ.IsMulLeftInvariant]
        (f : GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier) → ℝ),
        MemLp f 2 μ → ∀ (F0 : ℕ → ℝ≥0∞),
        (∀ M : ℕ, ∀ u ∈ KP, ∀ k ∈ KP, F0 M ≤ ‖f (QuotientGroup.mk (h0 * u * g ^ M * k))‖ₑ) →
        ∃ t : ℕ, (∑' m : ℕ, (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
            (F0 (m + t) ^ 2 * μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier))))) <
          ⊤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro KP hKP _ _ μ _ f hf F0 hF0
  obtain ⟨t, ht⟩ := exists_unip_mem T S KP
  refine ⟨t, ?_⟩
  classical
  have := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  obtain ⟨b, hb⟩ := hSc
  have hb' : b ∉ S := Finset.mem_compl.mp hb
  let I := Σ m : ℕ, (Pairs S → Fin m → T.ResidueField)
  let U : I → GeneralLinear n F.Carrier := fun i =>
    unip S (fun x => T.uniformizer ^ t * digitVal T (i.2 x))
  have hU : ∀ i, U i ∈ KP := fun i => ht _ fun x => digitVal_le_one T _
  let h : I → GeneralLinear n F.Carrier := fun i => h0 * U i * g ^ (i.1 + t)
  let s : I → Set (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) :=
    fun i => (fun q => (h i : GeneralLinear n F.Carrier ⧸
      Subgroup.center (GeneralLinear n F.Carrier)) * q) ''
        ((↑) '' (KP : Set (GeneralLinear n F.Carrier)))
  have hopen0 : IsOpen ((↑) '' (KP : Set (GeneralLinear n F.Carrier)) :
      Set (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))) :=
    QuotientGroup.isOpenMap_coe (N := Subgroup.center (GeneralLinear n F.Carrier))
      (KP : Set (GeneralLinear n F.Carrier)) KP.isOpen
  have hopen : ∀ i, IsOpen (s i) := fun i => isOpenMap_mul_left _ _ hopen0
  have hmeas : ∀ i, μ (s i) = μ ((↑) '' (KP : Set (GeneralLinear n F.Carrier))) := by
    intro i
    simp only [s, Set.image_mul_left]
    exact measure_preimage_mul μ _ _
  have hdisj : Pairwise fun i i' => Disjoint (s i) (s i') := by
    rintro ⟨m, δ⟩ ⟨m', δ'⟩ hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩ ⟨_, ⟨k', hk', rfl⟩, he⟩
    apply hne
    have heq : (QuotientGroup.mk (U ⟨m, δ⟩ * g ^ (m + t) * k) :
        GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) =
        QuotientGroup.mk (U ⟨m', δ'⟩ * g ^ (m' + t) * k') := by
      have e2 : (QuotientGroup.mk (h ⟨m, δ⟩ * k) :
          GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)) =
          QuotientGroup.mk (h ⟨m', δ'⟩ * k') := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact he.symm
      simp only [h, mul_assoc] at e2
      rw [QuotientGroup.mk_mul _ h0, QuotientGroup.mk_mul _ h0] at e2
      rw [mul_assoc (U _), mul_assoc (U _)]
      exact mul_left_cancel e2
    have hm1 := le_of_mk_eq T hS hb' hg (hKP (hU _)) (hKP (hU _)) (hKP hk) (hKP hk') heq
    have hm2 := le_of_mk_eq T hS hb' hg (hKP (hU _)) (hKP (hU _)) (hKP hk') (hKP hk) heq.symm
    have hmm : m = m' := by omega
    subst hmm
    congr 1
    funext x
    have hl := level_of_mk_eq T S hg (m + t) (hKP hk) (hKP hk') heq x
    rw [← mul_sub] at hl
    have hl' := level_of_uniformizer_pow_mul t hl
    have hm : ((m + t : ℕ) : ℤ) - (t : ℤ) = (m : ℤ) := by push_cast; ring
    rw [hm] at hl'
    exact eq_of_level_digitVal_sub T _ _ hl'
  have hlow : ∀ i, ∀ y ∈ s i, F0 (i.1 + t) ≤ ‖f y‖ₑ := by
    rintro i _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have h1 := hF0 (i.1 + t) (U i) (hU i) k hk
    simpa only [h, QuotientGroup.mk_mul] using h1
  have hfin := countableCellLpLower _ I μ f 2 two_ne_zero ENNReal.ofNat_ne_top hf s
    (fun i => (hopen i).measurableSet) hdisj (fun i => F0 (i.1 + t)) hlow
  rw [ENNReal.tsum_sigma'] at hfin
  have hcard : ∀ m : ℕ, (Fintype.card (Pairs S → Fin m → T.ResidueField) : ℝ≥0∞) =
      (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) := by
    intro m
    rw [Fintype.card_fun, Fintype.card_fun, card_pairs,
      PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card, ← pow_mul,
      Fintype.card_fin]
    push_cast
    rfl
  convert hfin using 1
  refine tsum_congr fun m => ?_
  simp only [hmeas, ENNReal.toReal_ofNat, ENNReal.rpow_two, tsum_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]

end Langlands.ExtractedCoefficientL2Obstruction
