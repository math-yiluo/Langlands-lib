import Langlands.Representation.Classification.ProductLeviNecessityCells
import Langlands.Representation.Classification.ProductLeviNecessityEigen
import Langlands.Representation.Classification.ProductLeviNecessityTest

/-!
# Strict Jacquet exponent bounds for square-integrable product-Levi representations

Let `σ` be a representation of a product Levi which is square integrable modulo
the centre. For a weakly contracting block-scalar tuple whose `j`-th block is the
diagonal matrix with the uniformizer on a nonempty proper set `S` of coordinates,
every generalized eigencharacter `ψ` of the normalized refined Jacquet module
satisfies the strict bound `‖ψ(c)‖ < 1`.

The matrix coefficient of a compression eigenvector is `λ ^ M ℓ(x)` on the cells
`K g ^ M K`, with `‖λ‖ ^ 2 = q ^ (-|S| |Sᶜ|) ‖ψ(c)‖ ^ 2`. The translated cells of
all powers `g ^ M` are pairwise disjoint modulo the centre, so the square
integral of the coefficient dominates `∑_m (‖ψ(c)‖ ^ 2) ^ m` times a positive
constant. If `‖ψ(c)‖ ≥ 1` this sum is infinite.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal Topology

namespace Langlands.ProductLeviSquareIntegrable

open GeneralLinear Geometric ProductLeviChamber ProductLeviNecessity MeasureTheory

universe uF uV

/-! ### Diagonal entries -/

section Diagonal

variable {R : Type*} [CommRing R] {N : ℕ} (S : Finset (Fin N))

theorem diagonal_unip_diagonal_apply_self (e₁ e₂ : Fin N → R) (Z : Pairs S → R) (a : Fin N) :
    (Matrix.diagonal e₁ * (unip S Z : Matrix (Fin N) (Fin N) R) * Matrix.diagonal e₂) a a =
      e₁ a * e₂ a := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, unip_val, Matrix.add_apply, Matrix.one_apply_eq,
    offMatrix_apply_self, add_zero, mul_one]

/-- The inverse of an invertible diagonal matrix is diagonal. -/
theorem val_inv_of_val_eq_diagonal {d : GeneralLinear N R} {u : Fin N → Rˣ}
    (hd : (d : Matrix (Fin N) (Fin N) R) = Matrix.diagonal (fun a => (u a : R))) :
    ((d⁻¹ : GeneralLinear N R) : Matrix (Fin N) (Fin N) R) =
      Matrix.diagonal (fun a => (((u a)⁻¹ : Rˣ) : R)) := by
  let D' : GeneralLinear N R :=
    ⟨Matrix.diagonal (fun a => (((u a)⁻¹ : Rˣ) : R)), Matrix.diagonal (fun a => (u a : R)),
      by rw [Matrix.diagonal_mul_diagonal]; simp,
      by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  have h : d * D' = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, hd]
    change Matrix.diagonal _ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_mul_diagonal]
    simp
  rw [inv_eq_of_mul_eq_one_right h]

end Diagonal

/-! ### Cells of different powers are disjoint -/

section Disjoint

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n)

/-- The diagonal units of the `M`-th power of the diagonal element with the
uniformizer on `S`. -/
def powUnits {N : ℕ} (S : Finset (Fin N)) (M : ℕ) (a : Fin N) : F.Carrierˣ :=
  if a ∈ S then LocalFactor.PadicAbelian.uniformizerUnit T ^ M else 1

theorem powUnits_val {N : ℕ} (S : Finset (Fin N)) (M : ℕ) :
    (fun a => ((powUnits T S M a : F.Carrierˣ) : F.Carrier)) =
      fun a => if a ∈ S then
        ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M : F.Carrierˣ) : F.Carrier) else 1 := by
  funext a
  unfold powUnits
  split_ifs <;> simp

theorem valuation_uniformizerUnit_inv_pow_mul_pow (M M' : ℕ) :
    T.discreteValuation
        ((((LocalFactor.PadicAbelian.uniformizerUnit T ^ M)⁻¹ : F.Carrierˣ) : F.Carrier) *
          ((LocalFactor.PadicAbelian.uniformizerUnit T ^ M' : F.Carrierˣ) : F.Carrier)) =
      WithZero.exp (-(-(M : ℤ) + M')) := by
  rw [← Units.val_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_value]

/-- Two translated cells of powers `g ^ M` and `g ^ M'` with the same image
modulo the centre have the same exponent, when `S` and its complement are
nonempty. -/
theorem pow_eq_of_mk_eq (j : Fin C.length) (S : Finset (Fin (C.size j)))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {g : C.Levi F.Carrier}
    (hg : (g j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) (M M' : ℕ)
    {Y Y' : Pairs S → F.Carrier} {k k' : C.Levi F.Carrier}
    (hk : k j ∈ CartanQuotient.maximalCompact T (C.size j))
    (hk' : k' j ∈ CartanQuotient.maximalCompact T (C.size j))
    (h : (QuotientGroup.mk (Pi.mulSingle j (unip S Y) * g ^ M * k) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) =
      QuotientGroup.mk (Pi.mulSingle j (unip S Y') * g ^ M' * k')) : M = M' := by
  have hc := QuotientGroup.eq.mp h
  rw [Subgroup.center_pi, Subgroup.mem_pi] at hc
  have hj := hc j (Set.mem_univ j)
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at hj
  have hdv : (((g ^ M) j : GeneralLinear (C.size j) F.Carrier) :
      Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => ((powUnits T S M a : F.Carrierˣ) : F.Carrier)) := by
    rw [pow_apply_val_eq_diagonal T C j S hg M, powUnits_val]
  have hd'v : (((g ^ M') j : GeneralLinear (C.size j) F.Carrier) :
      Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => ((powUnits T S M' a : F.Carrierˣ) : F.Carrier)) := by
    rw [pow_apply_val_eq_diagonal T C j S hg M', powUnits_val]
  have hdinv := val_inv_of_val_eq_diagonal hdv
  have hd'inv := val_inv_of_val_eq_diagonal hd'v
  set d := (g ^ M) j with hd_def
  set d' := (g ^ M') j with hd'_def
  set s := (unip S Y * d * k j)⁻¹ * (unip S Y' * d' * k' j) with hs_def
  obtain ⟨c, hcs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hj
  set κ := k j * (k' j)⁻¹ with hκ
  have hκK : κ ∈ CartanQuotient.maximalCompact T (C.size j) := mul_mem hk (inv_mem hk')
  have hκ' := (CartanQuotient.CellCount.mem_maximalCompact_iff κ).mp hκK
  have hL : d⁻¹ * unip S (Y' - Y) * d' = κ * s := by
    rw [← unip_inv_mul, hκ, mul_assoc (k j), Subgroup.mem_center_iff.mp hj ((k' j)⁻¹), hs_def]
    group
  have hLinv : κ⁻¹ = s * (d'⁻¹ * unip S (Y - Y') * d) := by
    have e1 : (d⁻¹ * unip S (Y' - Y) * d')⁻¹ = d'⁻¹ * unip S (Y - Y') * d := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← unip_neg, neg_sub, mul_assoc]
    rw [← e1, hL, mul_inv_rev κ s, mul_inv_cancel_left]
  -- Diagonal entries of the two relations.
  have E1 : ∀ a, ((((powUnits T S M a)⁻¹ : F.Carrierˣ) : F.Carrier)) *
      ((powUnits T S M' a : F.Carrierˣ) : F.Carrier) =
        (κ : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) a a * c := by
    intro a
    have h1 := congrArg
      (fun x : GeneralLinear (C.size j) F.Carrier =>
        (x : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) a a) hL
    simp only [Units.val_mul, hdinv, hd'v, diagonal_unip_diagonal_apply_self] at h1
    rw [h1, ← hcs, Matrix.scalar_apply, Matrix.mul_diagonal]
  have E2 : ∀ a, ((κ⁻¹ : GeneralLinear (C.size j) F.Carrier) :
      Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) a a =
        c * ((((powUnits T S M' a)⁻¹ : F.Carrierˣ) : F.Carrier) *
          ((powUnits T S M a : F.Carrierˣ) : F.Carrier)) := by
    intro a
    rw [hLinv, Units.val_mul, ← hcs, Matrix.scalar_apply, Matrix.diagonal_mul, Units.val_mul,
      Units.val_mul, hd'inv, hdv, diagonal_unip_diagonal_apply_self]
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hSc
  have hb' : b ∉ S := Finset.mem_compl.mp hb
  have hPa : ∀ L : ℕ, powUnits T S L a = LocalFactor.PadicAbelian.uniformizerUnit T ^ L :=
    fun L => ite_eq_left ha
  have hPb : ∀ L : ℕ, powUnits T S L b = 1 := fun L => ite_eq_right hb'
  -- The scalar has valuation one.
  have hc1 : T.discreteValuation c ≤ 1 := by
    have h2 := hκ'.2 b b
    rw [E2 b, hPb, hPb, inv_one, Units.val_one, mul_one, mul_one] at h2
    exact h2
  have hc2 : 1 ≤ T.discreteValuation c := by
    have h1 := E1 b
    rw [hPb, hPb, inv_one, Units.val_one, mul_one] at h1
    have h2 := congrArg T.discreteValuation h1
    rw [map_one, map_mul] at h2
    rw [h2]
    exact mul_le_of_le_one_left' (hκ'.1 b b)
  have hcv : T.discreteValuation c = 1 := le_antisymm hc1 hc2
  -- The exponents agree.
  have hle1 : WithZero.exp (-(-(M : ℤ) + M')) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← valuation_uniformizerUnit_inv_pow_mul_pow T M M', ← hPa M, ← hPa M', E1 a, map_mul,
      hcv, mul_one]
    exact hκ'.1 a a
  have hle2 : WithZero.exp (-(-(M' : ℤ) + M)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← valuation_uniformizerUnit_inv_pow_mul_pow T M' M, ← hPa M, ← hPa M']
    have h2 := hκ'.2 a a
    rw [E2 a, map_mul, hcv, one_mul] at h2
    exact h2
  rw [WithZero.exp_le_one_iff] at hle1 hle2
  omega

end Disjoint

/-! ### Lower bound for an integral over disjoint translates -/

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Z : Subgroup G)
  [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] (μ : Measure (G ⧸ Z))
  [μ.IsMulLeftInvariant]

/-- Pairwise disjoint left translates of the image of an open set, on the `i`-th of
which a function is bounded below by `a i`, bound its integral below. -/
theorem sum_mul_le_lintegral {ι : Type*} [Fintype ι] (h : ι → G) {K : Set G} (hK : IsOpen K)
    (hdisj : Pairwise fun i i' =>
      Disjoint ((fun q => (h i : G ⧸ Z) * q) '' ((↑) '' K))
        ((fun q => (h i' : G ⧸ Z) * q) '' ((↑) '' K)))
    (f : G ⧸ Z → ℝ≥0∞) (a : ι → ℝ≥0∞) (hf : ∀ i, ∀ k ∈ K, a i ≤ f ((h i * k : G) : G ⧸ Z)) :
    ∑ i, a i * μ ((↑) '' K) ≤ ∫⁻ q, f q ∂μ := by
  set s : ι → Set (G ⧸ Z) := fun i => (fun q => (h i : G ⧸ Z) * q) '' ((↑) '' K)
  have hopen0 : IsOpen ((↑) '' K : Set (G ⧸ Z)) := QuotientGroup.isOpenMap_coe K hK
  have hopen : ∀ i, IsOpen (s i) := fun i => isOpenMap_mul_left _ _ hopen0
  have hmeas : ∀ i, μ (s i) = μ ((↑) '' K) := by
    intro i
    simp only [s, Set.image_mul_left]
    exact measure_preimage_mul μ _ _
  calc ∑ i, a i * μ ((↑) '' K) = ∑ i, ∫⁻ _ in s i, a i ∂μ := by
        simp only [setLIntegral_const, hmeas]
    _ ≤ ∑ i, ∫⁻ q in s i, f q ∂μ := by
        refine Finset.sum_le_sum fun i _ => setLIntegral_mono' (hopen i).measurableSet ?_
        rintro q ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        simpa only [QuotientGroup.mk_mul] using hf i k hk
    _ = ∫⁻ q in ⋃ i, s i, f q ∂μ := by
        rw [lintegral_iUnion (fun i => (hopen i).measurableSet) hdisj, tsum_fintype]
    _ ≤ ∫⁻ q, f q ∂μ := setLIntegral_le_lintegral _ _

end Measure

/-! ### The summed cell lower bound -/

section Lower

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n)

/-- A function on the central quotient bounded below by `F0 M` on the images of
`u * g ^ M * k` with `u, k` in an open subgroup `KP` of the integral product
Levi has integral at least `∑_{m < L} q ^ (m |S| |Sᶜ|) F0 (m + t) μ(KP)` for a
fixed `t` and every `L`, when the `j`-th block of `g` is diagonal with the
uniformizer on a nonempty proper subset `S` and `1` elsewhere. -/
theorem cells_sum_lower_bound (j : Fin C.length) (S : Finset (Fin (C.size j)))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {g : C.Levi F.Carrier}
    (hg : (g j : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1)) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (KP : OpenSubgroup (C.Levi F.Carrier)),
      (KP : Set (C.Levi F.Carrier)) ⊆ ProductLeviTempered.integralLevi T C →
      ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
        [μ.IsMulLeftInvariant]
        (f : C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier) → ℝ≥0∞) (F0 : ℕ → ℝ≥0∞),
        (∀ M : ℕ, ∀ u ∈ KP, ∀ k ∈ KP, F0 M ≤ f (QuotientGroup.mk (u * g ^ M * k))) →
        ∃ t : ℕ, ∀ L : ℕ,
          ∑ m ∈ Finset.range L, (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
              (F0 (m + t) * μ (QuotientGroup.mk '' (KP : Set (C.Levi F.Carrier)))) ≤
            ∫⁻ q, f q ∂μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro KP hKP _ _ μ _ f F0 hf
  obtain ⟨t, ht⟩ := exists_unip_mem T C j S KP
  refine ⟨t, fun L => ?_⟩
  classical
  have := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  let h : (Σ m : Fin L, (Pairs S → Fin m.val → T.ResidueField)) → C.Levi F.Carrier := fun i =>
    Pi.mulSingle j (unip S (fun x => T.uniformizer ^ t * digitVal T (i.2 x))) * g ^ (i.1.val + t)
  have hcard : ∀ m : ℕ, (Fintype.card (Pairs S → Fin m → T.ResidueField) : ℝ≥0∞) =
      (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) := by
    intro m
    rw [Fintype.card_fun, Fintype.card_fun, card_pairs,
      PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card, ← pow_mul,
      Fintype.card_fin]
    push_cast
    rfl
  have hsum : ∑ m ∈ Finset.range L, (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
      (F0 (m + t) * μ (QuotientGroup.mk '' (KP : Set (C.Levi F.Carrier)))) =
      ∑ i : (Σ m : Fin L, (Pairs S → Fin m.val → T.ResidueField)),
        F0 (i.1.val + t) * μ (QuotientGroup.mk '' (KP : Set (C.Levi F.Carrier))) := by
    rw [Finset.sum_range, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [hsum]
  refine sum_mul_le_lintegral (Subgroup.center (C.Levi F.Carrier)) μ h KP.isOpen ?_ f
    (fun i => F0 (i.1.val + t)) ?_
  · rintro ⟨m, δ⟩ ⟨m', δ'⟩ hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩ ⟨_, ⟨k', hk', rfl⟩, he⟩
    apply hne
    have hkj := (ProductLeviTempered.mem_integralLevi T C k).mp (hKP hk) j
    have hk'j := (ProductLeviTempered.mem_integralLevi T C k').mp (hKP hk') j
    have heq : (QuotientGroup.mk (h ⟨m, δ⟩ * k) :
        C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) =
          QuotientGroup.mk (h ⟨m', δ'⟩ * k') := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact he.symm
    have hmm := pow_eq_of_mk_eq T C j S hS hSc hg (m.val + t) (m'.val + t) hkj hk'j heq
    obtain rfl : m = m' := Fin.ext (by omega)
    refine congrArg (Sigma.mk m) (funext fun x => ?_)
    have hl := level_of_mk_eq T C j S hg (m.val + t) hkj hk'j heq x
    rw [← mul_sub] at hl
    have hl' := level_of_uniformizer_pow_mul t hl
    have hm : ((m.val + t : ℕ) : ℤ) - (t : ℤ) = (m.val : ℤ) := by push_cast; ring
    rw [hm] at hl'
    exact eq_of_level_digitVal_sub T _ _ hl'
  · intro i k hk
    exact hf (i.1.val + t) _ (ht _ fun x => digitVal_le_one T _) k hk

end Lower

/-! ### The strict exponent bound -/

section Strict

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The strict bound for a weakly contracting block-scalar tuple whose `j`-th
block is the diagonal matrix with the uniformizer on a nonempty proper subset `S`
and `1` elsewhere, and whose refined modulus is `q ^ (-|S| |Sᶜ|)`. -/
theorem norm_lt_one_of_diagonal :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsWeaklyContracting T (c i)) →
      ∀ (j : Fin C.length) (S : Finset (Fin (C.size j))), S.Nonempty → Sᶜ.Nonempty →
      ((D j).blockScalar F.Carrier (c j) : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
        Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1) →
      ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) =
        (T.residueCardinality : ℝ) ^ (-((S.card * Sᶜ.card : ℕ) : ℤ)) →
      ‖(ψ (flatScalars C D c) : ℂ)‖ < 1 := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq D ψ hgen c hc j S hS hSc hg hδ
  obtain ⟨hadm, χ, hL2⟩ := hsq
  obtain ⟨K, -, hKU, ℓ, x, hℓx, hxK, hℓK, hcoef⟩ :=
    exists_eigen_coefficient T C σ hadm D ψ hgen
      (ProductLeviTempered.integralLevi T C).mem_nhds_one c hc
  set g : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c i) with hg_def
  set lam := compressionEigenvalue T C D ψ c with hlam
  set P : ℕ := S.card * Sᶜ.card with hP
  set q : ℝ := (T.residueCardinality : ℝ) with hq
  have hq1 : 1 < q := T.one_lt_residueCardinality_real
  have hq0 : 0 < q := by linarith
  have hcell : ∀ M : ℕ, ∀ u ∈ K, ∀ k ∈ K,
      matrixCoefficient σ (ℓ : Module.Dual ℂ V) x (u * g ^ M * k) =
        lam ^ M * (ℓ : Module.Dual ℂ V) x := by
    intro M u hu k hk
    change (ℓ : Module.Dual ℂ V) (σ (u * g ^ M * k) x) = _
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hxK k hk, hℓK u hu]
    exact hcoef M
  set δ : ℝ := ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
    ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδ]
    exact zpow_pos hq0 _
  have hlamnorm : ‖lam‖ = Real.sqrt δ * ‖(ψ (flatScalars C D c) : ℂ)‖ := by
    rw [hlam, compressionEigenvalue, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hψpos : 0 < ‖(ψ (flatScalars C D c) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hlampos : 0 < ‖lam‖ := by
    rw [hlamnorm]
    exact mul_pos (Real.sqrt_pos.mpr hδpos) hψpos
  have hℓpos : 0 < ‖(ℓ : Module.Dual ℂ V) x‖ := norm_pos_iff.mpr hℓx
  set s := μ (QuotientGroup.mk '' (K : Set (C.Levi F.Carrier))) with hs
  have hs0 : 0 < s :=
    (QuotientGroup.isOpenMap_coe _ K.isOpen).measure_pos μ
      ⟨_, Set.mem_image_of_mem _ K.one_mem⟩
  let f : C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier) → ℝ≥0∞ :=
    fun z => ‖χ.coefficientNorm (ℓ : Module.Dual ℂ V) x z‖ₑ ^ (2 : ℝ)
  have hI : ∫⁻ z, f z ∂μ < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by norm_num) (hL2 ℓ x).eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat] using h
  obtain ⟨t, ht⟩ := cells_sum_lower_bound T C j S hS hSc hg K hKU μ f
      (fun M => ‖lam ^ M * (ℓ : Module.Dual ℂ V) x‖ₑ ^ (2 : ℝ)) (by
        intro M u hu k hk
        refine le_of_eq ?_
        show _ = ‖χ.coefficientNorm (ℓ : Module.Dual ℂ V) x
          (QuotientGroup.mk (u * g ^ M * k))‖ₑ ^ (2 : ℝ)
        rw [UnitaryCentralCharacter.coefficientNorm_mk, hcell M u hu k hk, enorm_norm])
  by_contra hge
  push Not at hge
  -- The ratio of consecutive cell contributions is `‖ψ(c)‖ ^ 2 ≥ 1`.
  have hkey : (1 : ℝ≥0∞) ≤ (T.residueCardinality : ℝ≥0∞) ^ P * ‖lam‖ₑ ^ 2 := by
    have hreal : q ^ P * ‖lam‖ ^ 2 = ‖(ψ (flatScalars C D c) : ℂ)‖ ^ 2 := by
      rw [hlamnorm, mul_pow, Real.sq_sqrt hδpos.le, hδ, zpow_neg, zpow_natCast, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul]
    have hconv : (T.residueCardinality : ℝ≥0∞) ^ P * ‖lam‖ₑ ^ 2 =
        ENNReal.ofReal (q ^ P * ‖lam‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq0.le,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, hq, ENNReal.ofReal_natCast]
    rw [hconv, hreal]
    exact ENNReal.one_le_ofReal.mpr (one_le_pow₀ hge)
  set C0 : ℝ≥0∞ := ‖lam‖ₑ ^ (2 * t) * ‖(ℓ : Module.Dual ℂ V) x‖ₑ ^ 2 * s with hC0
  have hC0ne : C0 ≠ 0 := by
    have h1 : ‖lam‖ₑ ≠ 0 := enorm_ne_zero.mpr (norm_pos_iff.mp hlampos)
    have h2 : ‖(ℓ : Module.Dual ℂ V) x‖ₑ ≠ 0 := enorm_ne_zero.mpr hℓx
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)) hs0.ne'
  have hterm : ∀ m : ℕ, C0 ≤ (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
      (‖lam ^ (m + t) * (ℓ : Module.Dual ℂ V) x‖ₑ ^ (2 : ℝ) * s) := by
    intro m
    have e : (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
        (‖lam ^ (m + t) * (ℓ : Module.Dual ℂ V) x‖ₑ ^ (2 : ℝ) * s) =
        ((T.residueCardinality : ℝ≥0∞) ^ P * ‖lam‖ₑ ^ 2) ^ m * C0 := by
      rw [ENNReal.rpow_two, enorm_mul, enorm_pow, hC0, ← hP]
      ring
    rw [e]
    exact le_mul_of_one_le_left' (one_le_pow₀ hkey)
  have hsumL : ∀ L : ℕ, (L : ℝ≥0∞) * C0 ≤ ∫⁻ z, f z ∂μ := by
    intro L
    calc (L : ℝ≥0∞) * C0 = ∑ m ∈ Finset.range L, C0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.range L, (T.residueCardinality : ℝ≥0∞) ^ (m * (S.card * Sᶜ.card)) *
            (‖lam ^ (m + t) * (ℓ : Module.Dual ℂ V) x‖ₑ ^ (2 : ℝ) * s) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ ≤ ∫⁻ z, f z ∂μ := ht L
  obtain ⟨L, hL⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hI.ne hC0ne).ne
  rw [ENNReal.div_lt_iff (Or.inl hC0ne) (Or.inr hI.ne)] at hL
  exact absurd ((hsumL L).trans_lt hL) (lt_irrefl _)

/-- The strict exponent bound at the fundamental coweights of the product Levi. -/
def StrictFundHypothesis (ρ : Representation ℂ (C.Levi F.Carrier) V) : Prop :=
  letI := T.topology
  ∀ (s : FundIndex C)
    (ψ : (Fin (C.flatten (fundRefinement C s)).length → F.Carrierˣ) →* ℂˣ),
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet C (fundRefinement C s) ρ).comp
        ((flattenedLeviEquiv F.Carrier C (fundRefinement C s)).toMonoidHom.comp
          ((C.flatten (fundRefinement C s)).blockScalarLevi F.Carrier))) ψ →
    ‖(ψ (flatScalars C (fundRefinement C s) (fundScalars T C s)) : ℂ)‖ < 1

theorem fundScalars_eq_testScalars (s : FundIndex C) :
    fundScalars T C s = testScalars T C (fundRefinement C s) s.1 1 1 := by
  funext i l
  simp only [fundScalars, testScalars, twoScalars]
  by_cases hi : i = s.1
  · rw [ite_eq_left hi]
    by_cases hl : l.val = 0
    · rw [ite_eq_left hl, ite_eq_left ⟨hi, by omega⟩, zpow_one]
    · rw [ite_eq_right hl, ite_eq_right (fun h => hl (by omega))]
  · rw [ite_eq_right hi, ite_eq_right (fun h => hi h.1)]

/-- Square integrability modulo the centre gives the strict exponent bound at
every fundamental coweight. -/
theorem strictFundHypothesis_of_squareIntegrable :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ → StrictFundHypothesis T C σ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq s ψ hgen
  have hfs := fundScalars_eq_testScalars T C s
  have hmod := fund_refinedLeviModulus T C s
  rw [hfs, testScalars_refinedLeviModulus] at hmod
  have hq0 : (0 : ℝ) < T.residueCardinality := by
    have := residueCardinality_gt_one_real T
    linarith
  have hq1 : (T.residueCardinality : ℝ) ≠ 1 := (residueCardinality_gt_one_real T).ne'
  have hcard := neg_inj.mp ((zpow_right_inj₀ hq0 hq1).mp hmod)
  have hcard' : (testSet C (fundRefinement C s) s.1 1).card *
      (testSet C (fundRefinement C s) s.1 1)ᶜ.card =
        (s.2.val + 1) * (C.size s.1 - (s.2.val + 1)) := by exact_mod_cast hcard
  have hpos : 0 < (s.2.val + 1) * (C.size s.1 - (s.2.val + 1)) := by
    have := fundIndex_lt C s
    apply Nat.mul_pos <;> omega
  rw [← hcard'] at hpos
  have hS : (testSet C (fundRefinement C s) s.1 1).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hpos; omega)
  have hSc : (testSet C (fundRefinement C s) s.1 1)ᶜ.Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hpos; omega)
  rw [hfs]
  exact norm_lt_one_of_diagonal T C μ σ hsq (fundRefinement C s) ψ hgen _
    (testScalars_isWeaklyContracting T C (fundRefinement C s) s.1 1) s.1 _ hS hSc
    (testScalars_blockScalar_same T C (fundRefinement C s) s.1 1)
    (testScalars_refinedLeviModulus T C (fundRefinement C s) s.1 1)

end Strict

end Langlands.ProductLeviSquareIntegrable
