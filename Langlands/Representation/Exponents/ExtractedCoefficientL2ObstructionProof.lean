import Langlands.Representation.Exponents.ExtractedCoefficientL2ObstructionStatement
import Langlands.Representation.Exponents.ExtractedCoefficientL2ObstructionCells
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Classification.ProductLeviNecessityTest
import Langlands.Group.GL.BlockContractionProof

/-!
# Strict L2 decay for one exactly extracted normalized coefficient

Let `x` be the real part of `χ`. By `IsRealPartOf.isPositiveRootCone_iff`, the
conclusion follows once `x` lies in the open positive root cone, that is once

* `‖χ (c, …, c)‖ = 1` for every scalar `c`: the identity at a deep tuple `b₀`
  and at `b₀ · (c, …, c)` differ by the central scalar `c`, on which the
  coefficient changes by the unitary central character and the half modulus
  is trivial; and
* `‖χ fₖ‖ < 1` for `0 < k < r`, where `fₖ` has the uniformizer on the blocks
  below `k` and `1` on the others: otherwise the coefficient at
  `h₀ g ^ M`, `h₀ = b₀`, `g = fₖ` (as block-scalar matrices), has norm
  `A λ ^ M` with `q ^ d λ ^ 2 = ‖χ fₖ‖ ^ 2 ≥ 1`, `d = |S| |Sᶜ|`, and it is
  constant on the translated cells of `ExtractedCoefficientL2ObstructionCells`
  for a compact open fixing subgroup; their weighted sum then diverges,
  contradicting `cells_tsum_lt_top`.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal Topology

namespace Langlands.ExtractedCoefficientL2Obstruction

open GeneralLinear MeasureTheory ProductLeviNecessity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### Deep tuples -/

/-- The tuple with the uniformizer at the indices below `k` and `1` elsewhere. -/
def partialUniformizer (r k : ℕ) : Fin r → F.Carrierˣ :=
  fun j => if (j : ℕ) < k then LocalFactor.PadicAbelian.uniformizerUnit T else 1

/-- `‖χ fₖ‖ = q ^ (-(x₁ + ⋯ + xₖ))` for the real part `x` of `χ`. -/
theorem norm_partialUniformizer {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ} {x : Fin r → ℝ}
    (hx : T.IsRealPartOf χ x) (k : ℕ) :
    ‖(χ (partialUniformizer T r k) : ℂ)‖ =
      (T.residueCardinality : ℝ) ^ (-Exponents.partialSum x k) := by
  have hq0 : (0 : ℝ) < T.residueCardinality :=
    lt_trans zero_lt_one T.one_lt_residueCardinality_real
  rw [hx, Exponents.partialSum, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hq0,
    Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [partialUniformizer]
  split_ifs
  · rw [LocalFactor.PadicAbelian.uniformizerUnit_coe, T.normalizedAbs_uniformizer,
      ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 1
    push_cast
    ring
  · rw [Units.val_one, T.normalizedAbs_one, Real.one_rpow]

variable {n : ℕ} (B : BlockShape n)

theorem exists_deep {ε : ℝ} (hε : 0 < ε) : ∃ b0 : Fin B.length → F.Carrierˣ,
    ∀ i j : Fin B.length, i < j →
      T.normalizedAbs ((b0 i : F.Carrier) / (b0 j : F.Carrier)) < ε := by
  obtain ⟨b0, hb0⟩ := B.deepChamberNonempty T ε hε
  refine ⟨b0, fun i j hij => ?_⟩
  have h := hb0 i j hij
  rwa [BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe, Units.val_mul,
    Units.val_inv_eq_inv_val, ← div_eq_mul_inv] at h

variable {B}

theorem deep_mul_const {ε : ℝ} {b0 : Fin B.length → F.Carrierˣ}
    (hb0 : ∀ i j : Fin B.length, i < j →
      T.normalizedAbs ((b0 i : F.Carrier) / (b0 j : F.Carrier)) < ε) (z : F.Carrierˣ) :
    ∀ i j : Fin B.length, i < j →
      T.normalizedAbs ((((b0 * fun _ : Fin B.length => z) i : F.Carrierˣ) : F.Carrier) /
        (((b0 * fun _ : Fin B.length => z) j : F.Carrierˣ) : F.Carrier)) < ε := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul]
  rw [mul_div_mul_right _ _ z.ne_zero]
  exact hb0 i j hij

theorem normalizedAbs_uniformizerUnit_pow_le_one (M : ℕ) :
    T.normalizedAbs ((LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ M) ≤ 1 := by
  have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (M : ℤ)
  rw [zpow_natCast, Units.val_pow_eq_pow_val] at h
  rw [h]
  exact zpow_le_one_of_nonpos₀ T.one_lt_residueCardinality_real.le (by omega)

/-- Multiplying a deep tuple by powers of `fₖ` keeps it deep, also on walls. -/
theorem deep_mul_pow {ε : ℝ} {b0 : Fin B.length → F.Carrierˣ}
    (hb0 : ∀ i j : Fin B.length, i < j →
      T.normalizedAbs ((b0 i : F.Carrier) / (b0 j : F.Carrier)) < ε) (k M : ℕ) :
    ∀ i j : Fin B.length, i < j →
      T.normalizedAbs ((((b0 * partialUniformizer T B.length k ^ M) i : F.Carrierˣ) :
          F.Carrier) /
        (((b0 * partialUniformizer T B.length k ^ M) j : F.Carrierˣ) : F.Carrier)) < ε := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  simp only [partialUniformizer, Pi.mul_apply, Pi.pow_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]
  by_cases hj : (j : ℕ) < k
  · have hi : (i : ℕ) < k := lt_trans hij' hj
    simp only [hi, hj, ↓reduceIte]
    rw [mul_div_mul_right _ _ (pow_ne_zero _ (Units.ne_zero _))]
    exact hb0 i j hij
  · by_cases hi : (i : ℕ) < k
    · simp only [hi, hj, ↓reduceIte, Units.val_one, one_pow, mul_one]
      rw [mul_div_right_comm, T.normalizedAbs_mul]
      calc _ ≤ T.normalizedAbs ((b0 i : F.Carrier) / (b0 j : F.Carrier)) * 1 :=
            mul_le_mul_of_nonneg_left (normalizedAbs_uniformizerUnit_pow_le_one T M)
              (T.normalizedAbs_nonneg _)
        _ < ε := by rw [mul_one]; exact hb0 i j hij
    · simp only [hi, hj, ↓reduceIte, Units.val_one, one_pow, mul_one]
      exact hb0 i j hij

/-! ### Common scalars -/

theorem leviHalfModulus_const (z : F.Carrierˣ) :
    T.leviHalfModulus B (B.blockScalarLevi F.Carrier fun _ => z) = 1 :=
  (T.leviHalfModulus_eq_one B _).mpr (T.leviModulus_scalar B z)

variable (B)

/-- The identity at `b₀` and at `b₀ · (z, …, z)` force `‖χ (z, …, z)‖ = 1`. -/
theorem norm_const_eq_one [TopologicalSpace (GeneralLinear n F.Carrier)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (c : UnitaryCentralCharacter ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (v : V) (ℓ : Module.Dual ℂ V) {ε : ℝ}
    (hε : 0 < ε)
    (hid : ∀ b : Fin B.length → F.Carrierˣ,
      (∀ i j : Fin B.length, i < j →
        T.normalizedAbs ((b i : F.Carrier) / (b j : F.Carrier)) < ε) →
      ℓ (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b)) v) =
        (T.leviHalfModulus B (B.blockScalarLevi F.Carrier b) : ℂ) * (χ b : ℂ))
    (z : F.Carrierˣ) : ‖(χ (fun _ => z) : ℂ)‖ = 1 := by
  obtain ⟨b0, hb0⟩ := exists_deep T B hε
  have h1 : matrixCoefficient ρ ℓ v (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b0))
      = _ := hid b0 hb0
  have h2 := hid (b0 * fun _ : Fin B.length => z) (deep_mul_const T hb0 z)
  have hemb : B.leviEmbedding F.Carrier
      (B.blockScalarLevi F.Carrier (b0 * fun _ : Fin B.length => z)) =
      B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b0) *
        ((GeneralLinear.scalarToCenter z : Subgroup.center (GeneralLinear n F.Carrier)) :
          GeneralLinear n F.Carrier) := by
    rw [map_mul, map_mul]
    congr 1
    apply Units.ext
    change (B.blockScalar F.Carrier (fun _ => z) : Matrix (Fin n) (Fin n) F.Carrier) =
      ((Matrix.GeneralLinearGroup.scalar (Fin n) z : GeneralLinear n F.Carrier) :
        Matrix (Fin n) (Fin n) F.Carrier)
    rw [B.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  rw [hemb] at h2
  change matrixCoefficient ρ ℓ v (_ * _) = _ at h2
  rw [c.matrixCoefficient_mul_center, h1] at h2
  simp only [map_mul, Units.val_mul, leviHalfModulus_const, mul_one] at h2
  have hne : (T.leviHalfModulus B (B.blockScalarLevi F.Carrier b0) : ℂ) * (χ b0 : ℂ) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have h3 : (c.character (GeneralLinear.scalarToCenter z) : ℂ) = (χ (fun _ => z) : ℂ) := by
    apply mul_right_cancel₀ hne
    rw [h2]
    ring
  rw [← h3, c.norm_eq_one]

/-! ### Basic chamber tuples -/

/-- The block modulus of `fₖ` is `q ^ (-|S| |Sᶜ|)`, where `S` is the set of
coordinates in the blocks below `k`. -/
theorem leviModulus_partialUniformizer (k : ℕ) :
    ((T.leviModulus B (B.blockScalarLevi F.Carrier (partialUniformizer T B.length k)) : ℝ≥0) :
        ℝ) =
      (T.residueCardinality : ℝ) ^
        (-(((Finset.univ.filter fun a : Fin n => ((B.indexEquiv.symm a).1 : ℕ) < k).card *
          (Finset.univ.filter fun a : Fin n => ((B.indexEquiv.symm a).1 : ℕ) < k)ᶜ.card :
            ℕ) : ℤ)) := by
  rw [leviModulus_blockScalarLevi_of_abs T B _ (fun l => if (l : ℕ) < k then 1 else 0)]
  · congr 2
    rw [card_filter_block B (fun l => (l : ℕ) < k), Finset.compl_filter,
      card_filter_block B (fun l => ¬ (l : ℕ) < k)]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have h : l < l' ↔ l.val < l'.val := Iff.rfl
    by_cases hll' : l < l'
    · have := h.mp hll'
      simp only [hll', ↓reduceIte]
      split_ifs <;> omega
    · have : ¬ l.val < l'.val := fun h' => hll' (h.mpr h')
      simp only [hll', ↓reduceIte]
      split_ifs <;> omega
  · intro l
    simp only [partialUniformizer]
    split_ifs
    · rw [LocalFactor.PadicAbelian.uniformizerUnit_coe, T.normalizedAbs_uniformizer]
    · rw [Units.val_one, T.normalizedAbs_one, neg_zero, zpow_zero]

theorem norm_leviHalfModulus_sq (m : B.Levi F.Carrier) :
    ‖(T.leviHalfModulus B m : ℂ)‖ ^ 2 = ((T.leviModulus B m : ℝ≥0) : ℝ) := by
  rw [PadicField.TopologicalData.leviHalfModulus_apply, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _), ← NNReal.coe_pow, NNReal.sq_sqrt]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Square integrability forces `‖χ fₖ‖ < 1` for `0 < k < r`. -/
theorem partial_norm_lt_one :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsSmooth ρ →
    ∀ (c : UnitaryCentralCharacter ρ)
      [MeasurableSpace (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
      [BorelSpace (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
      (μ : Measure (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
      [μ.IsHaarMeasure]
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (v : V) (ℓ : SmoothDual ρ) {ε : ℝ}, 0 < ε →
      (∀ b : Fin B.length → F.Carrierˣ,
        (∀ i j : Fin B.length, i < j →
          T.normalizedAbs ((b i : F.Carrier) / (b j : F.Carrier)) < ε) →
        ℓ.1 (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b)) v) =
          (T.leviHalfModulus B (B.blockScalarLevi F.Carrier b) : ℂ) * (χ b : ℂ)) →
      MemLp (c.coefficientNorm ℓ.1 v) 2 μ →
      ∀ k : ℕ, 0 < k → k < B.length → ‖(χ (partialUniformizer T B.length k) : ℂ)‖ < 1 := by
  let := T.topology
  intro ρ hρ c _ _ μ _ χ v ℓ ε hε hid hL2 k hk0 hkr
  let := T.valuativeRel
  let := T.localField
  classical
  by_contra hlt
  have hge : 1 ≤ ‖(χ (partialUniformizer T B.length k) : ℂ)‖ := not_lt.mp hlt
  obtain ⟨b0, hb0⟩ := exists_deep T B hε
  set f := partialUniformizer T B.length k with hf_def
  set h0 := B.blockScalar F.Carrier b0 with hh0
  set g := B.blockScalar F.Carrier f with hg_def
  set S : Finset (Fin n) := Finset.univ.filter fun a => ((B.indexEquiv.symm a).1 : ℕ) < k
    with hS_def
  have hg : (g : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1) := by
    rw [hg_def, B.coe_blockScalar]
    congr 1
    funext a
    simp only [hS_def, hf_def, partialUniformizer, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp
  -- the coefficient along the ray
  have hcoef : ∀ M : ℕ, matrixCoefficient ρ ℓ.1 v (h0 * g ^ M) =
      ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier b0) : ℂ) * (χ b0 : ℂ)) *
        ((T.leviHalfModulus B (B.blockScalarLevi F.Carrier f) : ℂ) * (χ f : ℂ)) ^ M := by
    intro M
    have h := hid (b0 * f ^ M) (deep_mul_pow T hb0 k M)
    have he : B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier (b0 * f ^ M)) =
        h0 * g ^ M := by
      change B.blockScalar F.Carrier (b0 * f ^ M) = _
      rw [map_mul, map_pow]
    rw [he] at h
    change matrixCoefficient ρ ℓ.1 v (h0 * g ^ M) = _ at h
    rw [h]
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  set q : ℝ := (T.residueCardinality : ℝ) with hq_def
  have hq1 : 1 < q := T.one_lt_residueCardinality_real
  set d : ℕ := S.card * Sᶜ.card with hd_def
  set a0 : ℝ := ‖(T.leviHalfModulus B (B.blockScalarLevi F.Carrier b0) : ℂ)‖ *
    ‖(χ b0 : ℂ)‖ with ha0
  set hh : ℝ := ‖(T.leviHalfModulus B (B.blockScalarLevi F.Carrier f) : ℂ)‖ with hhh
  set xx : ℝ := ‖(χ f : ℂ)‖ with hxx
  have ha0pos : 0 < a0 :=
    mul_pos (norm_pos_iff.mpr (Units.ne_zero _)) (norm_pos_iff.mpr (Units.ne_zero _))
  have hhpos : 0 < hh := norm_pos_iff.mpr (Units.ne_zero _)
  have hxpos : 0 < xx := norm_pos_iff.mpr (Units.ne_zero _)
  have hnorm : ∀ M : ℕ, ‖matrixCoefficient ρ ℓ.1 v (h0 * g ^ M)‖ = a0 * (hh * xx) ^ M := by
    intro M
    rw [hcoef, norm_mul, norm_mul, norm_pow, norm_mul]
  have hqd : q ^ d * hh ^ 2 = 1 := by
    rw [hhh, norm_leviHalfModulus_sq, hf_def, leviModulus_partialUniformizer, ← hS_def,
      ← hd_def, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (by linarith))]
  -- a compact open subgroup fixing the coefficient on both sides
  obtain ⟨H, hH⟩ := matrixCoefficient_biInvariant ρ ℓ.1 v ℓ.2 (hρ v)
  have hKopen : IsOpen (CartanQuotient.maximalCompact T n : Set (GeneralLinear n F.Carrier)) := by
    rw [ProductLeviTempered.maximalCompact_eq]
    exact CuspidalSupport.LeviAdmissibility.isOpen_integralRange n
  let Kmax : OpenSubgroup (GeneralLinear n F.Carrier) :=
    ⟨CartanQuotient.maximalCompact T n, hKopen⟩
  let cj : GeneralLinear n F.Carrier →* GeneralLinear n F.Carrier := (MulAut.conj h0).toMonoidHom
  have hcj : Continuous cj := by
    change Continuous fun x => h0 * x * h0⁻¹
    exact (continuous_const.mul continuous_id).mul continuous_const
  let KP : OpenSubgroup (GeneralLinear n F.Carrier) := Kmax ⊓ H ⊓ H.comap cj hcj
  have hKP : (KP : Set (GeneralLinear n F.Carrier)) ⊆ CartanQuotient.maximalCompact T n :=
    fun x hx => (OpenSubgroup.mem_inf.mp (OpenSubgroup.mem_inf.mp hx).1).1
  have hinv : ∀ M : ℕ, ∀ u ∈ KP, ∀ k' ∈ KP,
      matrixCoefficient ρ ℓ.1 v (h0 * u * g ^ M * k') =
        matrixCoefficient ρ ℓ.1 v (h0 * g ^ M) := by
    intro M u hu k' hk'
    have hu' : h0 * u * h0⁻¹ ∈ H := OpenSubgroup.mem_comap.mp (OpenSubgroup.mem_inf.mp hu).2
    have hk'' : k' ∈ H := (OpenSubgroup.mem_inf.mp (OpenSubgroup.mem_inf.mp hk').1).2
    have h1 := hH ⟨_, hu'⟩ ⟨k', hk''⟩ (h0 * g ^ M)
    have e : h0 * u * g ^ M * k' = h0 * u * h0⁻¹ * (h0 * g ^ M) * k' := by group
    rw [e]
    exact h1
  -- the cells
  have hSne : S.Nonempty := by
    refine ⟨B.indexEquiv ⟨⟨0, by omega⟩, ⟨0, B.positive _⟩⟩, ?_⟩
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact hk0
  have hScne : Sᶜ.Nonempty := by
    refine ⟨B.indexEquiv ⟨⟨k, hkr⟩, ⟨0, B.positive _⟩⟩, ?_⟩
    simp only [hS_def, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply]
    exact lt_irrefl k
  obtain ⟨t, ht⟩ := cells_tsum_lt_top T hSne hScne hg h0 KP hKP μ (c.coefficientNorm ℓ.1 v) hL2
    (fun M => ‖matrixCoefficient ρ ℓ.1 v (h0 * g ^ M)‖ₑ) (by
      intro M u hu k' hk'
      rw [UnitaryCentralCharacter.coefficientNorm_mk, hinv M u hu k' hk', enorm_norm])
  -- the divergent lower bound
  have hmu : μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier))) ≠ 0 :=
    ((QuotientGroup.isOpenMap_coe (N := Subgroup.center (GeneralLinear n F.Carrier))
      (KP : Set (GeneralLinear n F.Carrier)) KP.isOpen).measure_pos μ
        ⟨_, Set.mem_image_of_mem _ KP.one_mem⟩).ne'
  set C0 : ℝ := (a0 * (hh * xx) ^ t) ^ 2 with hC0_def
  have hC0 : 0 < C0 := by positivity
  have hterm : ∀ m : ℕ, ENNReal.ofReal C0 *
        μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier))) ≤
      (T.residueCardinality : ℝ≥0∞) ^ (m * d) *
        (‖matrixCoefficient ρ ℓ.1 v (h0 * g ^ (m + t))‖ₑ ^ 2 *
          μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier)))) := by
    intro m
    rw [← mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hnorm (m + t), pow_mul', ← hq_def]
    calc C0 = C0 * 1 := (mul_one _).symm
      _ ≤ C0 * (xx ^ 2) ^ m :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ (one_le_pow₀ hge)) hC0.le
      _ = C0 * ((q ^ d * hh ^ 2) ^ m * (xx ^ 2) ^ m) := by rw [hqd, one_pow, one_mul]
      _ = (q ^ d) ^ m * (a0 * (hh * xx) ^ (m + t)) ^ 2 := by rw [hC0_def]; ring
  have htop : (∑' m : ℕ, (T.residueCardinality : ℝ≥0∞) ^ (m * d) *
      (‖matrixCoefficient ρ ℓ.1 v (h0 * g ^ (m + t))‖ₑ ^ 2 *
        μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier))))) = ⊤ := by
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ENNReal.ofReal C0 *
          μ (QuotientGroup.mk '' (KP : Set (GeneralLinear n F.Carrier))) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero
            (mul_ne_zero (ENNReal.ofReal_pos.mpr hC0).ne' hmu)).symm
      _ ≤ _ := ENNReal.tsum_le_tsum hterm
  exact ht.ne htop

end Langlands.ExtractedCoefficientL2Obstruction

namespace Langlands

open ExtractedCoefficientL2Obstruction

universe uF uV

/-- Square integrability of one coefficient that equals the positive half
modulus times `χ` on a deep block-scalar chamber forces `‖χ a‖ < 1` on every
nonconstant direction of the closed chamber. -/
theorem glExtractedCoefficientL2Obstruction :
    GLExtractedCoefficientL2ObstructionStatement.{uF, uV} := by
  intro p _ F T n _ V _ _ ρ
  let := T.topology
  intro hρ c _ _ μ _ B χ hχ v ℓ ε hε _ hid hL2 a hmono hne
  obtain ⟨x, hx⟩ := T.exists_isRealPartOf χ hχ
  have hcone : Exponents.IsPositiveRootCone x := by
    refine ⟨hx.sum_eq_zero_iff.mpr (norm_const_eq_one T B c χ v ℓ.1 hε hid), fun k hk hkr => ?_⟩
    have h1 := partial_norm_lt_one T B ρ hρ c μ χ v ℓ hε hid hL2 k hk hkr
    rw [norm_partialUniformizer T hx k] at h1
    by_contra h2
    exact absurd h1 (not_lt.mpr (Real.one_le_rpow T.one_lt_residueCardinality_real.le
      (by linarith [not_lt.mp h2])))
  exact (hx.isPositiveRootCone_iff.mp hcone).2 a hmono hne

end Langlands
