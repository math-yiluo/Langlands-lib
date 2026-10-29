import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement
import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.Representation.RankinSelberg.IwasawaTorusSumProof
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumStatement
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.Conductor.SphericalIntegrals
import Langlands.Group.GL.NormalizedCharacter

/-!
# Reduction of the restriction-square estimate to the torus lattice sum
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

namespace SquareIntegrableWhittakerRestriction

/-- A function on a topological group that is invariant under right
multiplication by an open subgroup is continuous. -/
theorem continuous_of_rightInvariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace X] (f : G → X) (J : Subgroup G)
    (hJ : IsOpen (J : Set G)) (hf : ∀ g : G, ∀ j ∈ J, f (g * j) = f g) :
    Continuous f := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hmem : (fun x => g⁻¹ * x) ⁻¹' (J : Set G) ∈ nhds g := by
    apply (hJ.preimage (continuous_const.mul continuous_id)).mem_nhds
    simp [J.one_mem]
  filter_upwards [hmem] with x hx
  simpa only [mul_inv_cancel_left] using hf g (g⁻¹ * x) hx

/-- The pairwise ratio product over `i < j` in closed form. -/
theorem prod_pairs_div (N : ℕ) (c : Fin N → ℝ) :
    ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j : Fin N => i < j), c i / c j =
      (∏ i : Fin N, c i ^ (N - 1 - i.val)) / ∏ i : Fin N, c i ^ i.val := by
  simp_rw [Finset.prod_div_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  · rw [Finset.prod_comm' (t' := Finset.univ)
      (s' := fun j => Finset.univ.filter (fun i : Fin N => i < j))
      (by intro i j; simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_const, Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- A product over a padded index set whose padding terms equal one. -/
theorem prod_padOne (n d : ℕ) (x : Fin (n + 1) → ℝ) (e : ℕ → ℕ) :
    ∏ i : Fin (n + d + 1), (if h : i.val < n + 1 then x ⟨i.val, h⟩ else 1) ^ e i.val =
      ∏ i : Fin (n + 1), x i ^ e i.val := by
  rw [Fin.prod_univ_eq_prod_range
    (fun i => (if h : i < n + 1 then x ⟨i, h⟩ else 1) ^ e i) (n + d + 1),
    show n + d + 1 = (n + 1) + d by omega, Finset.prod_range_add,
    ← Fin.prod_univ_eq_prod_range
      (fun i => (if h : i < n + 1 then x ⟨i, h⟩ else 1) ^ e i) (n + 1)]
  have htail : ∏ j ∈ Finset.range d,
      (if h : n + 1 + j < n + 1 then x ⟨n + 1 + j, h⟩ else 1) ^ e (n + 1 + j) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    simp [show ¬(n + 1 + j < n + 1) by omega]
  rw [htail, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [i.isLt]

/-- The upper-Borel modulus of `diag(a, 1_d)` is the modulus of `a` times
`(∏ g (a i)) ^ d`, for any positive function `g` of the exponents with `g 0 = 1`. -/
theorem modulus_padZero (g : ℤ → ℝ) (hg0 : g 0 = 1) (n d : ℕ) (a : Fin (n + 1) → ℤ) :
    ∏ i : Fin (n + d + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + d + 1) => i < j),
        g (if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0) /
          g (if h : j.val < n + 1 then a ⟨j.val, h⟩ else 0) =
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        g (a i) / g (a j)) * (∏ i : Fin (n + 1), g (a i)) ^ d := by
  have hc (i : Fin (n + d + 1)) : g (if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0) =
      if h : i.val < n + 1 then g (a ⟨i.val, h⟩) else 1 := by
    split_ifs <;> simp [hg0]
  rw [prod_pairs_div (n + d + 1) (fun i => g (if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0)),
    prod_pairs_div (n + 1) (fun i => g (a i))]
  simp only [hc]
  rw [prod_padOne n d (fun i => g (a i)) (fun i => n + d + 1 - 1 - i),
    prod_padOne n d (fun i => g (a i)) (fun i => i)]
  have hexp : ∏ i : Fin (n + 1), g (a i) ^ (n + d + 1 - 1 - i.val) =
      (∏ i : Fin (n + 1), g (a i) ^ (n + 1 - 1 - i.val)) * (∏ i : Fin (n + 1), g (a i)) ^ d := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add]
    congr 1
    have := i.isLt
    omega
  rw [hexp, div_mul_eq_mul_div]

/-- Pad an exponent vector of the small torus by zeros. -/
def extendExp (n d : ℕ) (a : Fin (n + 1) → ℤ) : Fin (n + d) → ℤ :=
  fun j => if h : j.val < n + 1 then a ⟨j.val, h⟩ else 0

theorem snoc_extendExp (n d : ℕ) (hd : 0 < d) (a : Fin (n + 1) → ℤ) (i : Fin (n + d + 1)) :
    (Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) i =
      if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0 := by
  induction i using Fin.lastCases with
  | last =>
    have hlast : ¬((Fin.last (n + d)).val < n + 1) := by
      rw [Fin.val_last]
      omega
    rw [Fin.snoc_last, dite_eq_right hlast]
  | cast j =>
    rw [Fin.snoc_castSucc]
    rfl

theorem extendExp_injective (n d : ℕ) (hd : 0 < d) :
    Function.Injective (extendExp n d) := by
  intro a b hab
  funext i
  have h := congrFun hab ⟨i.val, by have := i.isLt; omega⟩
  simpa [extendExp, i.isLt] using h

/-- Adjoining an identity block to a torus element gives the torus element of the
zero-padded exponent vector. -/
theorem appendIdentity_torus {F : Type*} [Field F] (n d : ℕ) (ϖ : Fˣ)
    (a : Fin (n + 1) → ℤ) :
    appendIdentity n d (Iwasawa.torus ϖ a) =
      Iwasawa.torus ϖ (fun i : Fin (n + d + 1) =>
        if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0) := by
  apply Units.ext
  ext i j
  rw [appendIdentity_entry]
  simp only [Iwasawa.torus_val, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < n + 1 <;> simp [hi]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    split_ifs <;> simp_all

/-- Adjoining an identity block to a torus element gives the torus element of the
zero-extended exponent vector with last exponent zero. -/
theorem appendIdentity_torus_snoc {F : Type*} [Field F] (n d : ℕ) (hd : 0 < d) (ϖ : Fˣ)
    (a : Fin (n + 1) → ℤ) :
    appendIdentity n d (Iwasawa.torus ϖ a) =
      Iwasawa.torus ϖ (Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) := by
  rw [appendIdentity_torus]
  congr 1
  funext i
  rw [snoc_extendExp n d hd a i]

theorem modulus_snoc_extendExp (g : ℤ → ℝ) (hg0 : g 0 = 1) (n d : ℕ) (hd : 0 < d)
    (a : Fin (n + 1) → ℤ) :
    ∏ i : Fin (n + d + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + d + 1) => i < j),
        g ((Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) i) /
          g ((Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) j) =
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
        g (a i) / g (a j)) * (∏ i : Fin (n + 1), g (a i)) ^ d := by
  simp only [snoc_extendExp n d hd a]
  exact modulus_padZero g hg0 n d a

/-- The inverse upper-Borel modulus of `diag(ϖ^a, 1_d)` is the inverse modulus of
`ϖ^a` times `|det ϖ^a| ^ (-d)`. -/
theorem inverseModulus_snoc_extendExp {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) (ϖ : F.Carrierˣ) (n d : ℕ) (hd : 0 < d)
    (a : Fin (n + 1) → ℤ) :
    (∏ i : Fin (n + d + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + d + 1) => i < j),
      T.normalizedAbs ((ϖ ^ (Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) i /
        ϖ ^ (Fin.snoc (extendExp n d a) 0 : Fin (n + d + 1) → ℤ) j : F.Carrierˣ) :
          F.Carrier))⁻¹ =
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((ϖ ^ a i / ϖ ^ a j : F.Carrierˣ) : F.Carrier))⁻¹ *
      normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ a).val) ^ (-((d : ℕ) : ℝ)) := by
  let g : ℤ → ℝ := fun z => T.normalizedAbs ((ϖ ^ z : F.Carrierˣ) : F.Carrier)
  have hdiv (x y : ℤ) :
      T.normalizedAbs ((ϖ ^ x / ϖ ^ y : F.Carrierˣ) : F.Carrier) = g x / g y := by
    rw [Units.val_div_eq_div_val]
    exact map_div₀ (normalizedAbsoluteValue T) _ _
  have hg0 : g 0 = 1 := by
    simp only [g, zpow_zero, Units.val_one]
    exact T.normalizedAbs_one
  have hdet : normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ a).val) =
      ∏ i, g (a i) := by
    rw [Iwasawa.torus_val, Matrix.det_diagonal, map_prod]
    rfl
  have hpos : 0 ≤ ∏ i, g (a i) := Finset.prod_nonneg fun i _ => T.normalizedAbs_nonneg _
  simp only [hdiv]
  rw [modulus_snoc_extendExp g hg0 n d hd a, hdet, Real.rpow_neg hpos, Real.rpow_natCast,
    mul_inv]

theorem continuous_appendIdentity {F : Type*} [Field F] [TopologicalSpace F] (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

/-- Formula (7) of JPSS 1983 §8.3 from the quotient Iwasawa formula, the discrete
torus decomposition and the torus lattice square-summability. -/
theorem of_torusSum
    (hIw : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
      QuotientIwasawaIntegrationStatement F T n)
    (hSum : IwasawaTorusSumStatement.{uF})
    (hB1 : SquareIntegrableWhittakerTorusSumStatement.{uF, uV}) :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV} := by
  intro p _ F T n k ψ _ μ hμ V _ _ π hirr hsq ℓ f
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  have hd : 0 < 0 + k + 1 := by omega
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let dk : Measure (GeneralLinear (n + 1) F.Carrier) :=
    (generalLinearHaar F.Carrier n).restrict (K : Set (GeneralLinear (n + 1) F.Carrier))
  let δt : (Fin (n + 1) → ℤ) → ℝ := fun lam =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((ϖ ^ lam i / ϖ ^ lam j : F.Carrierˣ) : F.Carrier)
  let qLam : (Fin (n + 1) → ℤ) → GeneralLinear (n + 1) F.Carrier →
      LeftUnipotentQuotient n F.Carrier := fun lam x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam * x)
  have hμeq : μ = Measure.sum (fun lam : Fin (n + 1) → ℤ =>
      ENNReal.ofReal ((δt lam)⁻¹) • Measure.map (qLam lam) dk) :=
    (hIw p F T n μ hμ).trans (hSum p F T n ϖ hϖ)
  -- Right smoothness of the Whittaker function and a finite cover of `K`.
  have hsmooth := hsq.isAdmissible.1
  obtain ⟨L, hL⟩ := model_isSmooth π hsmooth ℓ f
  have hLinv : ∀ y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier, ∀ l ∈ L,
      f.val.val (y * l) = f.val.val y := fun y l hl =>
    congrArg (fun w : (coefficientModel π ℓ).toSubmodule => w.val.val y) (hL ⟨l, hl⟩)
  let e := appendIdentity (F := F.Carrier) n (0 + k + 1)
  have he : Continuous e := continuous_appendIdentity n _
  let H := L.comap e he
  have hKzero : (Conductor.levelOpenSubgroup F.Carrier n 0 :
      Set (GeneralLinear (n + 1) F.Carrier)) = (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    change (Conductor.levelSubgroup F.Carrier n 0 : Set (GeneralLinear (n + 1) F.Carrier)) =
      (K : Set (GeneralLinear (n + 1) F.Carrier))
    rw [Conductor.levelSubgroup_zero]
  have hKcompact : IsCompact (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  have hKmeas : MeasurableSet (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  have hdet (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      normalizedAbsoluteValue T (Matrix.det x.val) = 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup hx
    have hx0 : Matrix.det x.val ≠ 0 := by
      intro hx0
      rw [hx0, map_zero] at hv
      exact zero_ne_one hv
    have hd1 : T.discreteValuation (Matrix.det x.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (ValuativeRel.valuation F.Carrier (Matrix.det x.val)) = 1
      rw [hv, map_one]
    rw [normalizedAbsoluteValue_apply, T.normalizedAbs_of_ne_zero hx0]
    simp [PadicField.TopologicalData.ord, hd1]
  obtain ⟨S, hS⟩ := hKcompact.elim_finite_subcover
    (fun ρ : GeneralLinear (n + 1) F.Carrier =>
      (fun x => ρ⁻¹ * x) ⁻¹' (H : Set (GeneralLinear (n + 1) F.Carrier)))
    (fun ρ => H.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, by
      show x⁻¹ * x ∈ H
      rw [inv_mul_cancel]
      exact H.one_mem⟩)
  have hcover (y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier)
      (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      ‖f.val.val (y * e x)‖ ^ 2 ≤ ∑ ρ ∈ S, ‖f.val.val (y * e ρ)‖ ^ 2 := by
    have hxS := hS hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at hxS
    obtain ⟨ρ, hρS, hρ⟩ := hxS
    have hl : e (ρ⁻¹ * x) ∈ L := hρ
    have hxρ := hLinv (y * e ρ) _ hl
    rw [mul_assoc, ← map_mul e, mul_inv_cancel_left] at hxρ
    rw [hxρ]
    exact Finset.single_le_sum (f := fun ρ => ‖f.val.val (y * e ρ)‖ ^ 2)
      (fun i _ => sq_nonneg _) hρS
  -- Continuity of the integrand on the quotient.
  let Φ : LeftUnipotentQuotient n F.Carrier → ℝ := fun q =>
    restrictedWhittakerNorm ψ k f.val q ^ 2 *
      quotientDeterminantAbs (normalizedAbsoluteValue T) n q ^ (-(((0 + k + 1 : ℕ) : ℝ)))
  have hΦnn (q : LeftUnipotentQuotient n F.Carrier) : 0 ≤ Φ q :=
    mul_nonneg (pow_nonneg (restrictedWhittakerNorm_nonneg ψ k f.val q) 2)
      (Real.rpow_nonneg (quotientDeterminantAbs_nonneg _ n q) _)
  have hWc : Continuous (fun y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier => f.val.val y) :=
    continuous_of_rightInvariant _ L.toSubgroup L.isOpen hLinv
  have hdetc : Continuous (fun g : GeneralLinear (n + 1) F.Carrier =>
      normalizedAbsoluteValue T (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (T.determinantNormContinuous (n + 1)).continuous)).congr fun x => rfl
  have hΦc : Continuous Φ := by
    have hW : Continuous (restrictedWhittakerNorm ψ k f.val) :=
      Continuous.quotient_lift (continuous_norm.comp (hWc.comp he)) _
    have hD : Continuous (quotientDeterminantAbs (normalizedAbsoluteValue T) n) :=
      Continuous.quotient_lift hdetc _
    exact (hW.pow 2).mul
      (hD.rpow_const fun q => Or.inl (quotientDeterminantAbs_pos _ n q).ne')
  have hΦm : Measurable (fun q => ENNReal.ofReal (Φ q)) :=
    ENNReal.measurable_ofReal.comp hΦc.measurable
  have hqc (lam : Fin (n + 1) → ℤ) : Continuous (qLam lam) :=
    (leftQuotient_isOpenQuotientMap _).continuous.comp (continuous_const.mul continuous_id)
  -- The pointwise bound on each compact orbit.
  let C : (Fin (n + 1) → ℤ) → ℝ := fun lam =>
    (∑ ρ ∈ S, ‖f.val.val (e (Iwasawa.torus ϖ lam) * e ρ)‖ ^ 2) *
      normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ lam).val) ^
        (-(((0 + k + 1 : ℕ) : ℝ)))
  have hpt (lam : Fin (n + 1) → ℤ) (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      Φ (qLam lam x) ≤ C lam := by
    change ‖f.val.val (e (Iwasawa.torus ϖ lam * x))‖ ^ 2 *
        normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ lam * x).val) ^
          (-(((0 + k + 1 : ℕ) : ℝ))) ≤ C lam
    rw [map_mul e, Units.val_mul, Matrix.det_mul, map_mul (normalizedAbsoluteValue T),
      hdet x hx, mul_one]
    exact mul_le_mul_of_nonneg_right (hcover _ x hx)
      (Real.rpow_nonneg (AbsoluteValue.nonneg _ _) _)
  -- The lattice terms of the bridge for the finitely many right translates.
  let a : GeneralLinear (n + 1) F.Carrier → (Fin (n + 1) → ℤ) → ℝ := fun ρ lam =>
    (∏ i : Fin (n + (0 + k + 1) + 1),
      ∏ j ∈ Finset.univ.filter (fun j : Fin (n + (0 + k + 1) + 1) => i < j),
        T.normalizedAbs ((ϖ ^ (Fin.snoc (extendExp n (0 + k + 1) lam) 0 :
            Fin (n + (0 + k + 1) + 1) → ℤ) i /
          ϖ ^ (Fin.snoc (extendExp n (0 + k + 1) lam) 0 :
            Fin (n + (0 + k + 1) + 1) → ℤ) j : F.Carrierˣ) : F.Carrier))⁻¹ *
      ‖f.val.val (Iwasawa.torus ϖ (Fin.snoc (extendExp n (0 + k + 1) lam) 0 :
        Fin (n + (0 + k + 1) + 1) → ℤ) * e ρ)‖ ^ 2
  have ha_nn (ρ : GeneralLinear (n + 1) F.Carrier) (lam : Fin (n + 1) → ℤ) : 0 ≤ a ρ lam :=
    mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
      T.normalizedAbs_nonneg _)) (sq_nonneg _)
  have hasum (ρ : GeneralLinear (n + 1) F.Carrier) : Summable (a ρ) := by
    have hB := hB1 p F T (n + (0 + k + 1)) ψ V π hirr hsq ℓ
      (modelRepresentation π ℓ (e ρ) f) ϖ hϖ
    dsimp only at hB
    exact hB.comp_injective (extendExp_injective n _ hd)
  have hδnn (lam : Fin (n + 1) → ℤ) : 0 ≤ δt lam :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => T.normalizedAbs_nonneg _
  have hbound (lam : Fin (n + 1) → ℤ) :
      ∫⁻ q, ENNReal.ofReal (Φ q) ∂(ENNReal.ofReal (δt lam)⁻¹ • Measure.map (qLam lam) dk) ≤
        ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := by
    rw [lintegral_smul_measure, lintegral_map hΦm (hqc lam).measurable, smul_eq_mul]
    calc ENNReal.ofReal (δt lam)⁻¹ * ∫⁻ x, ENNReal.ofReal (Φ (qLam lam x)) ∂dk
        ≤ ENNReal.ofReal (δt lam)⁻¹ * ∫⁻ _x, ENNReal.ofReal (C lam) ∂dk := by
          exact mul_le_mul_of_nonneg_left
            (lintegral_mono_ae (ae_restrict_of_forall_mem hKmeas fun x hx =>
              ENNReal.ofReal_le_ofReal (hpt lam x hx))) zero_le
      _ = ENNReal.ofReal ((δt lam)⁻¹ * C lam) := by
          rw [lintegral_const]
          simp only [dk, K, Measure.restrict_apply_univ, generalLinearHaar_integralSubgroup,
            mul_one]
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hδnn lam))]
      _ = ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := by
          congr 1
          simp only [a, C, e]
          rw [inverseModulus_snoc_extendExp T ϖ n _ hd lam,
            appendIdentity_torus_snoc n _ hd ϖ lam, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          simp only [δt]
          ring
  -- Assemble.
  show Integrable Φ μ
  rw [hμeq]
  refine ⟨hΦc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn), lintegral_sum_measure]
  calc ∑' lam, ∫⁻ q, ENNReal.ofReal (Φ q) ∂(ENNReal.ofReal (δt lam)⁻¹ • Measure.map (qLam lam) dk)
      ≤ ∑' lam, ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (∑' lam, ∑ ρ ∈ S, a ρ lam) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun lam => Finset.sum_nonneg fun ρ _ => ha_nn ρ lam)
        (summable_sum fun ρ _ => hasum ρ)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Formula (7) of JPSS 1983 §8.3 from the torus lattice square-summability, with the
quotient Iwasawa formula and the discrete torus decomposition supplied by their
published proofs. -/
theorem of_squareIntegrableWhittakerTorusSum
    (hB1 : SquareIntegrableWhittakerTorusSumStatement.{uF, uV}) :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV} :=
  of_torusSum (fun _ _ F T n => quotientIwasawaIntegration F T n) iwasawaTorusSum hB1

end SquareIntegrableWhittakerRestriction

end Langlands.RankinSelberg
