import Langlands.Representation.RankinSelberg.UnitaryCellMasses

/-!
# Square-summability of unitary Whittaker functions on the mirabolic torus lattice

Let `ρ` be an irreducible admissible unitarizable representation of `GL_(k+2)(F)` over a
p-adic field, `ℓ` a standard Whittaker functional, `v` a vector and `ϖ` a uniformizing
element. Then the family

`lam ↦ δ(ϖ^lam)⁻¹ · ‖ℓ(ρ(diag(ϖ^lam, 1)) v)‖²`,  `lam : Fin (k+1) → ℤ`,

is summable, where `δ` is the modulus character of the upper Borel subgroup of `GL_(k+1)`,
so that `δ(ϖ^lam)⁻¹` is `QuotientTorusEnvelope.density ϖ lam`. This is the torus-lattice
form of Jacquet–Shalika, *Euler products I*, Proposition (1.3), display (1.3.1): the Whittaker
functions of a unitary generic representation are square-integrable on `N \ P`.

The proof applies `padicCellBound` (module `UnitaryCellBound`) to the cells of the torus
elements `diag(ϖ^lam, 1)` for a compact open subgroup of the mirabolic group fixing `v`, and
bounds their masses from below with the torus decomposition of the quotient measure. It
generalizes `UnramifiedUnitary.rowSum_bounded` (single-row exponents, spherical vectors).
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory GeneralLinear HarmonicAnalysis Induction QuotientIntegration Whittaker
open UnramifiedUnitary

universe uF uV

/-! ### Lower bound for the quotient measure on a torus translate of an open set -/

section Masses

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A set of `N \ GL_(k+1)` containing the classes of `ϖ^λ x` for all `x` in a measurable
subset `K'` of `GL_(k+1)(O)` has mass at least the inverse modulus of `ϖ^λ` times the Haar
mass of `K'`. -/
theorem density_mul_haar_le_quotientMeasure (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (k + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (k + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient k F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient k F.Carrier) := ⟨rfl⟩
    ∀ ϖ : F.Carrierˣ, Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
    ∀ (lam : Fin (k + 1) → ℤ) (K' : Set (Langlands.GeneralLinear (k + 1) F.Carrier)),
      MeasurableSet K' →
      K' ⊆ (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k : Set _) →
      ∀ Y : Set (LeftUnipotentQuotient k F.Carrier),
      (∀ x ∈ K', leftQuotientMap (upperUnipotent (k + 1) F.Carrier) (Iwasawa.torus ϖ lam * x) ∈ Y) →
      ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) * generalLinearHaar F.Carrier k K' ≤
        unipotentQuotientHaar F.Carrier k Y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (k + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (k + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient k F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient k F.Carrier) := ⟨rfl⟩
  intro ϖ hϖ lam K' hK' hK'K Y hY
  let G := Langlands.GeneralLinear (k + 1) F.Carrier
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k
  let q := fun (x : G) => leftQuotientMap (upperUnipotent (k + 1) F.Carrier)
    (Iwasawa.torus ϖ lam * x)
  have hq : Measurable q :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  rw [QuotientTorusEnvelope.quotientMeasure_eq_sum_torus F T k _
    (unipotentQuotientHaar_isCompatible F.Carrier k) ϖ hϖ]
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ lam) Y)
  rw [Measure.smul_apply, smul_eq_mul]
  have h1 : generalLinearHaar F.Carrier k K' ≤
      Measure.map q ((generalLinearHaar F.Carrier k).restrict (K : Set G)) Y := by
    refine le_trans ?_ (Measure.le_map_apply hq.aemeasurable Y)
    calc generalLinearHaar F.Carrier k K'
        = generalLinearHaar F.Carrier k (K' ∩ (K : Set G)) := by
          rw [Set.inter_eq_left.2 hK'K]
      _ = ((generalLinearHaar F.Carrier k).restrict (K : Set G)) K' :=
          (Measure.restrict_apply hK').symm
      _ ≤ _ := measure_mono (fun x hx => hY x hx)
  gcongr

end Masses

/-! ### The measure on `N \ P` and the masses of torus cells -/

section MirabolicMeasure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance torusFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance torusFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance torusFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The torus element `diag(ϖ^lam, 1)` of the mirabolic group `P_(k+1) ⊆ GL_(k+2)`. -/
def torusElement (ϖ : F.Carrierˣ) (k : ℕ) (lam : Fin (k + 1) → ℤ) : mirabolic (k + 1) F.Carrier :=
  Mirabolic.levi (Iwasawa.torus ϖ lam)

theorem torusElement_val (ϖ : F.Carrierˣ) (k : ℕ) (lam : Fin (k + 1) → ℤ) :
    (torusElement F ϖ k lam).val = Iwasawa.torus ϖ (Fin.snoc lam 0) :=
  levi_torus ϖ lam

/-- The points of `GL_(k+1)(O)` whose Levi image lies in a given subgroup of `P_(k+1)`. -/
def leviIntegralSet (k : ℕ) (K : OpenSubgroup (mirabolic (k + 1) F.Carrier)) :
    Set (Langlands.GeneralLinear (k + 1) F.Carrier) :=
  {x | Mirabolic.levi x ∈ K} ∩
    ((Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k :
      Subgroup (Langlands.GeneralLinear (k + 1) F.Carrier)) :
        Set (Langlands.GeneralLinear (k + 1) F.Carrier))

theorem isOpen_leviIntegralSet (k : ℕ) (K : OpenSubgroup (mirabolic (k + 1) F.Carrier)) :
    IsOpen (leviIntegralSet F k K) := by
  refine IsOpen.inter (K.isOpen.preimage Mirabolic.continuous_levi) ?_
  have h := (Conductor.levelOpenSubgroup F.Carrier k 0).isOpen
  have he : ((Conductor.levelOpenSubgroup F.Carrier k 0 :
        OpenSubgroup (Langlands.GeneralLinear (k + 1) F.Carrier)) :
          Set (Langlands.GeneralLinear (k + 1) F.Carrier)) =
      ((Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer k :
        Subgroup (Langlands.GeneralLinear (k + 1) F.Carrier)) :
          Set (Langlands.GeneralLinear (k + 1) F.Carrier)) := by
    change ((Conductor.levelSubgroup F.Carrier k 0 :
      Subgroup (Langlands.GeneralLinear (k + 1) F.Carrier)) :
        Set (Langlands.GeneralLinear (k + 1) F.Carrier)) = _
    rw [Conductor.levelSubgroup_zero]
  rw [← he]
  exact h

theorem one_mem_leviIntegralSet (k : ℕ) (K : OpenSubgroup (mirabolic (k + 1) F.Carrier)) :
    (1 : Langlands.GeneralLinear (k + 1) F.Carrier) ∈ leviIntegralSet F k K :=
  ⟨by simp only [Set.mem_ofPred_eq, map_one]; exact one_mem K, one_mem _⟩

/-- A right-invariant measure on `N \ P_(k+1)` with positive finite orbit masses, under
which the cell of `diag(ϖ^lam, 1)` for a subgroup `K` has mass at least the inverse modulus of
`ϖ^lam` times the Haar mass of `leviIntegralSet F k K`. -/
theorem exists_mirabolicMeasure_torus (k : ℕ) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    [MeasurableSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier))]
    [BorelSpace (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier))] :
    ∃ ν : Measure (QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent (k + 1) F.Carrier)),
      IsFiniteMeasureOnCompacts ν ∧
      (∀ g : mirabolic (k + 1) F.Carrier,
        MeasurePreserving (QuotientIntegration.rightTranslate _ g) ν ν) ∧
      (∀ J : OpenSubgroup (mirabolic (k + 1) F.Carrier),
        IsCompact (J : Set (mirabolic (k + 1) F.Carrier)) →
        0 < ν (compactOpenQuotientOrbit _ J) ∧ ν (compactOpenQuotientOrbit _ J) < ⊤) ∧
      ∀ (K : OpenSubgroup (mirabolic (k + 1) F.Carrier)) (lam : Fin (k + 1) → ℤ),
        letI := borel (Langlands.GeneralLinear (k + 1) F.Carrier)
        letI : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
        ENNReal.ofReal (QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam) *
            generalLinearHaar F.Carrier k (leviIntegralSet F k K) ≤
          ν (compactOpenQuotientOrbit _ (conjSub (torusElement F ϖ k lam) K)) := by
  let T := F.canonicalTopologicalData
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear.upperUnipotent (k + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear.upperUnipotent (k + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (GeneralLinear.upperUnipotent (k + 1) F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (GeneralLinear.upperUnipotent (k + 1) F.Carrier)) := ⟨rfl⟩
  have hμ := RankinSelberg.unipotentQuotientHaar_isCompatible F.Carrier k
  let μ := RankinSelberg.unipotentQuotientHaar F.Carrier k
  let e := (MirabolicQuotient.quotientHomeomorph (n := k + 1) (F := F.Carrier)).symm
  have hinv : ∀ g : mirabolic (k + 1) F.Carrier,
      MeasurePreserving (QuotientIntegration.rightTranslate _ g) (μ.map e) (μ.map e) := by
    intro g
    refine ⟨(QuotientIntegration.rightTranslate _ g).continuous.measurable, ?_⟩
    have hcomm : (QuotientIntegration.rightTranslate (Mirabolic.upperUnipotent (k + 1) F.Carrier) g) ∘ e =
        e ∘ QuotientIntegration.rightTranslate (GeneralLinear.upperUnipotent (k + 1) F.Carrier)
          (Mirabolic.projection g) :=
      funext fun q => MirabolicQuotient.rightTranslate_quotientHomeomorph_symm g q
    rw [Measure.map_map (QuotientIntegration.rightTranslate _ g).continuous.measurable
      e.continuous.measurable, hcomm,
      ← Measure.map_map e.continuous.measurable
        (QuotientIntegration.rightTranslate _ _).continuous.measurable,
      (hμ.right_invariant (Mirabolic.projection g)).map_eq]
  refine ⟨μ.map e, Measure.IsFiniteMeasureOnCompacts.map μ e, hinv, fun J hJ => ?_,
    fun K lam => ?_⟩
  · have hm := (QuotientIntegration.isOpen_compactOpenQuotientOrbit
      (Mirabolic.upperUnipotent (k + 1) F.Carrier) J).measurableSet
    rw [Measure.map_apply e.continuous.measurable hm]
    have hpre : e ⁻¹' compactOpenQuotientOrbit _ J = e.symm '' compactOpenQuotientOrbit _ J :=
      (congrFun e.image_symm _).symm
    rw [hpre]
    exact hμ.measure_pos_lt_top
      ((QuotientIntegration.isCompact_compactOpenQuotientOrbit _ J hJ).image e.symm.continuous)
      (e.symm.isOpenMap _ (QuotientIntegration.isOpen_compactOpenQuotientOrbit _ J))
      ((QuotientIntegration.compactOpenQuotientOrbit_nonempty _ J).image _)
  · let t := torusElement F ϖ k lam
    let O := compactOpenQuotientOrbit (Mirabolic.upperUnipotent (k + 1) F.Carrier)
      (conjSub t K)
    let R := QuotientIntegration.rightTranslate (Mirabolic.upperUnipotent (k + 1) F.Carrier) t⁻¹
    have hR := hinv t⁻¹
    calc ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) *
          generalLinearHaar F.Carrier k (leviIntegralSet F k K)
        ≤ μ (e ⁻¹' (R ⁻¹' O)) := by
          apply density_mul_haar_le_quotientMeasure F T k ϖ hϖ lam
            (leviIntegralSet F k K) (isOpen_leviIntegralSet F k K).measurableSet
            Set.inter_subset_right
          intro x hx
          refine ⟨t * Mirabolic.levi x * t⁻¹, conj_mem_conjSub t _ hx.1, ?_⟩
          change Quotient.mk _ (t * Mirabolic.levi x * t⁻¹) =
            Quotient.mk _ (Mirabolic.levi (Iwasawa.torus ϖ lam * x) * t⁻¹)
          rw [map_mul]
          rfl
      _ ≤ (μ.map e) (R ⁻¹' O) := Measure.le_map_apply e.continuous.measurable.aemeasurable _
      _ ≤ ((μ.map e).map R) O := Measure.le_map_apply hR.measurable.aemeasurable O
      _ = (μ.map e) O := by rw [hR.map_eq]

/-- Distinct torus elements lie in distinct cells `N t K` for `K ≤ GL_(k+2)(O) ∩ P`. -/
theorem torusElement_ne (k : ℕ) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    {lam lam' : Fin (k + 1) → ℤ} (hne : lam ≠ lam')
    (h : Mirabolic.upperUnipotent (k + 1) F.Carrier)
    (κ : mirabolic (k + 1) F.Carrier) (hκ : κ ∈ mirabolicIntegral F k) :
    torusElement F ϖ k lam ≠ (h : mirabolic (k + 1) F.Carrier) * torusElement F ϖ k lam' * κ := by
  intro he
  have he' := congrArg Subtype.val he
  simp only [Subgroup.coe_mul, torusElement_val] at he'
  have hexp := Iwasawa.iwasawa_exponent_unique hϖ
    (u := 1) (k := 1) (one_mem _) h.property (one_mem _) ((mem_mirabolicIntegral F κ).1 hκ)
    (by rw [one_mul, mul_one]; exact he')
  apply hne
  have := congrArg Fin.init hexp
  simpa only [Fin.init_snoc] using this

/-- **Torus-lattice square-summability of unitary Whittaker functions** (Jacquet–Shalika I,
(1.3.1), in torus form). For an irreducible admissible unitarizable representation `ρ` of
`GL_(k+2)(F)`, a standard Whittaker functional `ℓ`, a vector `v` and a uniformizing `ϖ`, the
family `δ(ϖ^lam)⁻¹ ‖ℓ(ρ(diag(ϖ^lam, 1)) v)‖²` is summable over `lam ∈ ℤ^(k+1)`, `δ` the
upper-Borel modulus character. -/
theorem summable_density_mul_norm_sq (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (hadm : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) (hunit : IsUnitarizable ρ)
    (ℓ : glFunctionals ψ (k + 1) ρ) (v : V) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ) :
    Summable (fun lam : Fin (k + 1) → ℤ =>
      QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam *
        ‖ℓ.val (ρ (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2) := by
  by_cases hℓ : ℓ.val = 0
  · simp only [hℓ, LinearMap.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    exact summable_zero
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent (k + 1) F.Carrier)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
    (Mirabolic.upperUnipotent (k + 1) F.Carrier)) := ⟨rfl⟩
  -- a compact open subgroup of `P` fixing `v`
  obtain ⟨H, hH⟩ := hadm.1 v
  let K : OpenSubgroup (mirabolic (k + 1) F.Carrier) :=
    H.comap (mirabolic (k + 1) F.Carrier).subtype continuous_subtype_val ⊓ mirabolicIntegral F k
  have hKcpt : IsCompact (K : Set (mirabolic (k + 1) F.Carrier)) :=
    (isCompact_mirabolicIntegral F k).of_isClosed_subset K.isClosed
      (fun x hx => (inf_le_right : K ≤ mirabolicIntegral F k) hx)
  have hvK : ∀ g ∈ K, ρ g.val v = v := by
    intro g hg
    have h := hH
    rw [fixedVectors, Representation.mem_invariants] at h
    exact h ⟨g.val, (inf_le_left : K ≤ _) hg⟩
  obtain ⟨ν, hfin, hinv, hmass, hcell⟩ := exists_mirabolicMeasure_torus F k ϖ hϖ
  obtain ⟨C, hC⟩ := padicCellBound F (k + 1) ψ ρ hadm hirr hunit ℓ hℓ ν hfin hinv hmass v K
    hKcpt hvK
  -- the Haar mass of the Levi-integral set is positive and finite
  let : MeasurableSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (k + 1) F.Carrier) := ⟨rfl⟩
  set c := generalLinearHaar F.Carrier k (leviIntegralSet F k K) with hc
  have hc0 : 0 < c :=
    (isOpen_leviIntegralSet F k K).measure_pos _ ⟨1, one_mem_leviIntegralSet F k K⟩
  have hctop : c < ⊤ := by
    refine lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_
    have hcpt : IsCompact (Conductor.integralSubgroup
        (ValuativeRel.valuation F.Carrier).integer k : Set (Langlands.GeneralLinear (k + 1) F.Carrier)) := by
      have h := Conductor.isCompact_levelOpenSubgroup F.Carrier k 0
      change IsCompact ((Conductor.levelSubgroup F.Carrier k 0 :
        Subgroup (Langlands.GeneralLinear (k + 1) F.Carrier)) :
          Set (Langlands.GeneralLinear (k + 1) F.Carrier)) at h
      rwa [Conductor.levelSubgroup_zero] at h
    exact hcpt.measure_lt_top
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hctop.ne
  -- an injection of the exponent lattice into `ℕ`
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat (Fin (k + 1) → ℤ)
  let g : ℕ → mirabolic (k + 1) F.Carrier := fun i =>
    torusElement F ϖ k (Function.invFun ι i)
  have hg : ∀ lam, g (ι lam) = torusElement F ϖ k lam := fun lam => by
    simp only [g, Function.leftInverse_invFun hι lam]
  refine summable_of_sum_le (c := C / c.toReal)
    (fun lam => mul_nonneg (QuotientTorusEnvelope.density_pos F _ ϖ lam).le (sq_nonneg _))
    (fun u => ?_)
  rw [le_div_iff₀ hcr, Finset.sum_mul]
  have hb := hC (u.map ⟨ι, hι⟩) g (by
    intro i hi j hj hij h κ hκ
    obtain ⟨lam, -, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨lam', -, rfl⟩ := Finset.mem_map.1 hj
    simp only [Function.Embedding.coeFn_mk] at hij ⊢
    rw [hg, hg]
    exact torusElement_ne F k ϖ hϖ (fun h' => hij (by rw [h'])) h κ
      ((inf_le_right : K ≤ mirabolicIntegral F k) hκ))
  rw [Finset.sum_map] at hb
  refine le_trans (Finset.sum_le_sum fun lam _ => ?_) hb
  simp only [Function.Embedding.coeFn_mk, hg, torusElement_val]
  have hfin' := (hmass _ (isCompact_conjSub (torusElement F ϖ k lam) _ hKcpt)).2
  have hle : QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam * c.toReal ≤
      (ν (compactOpenQuotientOrbit _ (conjSub (torusElement F ϖ k lam) K))).toReal := by
    have h := hcell K lam
    rw [← hc, ← ENNReal.ofReal_toReal hctop.ne, ← ENNReal.ofReal_mul
      (QuotientTorusEnvelope.density_pos F _ ϖ lam).le] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hfin'.ne).1 h
  calc QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam *
        ‖ℓ.val (ρ (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2 * c.toReal
      = QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam * c.toReal *
        ‖ℓ.val (ρ (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (sq_nonneg _)

end MirabolicMeasure

end Langlands.RankinSelberg.UnitaryGeneric
