import Langlands.Representation.RankinSelberg.CorankOneEntireSliceStatement
import Langlands.Representation.RankinSelberg.IntegralDeterminant
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Analysis.Analytic.Constructions

/-!
# Finite evaluation of corank-one determinant slices with common compact support

JPSS (1983), Section 4.5, printed pages 408–409. Suppose a family of standard
Whittaker functions on `GL_(r+2)` is right invariant under one open subgroup and
depends analytically on a parameter at each point, and suppose the restrictions to
one determinant slice of all corank-one integrands against a fixed coefficient
on `GL_(r+1)` vanish outside one compact set. Then one compact open subgroup `J`
of `GL_(r+1)` leaves every integrand and the slice invariant, finitely many
pairwise disjoint `J`-orbits carry all the restricted integrands, and each slice
integral is a finite sum of orbit masses times point values, with orbits and
masses independent of the parameter. Hence every slice is integrable and its
coefficient is analytic. The common compact support is a hypothesis here.
-/

noncomputable section

namespace Langlands.RankinSelberg.CommonLevel

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-! ## Right orbits of a subgroup on the left-unipotent quotient -/

section Orbits

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)

/-- The orbit of a coset `q` under right translation by the elements of `J`. -/
def rightTranslateOrbit (J : Subgroup G) (q : LeftQuotient H) : Set (LeftQuotient H) :=
  (fun k : G => rightTranslate H k q) '' (J : Set G)

theorem self_mem_rightTranslateOrbit (J : Subgroup G) (q : LeftQuotient H) :
    q ∈ rightTranslateOrbit H J q :=
  ⟨1, J.one_mem, rightTranslate_one H q⟩

theorem rightTranslateOrbit_eq_of_mem {J : Subgroup G} {q q' : LeftQuotient H}
    (h : q' ∈ rightTranslateOrbit H J q) :
    rightTranslateOrbit H J q' = rightTranslateOrbit H J q := by
  obtain ⟨k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k * k', J.mul_mem hk hk', (rightTranslate_mul H k k' q).symm⟩
  · rintro ⟨k', hk', rfl⟩
    refine ⟨k⁻¹ * k', J.mul_mem (J.inv_mem hk) hk', ?_⟩
    change rightTranslate H (k⁻¹ * k') (rightTranslate H k q) = rightTranslate H k' q
    rw [rightTranslate_mul, mul_inv_cancel_left]

/-- Two right orbits are equal or disjoint. -/
theorem disjoint_rightTranslateOrbit {J : Subgroup G} {q q' : LeftQuotient H}
    (h : rightTranslateOrbit H J q ≠ rightTranslateOrbit H J q') :
    Disjoint (rightTranslateOrbit H J q) (rightTranslateOrbit H J q') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact h ((rightTranslateOrbit_eq_of_mem H hx).symm.trans (rightTranslateOrbit_eq_of_mem H hx'))

theorem rightTranslateOrbit_mk (J : Subgroup G) (g : G) :
    rightTranslateOrbit H J (Quotient.mk _ g) =
      leftQuotientMap H '' ((fun k => g * k) '' (J : Set G)) := by
  rw [rightTranslateOrbit, Set.image_image]
  rfl

theorem isOpen_rightTranslateOrbit {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (q : LeftQuotient H) : IsOpen (rightTranslateOrbit H J q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [rightTranslateOrbit_mk]
    exact (leftQuotient_isOpenQuotientMap H).isOpenMap _ (isOpenMap_mul_left g _ hJ)

theorem isCompact_rightTranslateOrbit {J : Subgroup G} (hJ : IsCompact (J : Set G))
    (q : LeftQuotient H) : IsCompact (rightTranslateOrbit H J q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [rightTranslateOrbit_mk, Set.image_image]
    exact hJ.image ((leftQuotient_isOpenQuotientMap H).continuous.comp
      (continuous_const.mul continuous_id))

/-- A compact set of cosets meets only finitely many right orbits of an open subgroup:
it is covered by pairwise disjoint orbits of finitely many of its own points. -/
theorem exists_finset_rightTranslateOrbit_cover {J : Subgroup G} (hJ : IsOpen (J : Set G))
    {C : Set (LeftQuotient H)} (hC : IsCompact C) :
    ∃ u : Finset (LeftQuotient H), (∀ q ∈ u, q ∈ C) ∧
      (u : Set (LeftQuotient H)).PairwiseDisjoint (rightTranslateOrbit H J) ∧
      C ⊆ ⋃ q ∈ u, rightTranslateOrbit H J q := by
  classical
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover (rightTranslateOrbit H J)
    (fun q _ => (isOpen_rightTranslateOrbit H hJ q).mem_nhds
      (self_mem_rightTranslateOrbit H J q))
  obtain ⟨u, hut, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (t : Set (LeftQuotient H)) (t.image (rightTranslateOrbit H J)) (by
      intro O hO
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hO
      exact ⟨q, hq, rfl⟩)
  refine ⟨u, fun q hq => htC q (hut hq), ?_, ?_⟩
  · intro q hq q' hq' hne
    exact disjoint_rightTranslateOrbit H fun h => hne (hinj hq hq' h)
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hCt hx)
    have hmem : rightTranslateOrbit H J q ∈ u.image (rightTranslateOrbit H J) := by
      rw [himg]
      exact Finset.mem_image_of_mem _ hq
    obtain ⟨q', hq', heq⟩ := Finset.mem_image.mp hmem
    exact Set.mem_iUnion₂.mpr ⟨q', hq', heq ▸ hxq⟩

variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- Finite orbit decomposition of a restricted integral. Let `J` be a compact open
subgroup preserving the measurable set `S`, and `f` a right `J`-invariant function.
If the points of `S` where `f` does not vanish lie in finitely many pairwise disjoint
`J`-orbits of points of `S`, then `f` is integrable on `S` and its restricted integral
is the sum of the orbit masses times the values of `f` at the chosen points. -/
theorem integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    {J : Subgroup G} (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G))
    {S : Set (LeftQuotient H)} (hS : MeasurableSet S)
    (hSJ : ∀ q ∈ S, ∀ k ∈ J, rightTranslate H k q ∈ S)
    (u : Finset (LeftQuotient H)) (huS : ∀ q ∈ u, q ∈ S)
    (hdisj : (u : Set (LeftQuotient H)).PairwiseDisjoint (rightTranslateOrbit H J))
    (f : LeftQuotient H → ℂ) (hfJ : ∀ q, ∀ k ∈ J, f (rightTranslate H k q) = f q)
    (hsupp : ∀ q ∈ S, f q ≠ 0 → q ∈ ⋃ q' ∈ u, rightTranslateOrbit H J q') :
    IntegrableOn f S ν ∧
      ∫ q in S, f q ∂ν = ∑ q ∈ u, (ν.real (rightTranslateOrbit H J q) : ℂ) * f q := by
  have hconst : ∀ q, ∀ x ∈ rightTranslateOrbit H J q, f x = f q := by
    rintro q x ⟨k, hk, rfl⟩
    exact hfJ q k hk
  have horbS : ∀ q ∈ u, rightTranslateOrbit H J q ⊆ S := by
    rintro q hq x ⟨k, hk, rfl⟩
    exact hSJ q (huS q hq) k hk
  have hmeas : ∀ q, MeasurableSet (rightTranslateOrbit H J q) := fun q =>
    (isOpen_rightTranslateOrbit H hJo q).measurableSet
  have hfin : ∀ q, ν (rightTranslateOrbit H J q) ≠ ⊤ := fun q =>
    (isCompact_rightTranslateOrbit H hJc q).measure_lt_top.ne
  have horbInt : ∀ q, IntegrableOn f (rightTranslateOrbit H J q) ν := by
    intro q
    rw [integrableOn_congr_fun (hconst q) (hmeas q)]
    exact integrableOn_const (hfin q)
  have hind : ∀ x, S.indicator f x = ∑ q ∈ u, (rightTranslateOrbit H J q).indicator f x := by
    intro x
    by_cases hx : ∃ q ∈ u, x ∈ rightTranslateOrbit H J q
    · obtain ⟨q, hq, hxq⟩ := hx
      rw [Finset.sum_eq_single q, Set.indicator_of_mem hxq,
        Set.indicator_of_mem (horbS q hq hxq)]
      · intro q' hq' hne
        apply Set.indicator_of_notMem
        intro hxq'
        exact Set.disjoint_left.mp (hdisj (Finset.mem_coe.2 hq') (Finset.mem_coe.2 hq) hne)
          hxq' hxq
      · intro hq'
        exact absurd hq hq'
    · push Not at hx
      rw [Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (hx q hq) f]
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        by_contra hne
        obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hsupp x hxS hne)
        exact hx q hq hxq
      · exact Set.indicator_of_notMem hxS f
  have hterm : ∀ q ∈ u, Integrable ((rightTranslateOrbit H J q).indicator f) ν := fun q _ =>
    (integrable_indicator_iff (hmeas q)).2 (horbInt q)
  have hint : Integrable (S.indicator f) ν := by
    rw [show S.indicator f = fun x => ∑ q ∈ u, (rightTranslateOrbit H J q).indicator f x from
      funext hind]
    exact integrable_finsetSum u hterm
  refine ⟨(integrable_indicator_iff hS).1 hint, ?_⟩
  rw [← integral_indicator hS, show S.indicator f =
      fun x => ∑ q ∈ u, (rightTranslateOrbit H J q).indicator f x from funext hind,
    integral_finsetSum u hterm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator (hmeas q), setIntegral_congr_fun (hmeas q) (hconst q),
    setIntegral_const, Complex.real_smul]

end Orbits

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An integral invertible matrix has determinant of order zero. -/
theorem ord_det_of_mem_integralSubgroup {r : ℕ}
    {k : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ Conductor.integralSubgroup T.Integers r) :
    T.ord (GeneralLinear.determinant k : F.Carrier) = 0 := by
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have h : (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant k : F.Carrier)) =
      (T.residueCardinality : ℝ) ^ (-(0 : ℤ)) := by
    rw [← T.normalizedAbs_of_ne_zero (GeneralLinear.determinant k).ne_zero, neg_zero,
      zpow_zero]
    exact normalizedAbs_det_of_mem_integralSubgroup T hk
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' h)

/-- JPSS (1983), Section 4.5, printed pages 408–409, in the corank-one setting,
conditional on common compact support. Let `U` be a family of standard Whittaker
functions on `GL_(r+2)` right invariant under one open subgroup `K` and analytic in
the parameter at each point, and `Wprime` a fixed coefficient of a representation of
Whittaker type on `GL_(r+1)`. If on the slice `S_m` every corank-one integrand at
`s = 0` vanishes outside one compact set `C`, then each of these integrands is
integrable on `S_m` and the slice coefficient is analytic in the parameter. -/
theorem corank_slice_of_common_support (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient r F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : Measure (LeftUnipotentQuotient r F.Carrier))
      [IsFiniteMeasureOnCompacts ν]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
      IsOfWhittakerType r (inverseStandardCharacter ψ r) τ →
      ∀ (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
        (U : ℂ → WhittakerFunctions ψ (r + 1))
        (K : Subgroup (Langlands.GeneralLinear (r + 1 + 1) F.Carrier)),
        IsOpen (K : Set (Langlands.GeneralLinear (r + 1 + 1) F.Carrier)) →
        (∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1 + 1) F.Carrier) (k : K),
          (U u).val (g * k) = (U u).val g) →
        (∀ (g : Langlands.GeneralLinear (r + 1 + 1) F.Carrier) (u : ℂ),
          AnalyticAt ℂ (fun z => (U z).val g) u) →
        ∀ (m : ℤ) (C : Set (LeftUnipotentQuotient r F.Carrier)), IsCompact C →
          (∀ z : ℂ, Function.support ((determinantSlice T r m).indicator
            (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0)) ⊆ C) →
          (∀ u : ℂ,
            SliceIntegrableAt T ν
              (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U u) Wprime.val 0) m) ∧
          ∀ u : ℂ,
            AnalyticAt ℂ
              (fun z => sliceCoefficient T ν
                (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0) m) u := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient r F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
  intro ψ ν _ V _ _ τ hτ ℓ Wprime U K hKo hKinv hU m C hC hsupp
  let G := Langlands.GeneralLinear (r + 1) F.Carrier
  let N := upperUnipotent (r + 1) F.Carrier
  let S := determinantSlice T r m
  let f : ℂ → LeftUnipotentQuotient r F.Carrier → ℂ := fun z =>
    corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0
  have hCS : IsCompact (C ∩ S) := hC.inter_right (isClosed_determinantSlice T r m)
  have hsuppC : ∀ z, ∀ q ∈ S, f z q ≠ 0 → q ∈ C ∩ S := by
    intro z q hqS hne
    refine ⟨hsupp z ?_, hqS⟩
    rw [Function.mem_support, Set.indicator_of_mem hqS]
    exact hne
  -- One common right level.
  obtain ⟨v, rfl⟩ := modelMap_surjective τ ℓ Wprime
  obtain ⟨K1, hK1⟩ := hτ.1.1 v
  let J : Subgroup G := K1.toSubgroup ⊓ K.comap (rankInclusion 1) ⊓
    Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r
  have hKcont : Continuous (rankInclusion (R := F.Carrier) (n := r + 1) 1) :=
    (GeneralLinear.rankInclusionContinuous (R := F.Carrier) (n := r + 1) 1).continuous_toFun
  have hIo : IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r :
      Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact (Conductor.levelOpenSubgroup F.Carrier r 0).isOpen
  have hIc : IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r :
      Set G) := by
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier r 0
  have hJo : IsOpen (J : Set G) :=
    (K1.isOpen.inter (hKo.preimage hKcont)).inter hIo
  have hJc : IsCompact (J : Set G) :=
    hIc.of_isClosed_subset (J.isClosed_of_isOpen hJo) fun k hk => hk.2
  -- Invariance of the integrands and of the slice under the common level.
  have hfJ : ∀ z q, ∀ k ∈ J, f z (rightTranslate N k q) = f z q := by
    intro z q k hk
    induction q using Quotient.inductionOn with
    | h g =>
      change (U z).val (rankInclusion 1 (g * k)) * (modelMap τ ℓ v).val.val (g * k) *
          determinantWeight (normalizedAbsoluteValue T) (g * k) (0 - 1 / 2) =
        (U z).val (rankInclusion 1 g) * (modelMap τ ℓ v).val.val g *
          determinantWeight (normalizedAbsoluteValue T) g (0 - 1 / 2)
      have h1 : (U z).val (rankInclusion 1 (g * k)) = (U z).val (rankInclusion 1 g) := by
        rw [map_mul]
        exact hKinv z (rankInclusion 1 g) ⟨rankInclusion 1 k, hk.1.2⟩
      have h2 : (modelMap τ ℓ v).val.val (g * k) = (modelMap τ ℓ v).val.val g := by
        change ℓ.val (τ (g * k) v) = ℓ.val (τ g v)
        rw [map_mul, Module.End.mul_apply]
        congr 2
        exact (Representation.mem_invariants _ v).1 hK1 ⟨k, hk.1.1⟩
      have h3 : determinantWeight (normalizedAbsoluteValue T) (g * k) (0 - 1 / 2) =
          determinantWeight (normalizedAbsoluteValue T) g (0 - 1 / 2) := by
        unfold determinantWeight
        rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbsoluteValue_apply T
          (Matrix.det k.val), normalizedAbs_det_of_mem_integralSubgroup T hk.2, mul_one]
      rw [h1, h2, h3]
  have hSJ : ∀ q ∈ S, ∀ k ∈ J, rightTranslate N k q ∈ S := by
    intro q hq k hk
    rw [rightTranslate_mem_determinantSlice, ord_det_of_mem_integralSubgroup T hk.2, sub_zero]
    exact hq
  -- Finitely many disjoint orbits, chosen once for all parameters.
  obtain ⟨u, huC, hdisj, hcover⟩ := exists_finset_rightTranslateOrbit_cover N hJo hCS
  have hmain : ∀ z, IntegrableOn (f z) S ν ∧
      ∫ q in S, f z q ∂ν = ∑ q ∈ u, (ν.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    fun z => integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit N ν hJo hJc
      (measurableSet_determinantSlice T r m) hSJ u (fun q hq => (huC q hq).2) hdisj (f z)
      (hfJ z) fun q hq hne => hcover (hsuppC z q hq hne)
  refine ⟨fun z => (hmain z).1, fun z0 => ?_⟩
  have heq : (fun z => sliceCoefficient T ν
      (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) (modelMap τ ℓ v).val 0) m) =
      fun z => ∑ q ∈ u, (ν.real (rightTranslateOrbit N J q) : ℂ) * f z q :=
    funext fun z => (hmain z).2
  rw [heq]
  refine Finset.analyticAt_fun_sum _ fun q _ => analyticAt_const.mul ?_
  induction q using Quotient.inductionOn with
  | h g =>
    exact ((hU (rankInclusion 1 g) z0).mul analyticAt_const).mul analyticAt_const

end Padic

end Langlands.RankinSelberg.CommonLevel
