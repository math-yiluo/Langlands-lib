import Langlands.Representation.Derivative.HighestDerivativeChain
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentInitialTruncationOrderProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Classification.MirabolicDerivativeContragredient
import Langlands.Representation.Aubert.ZelevinskyHighestDerivative
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof

/-!
# Derivative chains inside products of segment socles

Let `c` be a precedence-ordered product `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` of segment socles on
`GL_n`, with multisegment `a`. Write `k = ∑ rank Δ_i`.

* `segmentProduct_step`: the order-`k` derivative of `c` is the product for `a⁻`,
  higher derivatives vanish, and every nonzero subrepresentation of `c` has a nonzero
  order-`k` derivative (Zelevinsky 1980, Theorem 6.2 and §6.6).
* `not_derivativeChain_of_quotient`: if `V ⊆ c` and `K ⊆ V` is nonzero, the chain of
  derivatives of `V / K` along `levelSequence a` dies.
* `derivativeChain_of_pairing`: if a nonzero `A ⊆ c` pairs invariantly with `B`,
  nondegenerately in `A`, then the chain of derivatives of `B` along `levelSequence a`
  survives (iterating Bernstein–Zelevinsky 1977, Proposition 3.8).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

open scoped NNReal

namespace Langlands.Derivative.HighestDerivativeChain

open GeneralLinear HarmonicAnalysis PadicField.TopologicalData Classification
open Classification.MirabolicDerivativeContragredient

universe uF uV

section Datum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The total rank of the multisegment of a datum is the sum of the segment ranks. -/
theorem multisegment_map_rank_sum {n : ℕ} (c : T.SegmentProductDatum.{uV, uF} n) :
    (c.multisegment.map Segment.rank).sum = ∑ i, (c.segments i).rank := by
  simp [SegmentProductDatum.multisegment, List.sum_ofFn]

/-- A datum with a nonempty multisegment lives on a group of positive rank. -/
theorem pos_of_multisegment_ne_zero {n : ℕ} (c : T.SegmentProductDatum.{uV, uF} n)
    (h : c.multisegment ≠ 0) : 0 < n := by
  obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨i, rfl⟩ : Δ ∈ Set.range c.segments := List.mem_ofFn.mp hΔ
  rw [← c.degree_sum]
  exact lt_of_lt_of_le (c.segments i).degree_pos
    (Finset.single_le_sum (f := fun j => (c.segments j).degree) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i))

/-- A datum with an empty multisegment lives on `GL_0`. -/
theorem eq_zero_of_multisegment_eq_zero {n : ℕ} (c : T.SegmentProductDatum.{uV, uF} n)
    (h : c.multisegment = 0) : n = 0 := by
  have hl : c.length = 0 := by
    have := congrArg Multiset.card h
    simpa [SegmentProductDatum.multisegment] using this
  rw [← c.degree_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact absurd i.2 (by omega)

end Datum

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- One derivative step for a precedence-ordered product of segment socles. For
`k = ∑ rank Δ_i`, the order-`k` derivative of the product is the product for the
truncated multisegment, all higher derivatives vanish, and every nonzero subrepresentation
has a nonzero order-`k` derivative. -/
theorem segmentProduct_step (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : c.IsPrecedenceOrdered) (hs : c.HasSegmentSocles) (hc : c.multisegment ≠ 0)
    (k : ℕ) (hkdef : k = (c.multisegment.map Segment.rank).sum) :
    letI := T.topology
    ∃ (hk : 0 < k ∧ k ≤ n) (c' : T.SegmentProductDatum.{max uF uV, uF} (n - k)),
      c'.IsPrecedenceOrdered ∧ c'.HasSegmentSocles ∧
      c'.multisegment = c.multisegment.filterMap Segment.dropLast ∧
      Nonempty ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk.2).obj c.induced ≅
        c'.induced) ∧
      (∀ (j : ℕ) (hj : j ≤ n), k < j →
        Subsingleton ((generalLinearDerivative.{uF, max uF uV} T ψ n j hj).obj c.induced)) ∧
      ∀ (V : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (f : V ⟶ c.induced),
        Function.Injective (SmoothRep.hom f) → Nontrivial V →
          Nontrivial ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk.2).obj V) := by
  let := T.topology
  have hn := pos_of_multisegment_ne_zero c hc
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  rw [multisegment_map_rank_sum] at hkdef
  subst hkdef
  have hk : ∑ i, (c.segments i).rank ≤ M + 1 :=
    Aubert.ZelevinskyHighestDerivative.sum_rank_le F T c
  have hkpos : 0 < ∑ i, (c.segments i).rank :=
    Aubert.ZelevinskyHighestDerivative.sum_rank_pos F T hn c
  have hk' : 0 < ∑ i, (c.segments i).rank ∧ ∑ i, (c.segments i).rank ≤ M + 1 :=
    ⟨hkpos, hk⟩
  obtain ⟨hvan, ⟨c', hlist, hs', ⟨e⟩⟩, -⟩ :=
    segmentSocleProductHighestDerivative.{uF, max uF uV} F T ψ (M + 1) c hs _ hk rfl
  have hlist' : List.ofFn c'.segments = Segment.dropLastList (List.ofFn c.segments) :=
    hlist.trans (Segment.filterMap_eq_dropLastList _)
  have ho' : c'.IsPrecedenceOrdered := by
    have h₁ := (segmentInitialTruncationOrder.{uF, max uF uV} F T
      (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T)).2 _
      ((T.isPrecedenceOrdered_iff_list c.segments).mp ho)
    rw [← hlist'] at h₁
    exact (T.isPrecedenceOrdered_iff_list c'.segments).mpr h₁
  have hms : c'.multisegment = c.multisegment.filterMap Segment.dropLast := by
    unfold SegmentProductDatum.multisegment
    rw [hlist', Multiset.filterMap_coe]
    rfl
  -- Homogeneity of the restricted product (Ze80 Thm 6.2).
  have hsep := precedenceOrdered_endpointSeparated.{uF, max uF uV} F T
    (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T) c.segments ho
  have hhom : IsHomogeneous T ψ ((generalLinearRestriction T M).obj c.induced) :=
    (isGeneralLinearHomogeneous_iff T ψ c.induced).mp
      (segmentSocleProductHomogeneity.{uF, max uF uV} F T ψ M c hs hsep)
  have hlevX : level T ψ ((generalLinearRestriction T M).obj c.induced) =
      ∑ i, (c.segments i).rank := by
    rw [level_eq_iff T ψ hkpos]
    refine ⟨hk, ?_, ?_⟩
    · rw [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ hk',
        LevelCalculus.nontrivial_iff_of_iso e]
      exact segmentSocleProduct_nontrivial F T c' hs'
    · intro m hkm hm hnz
      rw [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ
        ⟨by omega, hm⟩] at hnz
      exact (not_nontrivial_iff_subsingleton.mpr (hvan m hm hkm)) hnz
  refine ⟨hk', c', ho', hs', hms, ⟨e⟩, hvan, ?_⟩
  intro V f hf hV
  have hfR : Function.Injective (SmoothRep.hom ((generalLinearRestriction T M).map f)) :=
    LevelCalculus.map_injective_of_exact (generalLinearRestriction_mapsShortExact F T M) f hf
  have hVR : Nontrivial ((generalLinearRestriction T M).obj V) := hV
  have hlev := LevelCalculus.level_eq_of_isHomogeneous T ψ hhom _ hfR hVR
  have hVk := ((level_eq_iff T ψ hkpos _).mp (hlev.trans hlevX)).2.1
  rwa [Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ hk']
    at hVk

/-- Quotients by nonzero subrepresentations lose the derivative chain. If `V` embeds in a
precedence-ordered product `c` of segment socles and `K → V → W` is short exact with
`K` nonzero, then the derivative chain of `W` along `levelSequence c.multisegment`
fails. -/
theorem not_derivativeChain_of_quotient
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (n : ℕ) (c : T.SegmentProductDatum.{max uF uV, uF} n),
      c.IsPrecedenceOrdered → c.HasSegmentSocles →
      ∀ {K V W : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
        (f : V ⟶ c.induced), Function.Injective (SmoothRep.hom f) →
        ∀ (i : K ⟶ V) (q : V ⟶ W), LevelCalculus.IsShortExact i q → Nontrivial K →
          ¬ DerivativeChain T ψ (levelSequence c.multisegment) n W := by
  let := T.topology
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c ho hs K V W f hf i q hiq hK
  by_cases hc : c.multisegment = 0
  · rw [hc, levelSequence_zero, derivativeChain_nil, not_nontrivial_iff_subsingleton]
    have hn0 := eq_zero_of_multisegment_eq_zero c hc
    subst hn0
    have h1 := SegmentProductOrderedAssembly.finrank_zeroDatum c
    have hfin : FiniteDimensional ℂ c.induced := Module.finite_of_finrank_eq_succ h1
    have hVfin : FiniteDimensional ℂ V :=
      Module.Finite.of_injective (SmoothRep.hom f).toLinearMap hf
    have hKfin : FiniteDimensional ℂ K :=
      Module.Finite.of_injective (SmoothRep.hom i).toLinearMap hiq.injective
    have hV1 : Module.finrank ℂ V ≤ 1 :=
      h1 ▸ LinearMap.finrank_le_finrank_of_injective (f := (SmoothRep.hom f).toLinearMap) hf
    have hK1 : 0 < Module.finrank ℂ K := Module.finrank_pos
    have hKV : Module.finrank ℂ K ≤ Module.finrank ℂ V :=
      LinearMap.finrank_le_finrank_of_injective (f := (SmoothRep.hom i).toLinearMap)
        hiq.injective
    have hrange : LinearMap.range (SmoothRep.hom i).toLinearMap = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hiq.injective]
      omega
    have hzero : ∀ w : W, w = 0 := by
      intro w
      obtain ⟨v, rfl⟩ := hiq.surjective w
      have hv : v ∈ LinearMap.ker (SmoothRep.hom q).toLinearMap := by
        rw [← hiq.exact, hrange]
        exact Submodule.mem_top
      exact hv
    exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  · obtain ⟨hk, c', ho', hs', hms, ⟨e⟩, -, hnt⟩ :=
      segmentProduct_step F T ψ c ho hs hc _ rfl
    rw [levelSequence_eq_cons hc, ← hms, derivativeChain_cons]
    rintro ⟨_, hch⟩
    have hex := generalLinearDerivativeExactness.{uF, max uF uV} F T ψ n _ hk.2
    have hs2 := LevelCalculus.isShortExact_map hex hiq
    have hfD : Function.Injective (SmoothRep.hom
        ((generalLinearDerivative.{uF, max uF uV} T ψ n _ hk.2).map f ≫ e.hom)) :=
      (LevelCalculus.iso_hom_injective e).comp (LevelCalculus.map_injective_of_exact hex f hf)
    have hKD := hnt K (i ≫ f) (hf.comp hiq.injective) hK
    exact ih _ (by omega) c' ho' hs' _ hfD _ _ hs2 hKD hch

/-- Invariant pairings propagate the derivative chain. If a nonzero `A` embeds in a
precedence-ordered product `c` of segment socles and pairs invariantly with `B`,
nondegenerately in `A`, then the derivative chain of `B` along
`levelSequence c.multisegment` holds. -/
theorem derivativeChain_of_pairing
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (n : ℕ) (c : T.SegmentProductDatum.{max uF uV, uF} n),
      c.IsPrecedenceOrdered → c.HasSegmentSocles →
      ∀ {A B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
        (f : A ⟶ c.induced), Function.Injective (SmoothRep.hom f) → Nontrivial A →
        ∀ γ : InvariantBilinear.forms A.representation B.representation (fun _ => (1 : ℂ)),
          (∀ a : A, (∀ b : B, γ.val a b = 0) → a = 0) →
          DerivativeChain T ψ (levelSequence c.multisegment) n B := by
  let := T.topology
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c ho hs A B f hf hA γ hγ
  by_cases hc : c.multisegment = 0
  · rw [hc, levelSequence_zero, derivativeChain_nil]
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨b, hb⟩ : ∃ b, γ.val a b ≠ 0 := by
      by_contra! H
      exact ha (hγ a H)
    exact ⟨b, 0, fun h => hb (by rw [h, map_zero])⟩
  · obtain ⟨k, hkdef⟩ : ∃ k, k = (c.multisegment.map Segment.rank).sum := ⟨_, rfl⟩
    obtain ⟨hk, c', ho', hs', hms, ⟨e⟩, hvan, hnt⟩ :=
      segmentProduct_step F T ψ c ho hs hc k hkdef
    have hn := pos_of_multisegment_ne_zero c hc
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [levelSequence_eq_cons hc, ← hkdef, ← hms,
      ← derivativeChain_twist_iff F T ψ 1 _ B, derivativeChain_cons]
    refine ⟨hk, ?_⟩
    let B₁ := B.twist (T.determinantPowerCharacter (N + 1) 1)
      (T.isOpen_ker_determinantPowerCharacter (N + 1) 1)
    -- The `|det|`-covariant pairing of the mirabolic restrictions.
    let β : InvariantBilinear.forms ((generalLinearRestriction T N).obj A).representation
        ((generalLinearRestriction T N).obj B₁).representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)) :=
      ⟨γ.val, fun g a b => by
        change γ.val (A.representation g.val a)
            ((T.determinantPowerCharacter (N + 1) 1 g.val : ℂ) • B.representation g.val b) = _
        rw [map_smul, smul_eq_mul, γ.property g.val a b]
        simp only [one_mul, coe_realPowerCharacter, Real.rpow_one]
        rfl⟩
    have hDex : ∀ (j : ℕ) (hj : j ≤ N + 1), Mirabolic.MapsShortExactIntertwiners
        (generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) j hj) :=
      fun j hj => generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (N + 1) j hj
    have hAnt : Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj
        ((generalLinearRestriction T N).obj A)) := by
      rw [mirabolicDerivativeOfOrder_restriction]
      exact hnt A f hf hA
    have hAvan : ∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
        Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj
          ((generalLinearRestriction T N).obj A)) := by
      intro j hj hkj
      rw [mirabolicDerivativeOfOrder_restriction]
      have := hvan j hj.2 hkj
      exact LevelCalculus.subsingleton_of_injective _
        (LevelCalculus.map_injective_of_exact (hDex j hj.2) f hf)
    have key : ∃ γ' : InvariantBilinear.forms
        ((generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk.2).obj A).representation
        ((generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk.2).obj B₁).representation
        (fun _ => (1 : ℂ)),
        ∀ v, (∀ w, γ'.val v w = 0) → v = 0 := by
      rw [← mirabolicDerivativeOfOrder_restriction ψ N k hk A,
        ← mirabolicDerivativeOfOrder_restriction ψ N k hk B₁]
      exact mirabolicHighestDerivativePairing.{uF, max uF uV, max uF uV} F T ψ N _ _ k hk
        hAnt hAvan β (fun a ha => hγ a ha)
    obtain ⟨γ', hγ'⟩ := key
    have hfD : Function.Injective (SmoothRep.hom
        ((generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) k hk.2).map f ≫ e.hom)) :=
      (LevelCalculus.iso_hom_injective e).comp
        (LevelCalculus.map_injective_of_exact (hDex k hk.2) f hf)
    exact ih _ (by omega) c' ho' hs' _ hfD (hnt A f hf hA) γ' hγ'

end Langlands.Derivative.HighestDerivativeChain
