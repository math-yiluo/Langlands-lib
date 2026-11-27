import Langlands.Global.ArthurTruncationBruhatExpansion

/-! # The constant term of the full finite parabolic sum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Group.RelativeWeylIndexing Langlands.Aubert.General.RationalPointFamily
  AdelicGroupPoints EisensteinConstantTerm ArthurParabolicSpaces
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "B" => SimpleRoot i ν
local notation "W" => relativeWeylGroup i
local notation "roots" => rootSet i ν
local notation "p" => Standard.parabolicHom i ν
local notation "rad" => Standard.unipotentHom i ν

/-- The rational-coset series of one standard cutoff kernel. -/
def cutoffSeries (S : Finset B) (Tp : V T) (φ : A → ℂ) (x : A) : ℂ :=
  ∑' c : ParabolicRationalCosets F (p (roots S)), cutoffKernel hG hi D hK hρ (roots S) Tp φ
    (((c.out : rationalSubgroup F G) : A) * x)

include hG hi in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Every subset of the simple character labels is the image of a set of simple roots. -/
theorem exists_labelFinset (S : Finset (characterLattice T))
    (hS : S ∈ (simpleFinset ν hG hi).powerset) : ∃ R : Finset B, labelFinset R = S := by
  classical
  refine ⟨S.subtype (· ∈ simpleRelativeRoots i ν), ?_⟩
  ext a
  rw [← Finset.mem_coe, coe_labelFinset, mem_rootSet]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact Finset.mem_subtype.mp hb
  · intro ha
    have hroot := (mem_simpleFinset hG hi).mp ((Finset.mem_powerset.mp hS) ha)
    exact ⟨⟨a, hroot⟩, Finset.mem_subtype.mpr ha, rfl⟩

include hG hi in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
private theorem labelFinset_univ [Fintype B] : labelFinset (Finset.univ : Finset B) = simpleFinset ν hG hi := by
  ext a
  rw [← Finset.mem_coe, coe_labelFinset, mem_rootSet, mem_simpleFinset hG hi]
  constructor
  · rintro ⟨b, _, rfl⟩
    exact b.2
  · exact fun ha => ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

/-- Reindexing the truncation from character subsets to finite subsets of the root type. -/
theorem truncation_eq_sum_cutoffSeries [Fintype B] (Tp : V T) (φ : A → ℂ) (x : A) :
    truncation hG hi D hK hρ Tp φ x = ∑ S : Finset B,
      (-1 : ℂ) ^ (Fintype.card B - S.card) * cutoffSeries hG hi D hK hρ S Tp φ x := by
  classical
  unfold truncation
  symm
  refine Finset.sum_bij (fun S _ => labelFinset S) (fun S _ => labelFinset_mem_powerset hG hi S)
    (fun _ _ _ _ eq => Finset.map_injective _ eq) ?_ ?_
  · intro S hS
    obtain ⟨R, rfl⟩ := exists_labelFinset hG hi S hS
    exact ⟨R, Finset.mem_univ _, rfl⟩
  · intro S _
    rw [← labelFinset_univ hG hi, card_labelFinset, card_labelFinset]
    let summand (J : Set (characterLattice T)) :=
      (-1 : ℂ) ^ (Fintype.card B - S.card) *
        ∑' c : ParabolicRationalCosets F (p J), cutoffKernel hG hi D hK hρ J Tp φ
          (((c.out : rationalSubgroup F G) : A) * x)
    exact congrArg summand (coe_labelFinset S).symm

include hν in
/-- A single rational-coset series is integrable over each testing radical's compact quotient. -/
theorem cutoffSeries_integrable_radical (Q S : Finset B) (Tp : V T) (φ : A → ℂ)
    (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ) (x : A) :
    let U := SubgroupFunctor.range (rad (roots Q))
    letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set A) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (rad (roots Q))
    Integrable (fun v : AdelicSubgroupPoints.RationalQuotient F G U =>
      cutoffSeries hG hi D hK hρ S Tp φ ((v.out : AdelicSubgroupPoints.adelicPoints F G U).val * x))
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U) := by
  classical
  intro U
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set A) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (rad (roots Q))
  let X := AdelicSubgroupPoints.adelicPoints F G U
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G U
  let Z := AdelicSubgroupPoints.RationalQuotient F G U
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  have hU := (Standard.parabolicStructure i ν hG hi hν _ (rootSet_subset i ν Q)).2.2.1.1
  let : CompactSpace Z := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
    (rad (roots Q)) hU.smooth hU.connectedSpace hU.isUnipotent
  let : IsProbabilityMeasure m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let Φ := cutoffKernel hG hi D hK hρ (roots S) Tp φ
  let f (v : X) := cutoffSeries hG hi D hK hρ S Tp φ ((v : A) * x)
  have hm : Measurable Φ := cutoffKernel_measurable hG hi hν D hK hρ _ Tp φ hφ
  have hfm : Measurable f := by
    apply Measurable.tsum
    intro c
    exact hm.comp (continuous_const.mul (continuous_subtype_val.mul_const x)).measurable
  have hfinv (delta : Γ) (v : X) : f ((delta : X) * v) = f v := by
    let P := p (roots S)
    let Pm := (rationalSubgroup F _).map (map F _ G P).toMonoidHom
    have hP : ∀ r ∈ Pm, ∀ y, Φ (r * y) = Φ y := by
      intro r hr y
      exact truncationKernel_parabolicRational_mul hG hi hν D hK hρ (rootSet_subset i ν S)
        Tp φ hφ.2.2 ((mem_parabolicRationalImage_iff _ _).mpr ((rationalImage_eq_map P).symm ▸ hr)) y
    have hdelta : ((delta : X) : A) ∈ rationalSubgroup F G :=
      rationalImage_le_rationalSubgroup _ ((mem_rationalSubgroup_range_iff _ _).mp delta.2)
    have he := tsum_out_mul_left (P := Pm) (g := Φ) hP hdelta ((v : A) * x)
    change cutoffSeries hG hi D hK hρ S Tp φ (((((delta : X) * v) : X) : A) * x) =
      cutoffSeries hG hi D hK hρ S Tp φ ((v : A) * x)
    rw [Subgroup.coe_mul, mul_assoc]
    exact he
  have hqm : Measurable (fun v : Z => f v.out) := by
    rw [RankinSelbergGlobal.Unfolding.out_eq_lift Γ f hfinv]
    exact measurable_from_quotient.mpr hfm
  obtain ⟨C, hC, hbound⟩ := exists_enorm_cutoffSeries_bound_on_radical hG hi hν D hK hρ
    (labelFinset S) (labelFinset_mem_powerset hG hi S) (roots Q) (rootSet_subset i ν Q) Tp φ hφ x
  rw [coe_labelFinset] at hbound
  change Integrable (fun v : Z => f v.out) m
  apply (integrable_const C.toReal).mono hqm.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun v => ?_
  have hC' : ‖f v.out‖ₑ ≤ C := enorm_tsum_le_tsum_enorm.trans (hbound v.out)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_ofReal (norm_nonneg _)]
  exact ENNReal.toReal_mono hC (by simpa only [ofReal_norm] using hC')

include hν in
/-- The full constant term is the sum of the signed Bruhat expansions of its cutoff series. -/
theorem constantTerm_truncation_eq_bruhat [Fintype B] [Fintype W]
    (hunf : GeometricLemmaUnfoldingStatement.{u})
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (Q : Finset B) (n : W → normalizerPoints i)
    (hn : ∀ w, (QuotientGroup.mk (n w) : W) = w)
    (Tp : V T) (φ : A → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ) (x : A) :
    constantTerm F i ν (roots Q) (truncation hG hi D hK hρ Tp φ) x =
      ∑ S : Finset B, (-1 : ℂ) ^ (Fintype.card B - S.card) *
        ∑ w ∈ Finset.univ.filter (IsMinimal cs Q S),
          bruhatCutoffSum hG hi D hK hρ Q S (intersectionSubset cs Q S w)
            (intersectionSubset cs S Q w⁻¹) (innerAdelicPoint F G (n w).val) Tp φ x := by
  classical
  let U := SubgroupFunctor.range (rad (roots Q))
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set A) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (rad (roots Q))
  let Z := AdelicSubgroupPoints.RationalQuotient F G U
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let f (S : Finset B) (v : Z) := cutoffSeries hG hi D hK hρ S Tp φ
    ((v.out : AdelicSubgroupPoints.adelicPoints F G U).val * x)
  let sign (S : Finset B) : ℂ := (-1 : ℂ) ^ (Fintype.card B - S.card)
  have hInt (S : Finset B) : Integrable (f S) m :=
    cutoffSeries_integrable_radical hG hi hν D hK hρ Q S Tp φ hφ x
  change (∫ v : Z, truncation hG hi D hK hρ Tp φ
    ((v.out : AdelicSubgroupPoints.adelicPoints F G U).val * x) ∂m) = _
  simp_rw [truncation_eq_sum_cutoffSeries hG hi D hK hρ]
  change (∫ v, ∑ S, sign S * f S v ∂m) = _
  rw [integral_finsetSum _ (fun S _ => (hInt S).const_mul (sign S))]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_const_mul]
  apply congrArg (sign S * ·)
  exact (constantTerm_cutoffSeries_bruhat hG hi hν D hK hρ hunf cs hcs Q S n hn Tp φ hφ x).2.2

end Langlands.Global.ArthurTruncation.Idempotence
