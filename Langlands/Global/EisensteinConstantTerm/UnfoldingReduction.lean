import Langlands.Global.EisensteinConstantTerm.UnfoldingAdelic

/-! # The unfolding identity of the geometric lemma from subgroup facts in `G(𝔸)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped ENNReal NNReal CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme LeftCosetSpace AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup isClosed_conjStab

set_option maxHeartbeats 1600000 in
/-- **The unfolding identity from the subgroup structure.** Under the hypotheses of
`GeometricLemmaUnfoldingStatement` on the four unipotent radicals, the subgroup facts
`UnfoldingSubgroupStructure` in `G(𝔸)` imply its conclusion for every `h` and `y`. -/
theorem geometricLemmaUnfolding_of_structure (F : Type u) [Field F] [NumberField F]
    {G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine V.X.left] [IsAffine P'.X.left] [IsAffine U'.X.left]
    [IsAffine V'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
    (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')
    [IsClosedImmersion (f ≫ p).hom.hom.left] [IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left]
    [IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left]
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hU' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hV' : LeviSubgroup.IsGeometricUnipotentRadical iV')
    (hS : UnfoldingSubgroupStructure F p iU q iV w f iU' g' iV')
    (h : AdelicGroupPoints F G → ℂ) (hm : Measurable h)
    (hhU : ∀ u ∈ parabolicUnipotentImage F p iU, ∀ x, h (u * x) = h x)
    (hhP : ∀ z ∈ rationalImage F p, ∀ x, h (z * x) = h x) (y : AdelicGroupPoints F G)
    (hfin : ∫⁻ x, ‖h ((innerAdelicPoint F G w)⁻¹ *
            ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
              (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)‖ₑ
          ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G w) < ∞) :
    Integrable (fun x => subgroupConstantTerm F (iU' ≫ f ≫ p) h
        ((innerAdelicPoint F G w)⁻¹ *
          ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
            (SubgroupFunctor.range (iV' ≫ g' ≫ q))) : AdelicGroupPoints F G) * y))
      (intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) (innerAdelicPoint F G w)) ∧
    ∫ x, subgroupConstantTerm F (iU' ≫ f ≫ p) h
        ((innerAdelicPoint F G w)⁻¹ *
          ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
            (SubgroupFunctor.range (iV' ≫ g' ≫ q))) : AdelicGroupPoints F G) * y)
      ∂intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) (innerAdelicPoint F G w) =
    ∫ x, h ((innerAdelicPoint F G w)⁻¹ *
        ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)
      ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G w) := by
  set wA := innerAdelicPoint F G w with hwA
  set GF := AdelicGroupPoints.rationalSubgroup F G
  have hR : IsDiscrete (GF : Set (AdelicGroupPoints F G)) := isDiscrete_rationalSubgroupAdelic
  have hw : wA ∈ GF := by rw [hwA, innerAdelicPoint_eq_rational]; exact ⟨_, rfl⟩
  -- the group schemes
  have hUcl : IsClosedSubgroup iU := hU.1.isClosedSubgroup
  have : IsClosedImmersion iU.hom.hom.left := hUcl
  have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  have hjU : IsClosedSubgroup (iU ≫ p) :=
    hUcl.comp (inferInstance : IsClosedImmersion p.hom.hom.left)
  have : IsClosedImmersion (iU ≫ p).hom.hom.left := hjU
  have hjV : IsClosedSubgroup (iV ≫ q) :=
    (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left)
  have hjV' : IsClosedSubgroup (iV' ≫ g' ≫ q) :=
    (inferInstance : IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left)
  have hjU' : IsClosedSubgroup (iU' ≫ f ≫ p) :=
    (inferInstance : IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left)
  have : IsAffineHom V.X.hom := by rw [← Over.w (iV ≫ q).hom.hom]; infer_instance
  have : LocallyOfFiniteType V.X.hom := by rw [← Over.w (iV ≫ q).hom.hom]; infer_instance
  -- the adelic subgroups
  set Va := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
  set V'a := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q))
  set Ua := parabolicUnipotentImage F p iU
  set U'a := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p))
  have : IsClosed (Va : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  have : IsClosed (V'a : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV' ≫ g' ≫ q)
  have : IsClosed (Ua : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  have : IsClosed (U'a : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU' ≫ f ≫ p)
  obtain ⟨hS0, ⟨A, hAcl, hAU', hAV, hUU', hUn, hAU, hdecU, hratU⟩,
    ⟨B, hBcl, hBV', hBU, hVV', hVn, hBV, hdecV, hratV⟩⟩ := hS
  have : IsClosed (A : Set (AdelicGroupPoints F G)) := hAcl
  have : IsClosed (B : Set (AdelicGroupPoints F G)) := hBcl
  -- compact covers
  obtain ⟨CV, hCV, hCVc⟩ := exists_cover_latticeOf_range (iV ≫ q) hV.1.smooth
    hV.1.connectedSpace hV.1.isUnipotent
  obtain ⟨CV', hCV', hCV'c⟩ := exists_cover_latticeOf_range (iV' ≫ g' ≫ q) hV'.1.smooth
    hV'.1.connectedSpace hV'.1.isUnipotent
  obtain ⟨CU, hCU, hCUc⟩ := exists_cover_latticeOf_range (iU ≫ p) hU.1.smooth
    hU.1.connectedSpace hU.1.isUnipotent
  obtain ⟨CU', hCU', hCU'c⟩ := exists_cover_latticeOf_range (iU' ≫ f ≫ p) hU'.1.smooth
    hU'.1.connectedSpace hU'.1.isUnipotent
  obtain ⟨CK, hCK, hCKc⟩ := exists_cover_conjStab p iU (iV ≫ q) w hjU hV.1.isUnipotent
  obtain ⟨CN, hCN, hCNc⟩ := exists_cover_conjStab (f ≫ p) iU' (iV ≫ q) w hjU' hV.1.isUnipotent
  -- rational points of `U'` lie in `P(F)`
  have hU'R : ∀ x ∈ U'a, x ∈ GF → x ∈ rationalImage F p := by
    intro x hx hxR
    have h1 : (⟨x, hx⟩ : U'a) ∈
        AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iU' ≫ f ≫ p)) := by
      rw [rationalSubgroup_range_eq_latticeOf _ hjU']; exact hxR
    have h2 := (mem_rationalSubgroup_range_iff _ _).mp h1
    change x ∈ rationalImage F (iU' ≫ f ≫ p) at h2
    rw [← Category.assoc] at h2
    exact rationalImage_comp_le (iU' ≫ f) p h2
  have hhR : ∀ z ∈ U'a, z ∈ GF → ∀ x, h (z * x) = h x :=
    fun z hz hzR x => hhP z (hU'R z hz hzR) x
  -- the two lattices
  have hL1 : stabilizerRationalSubgroup F p (iV ≫ q) wA = latticeOf GF Va ⊓ conjStab Va U'a wA := by
    ext v
    rw [mem_stabilizerRationalSubgroup_iff, Subgroup.mem_inf, mem_conjStab]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : v.val ∈ GF := rationalSubgroup_le_latticeOf _ h1
      exact ⟨h1', hS0 v.val v.property h1' h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [rationalSubgroup_range_eq_latticeOf _ hjV]; exact h1, ?_⟩
      exact hU'R _ h2 ((conj_mem_iff hw _).mpr h1)
  have hL2 : intertwiningRationalSubgroup F (f ≫ p) iU' (iV' ≫ g' ≫ q) wA =
      latticeOf GF V'a ⊓ conjStab V'a U'a wA := by
    ext v
    rw [mem_intertwiningRationalSubgroup_iff, Subgroup.mem_inf, mem_conjStab,
      rationalSubgroup_range_eq_latticeOf _ hjV']
    rfl
  -- quotient measure structure
  have : BorelSpace (LeftQuotient (conjStab Va U'a wA)) := by
    have : T2Space (LeftQuotient (conjStab Va U'a wA)) :=
      leftQuotient_t2Space _ (isClosed_conjStab Va U'a wA)
    have : SecondCountableTopology (LeftQuotient (conjStab Va U'a wA)) :=
      (leftQuotient_isOpenQuotientMap _).secondCountableTopology
    have : PolishSpace Va := (inferInstance : IsClosed (Va : Set (AdelicGroupPoints F G))).polishSpace
    exact LeftCosetSpace.quotient_borelSpace _
  -- the left side
  have hΓd := isDiscrete_stabilizerRationalSubgroup F p (iV ≫ q) wA
  have hΓ₀d : IsDiscrete ((latticeOf GF Va ⊓ conjStab Va U'a wA : Subgroup Va) : Set Va) :=
    (isDiscrete_latticeOf GF hR Va).mono inf_le_left
  have hLm : Measurable (fun v : Va => h (wA⁻¹ * v.val * y)) :=
    hm.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hLinv : ∀ g ∈ stabilizerRationalSubgroup F p (iV ≫ q) wA, ∀ v : Va,
      h (wA⁻¹ * (g * v).val * y) = h (wA⁻¹ * v.val * y) := by
    intro g hg v
    have hg' := ((mem_stabilizerRationalSubgroup_iff F p (iV ≫ q) wA g).mp hg).2
    rw [Subgroup.coe_mul, show wA⁻¹ * (g.val * v.val) * y = (wA⁻¹ * g.val * wA) *
      (wA⁻¹ * v.val * y) by group]
    exact hhP _ hg' _
  have hμV := normalizedHaarMeasure_eq_normalizedHaar (iV ≫ q) hjV
  have hfdL := fundamentalDomain_congr hL1 hΓd hΓ₀d
  have hfin' : ∫⁻ v in fundamentalDomain (latticeOf GF Va ⊓ conjStab Va U'a wA)
        ((isDiscrete_latticeOf GF hR Va).mono inf_le_left), ‖h (wA⁻¹ * v.val * y)‖ₑ
        ∂normalizedHaar (latticeOf GF Va) (isDiscrete_latticeOf GF hR Va) < ∞ := by
    have := lintegral_discreteQuotientMeasure_out _ hΓd
      (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q)))
      (fun v : Va => ‖h (wA⁻¹ * v.val * y)‖ₑ) hLm.enorm
      (fun g hg v => by rw [hLinv g hg v])
    rw [← hfdL, ← hμV, ← this]
    exact hfin
  -- the abstract identity
  obtain ⟨hI, hE⟩ := integral_unfolding_eq GF hR Va V'a Ua U'a A B wA hw hUU' hAU' hAV hUn hAU
    hdecU hratU hVV' hBV' hBU hVn hBV hdecV hratV hCV hCVc hCV' hCV'c hCU hCUc hCU' hCU'c
    hCK hCKc hCN hCNc h hm hhU hhR y hfin'
  -- the right side
  have hΓ'd := isDiscrete_intertwiningRationalSubgroup F (f ≫ p) iU' (iV' ≫ g' ≫ q) wA
  have hμV' := normalizedHaarMeasure_eq_normalizedHaar (iV' ≫ g' ≫ q) hjV'
  have hfdR := fundamentalDomain_congr hL2 hΓ'd
    ((isDiscrete_latticeOf GF hR V'a).mono inf_le_left)
  have hCeq : ∀ x : AdelicGroupPoints F G, subgroupConstantTerm F (iU' ≫ f ≫ p) h x =
      ∫ u in fundamentalDomain (latticeOf GF U'a) (isDiscrete_latticeOf GF hR U'a),
        h (u.val * x) ∂normalizedHaar (latticeOf GF U'a) (isDiscrete_latticeOf GF hR U'a) :=
    fun x => subgroupConstantTerm_eq_setIntegral (iU' ≫ f ≫ p) h hm
      (fun z hz x => hhP z (by
        rw [← Category.assoc] at hz
        exact rationalImage_comp_le (iU' ≫ f) p hz) x) x
  have hRm : Measurable (fun x : V'a =>
      subgroupConstantTerm F (iU' ≫ f ≫ p) h (wA⁻¹ * x.val * y)) := by
    simp_rw [hCeq]
    exact (measurable_setIntegral_subgroup_mul U'a _ _ h hm).comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hRinv : ∀ g ∈ intertwiningRationalSubgroup F (f ≫ p) iU' (iV' ≫ g' ≫ q) wA,
      ∀ x : V'a, subgroupConstantTerm F (iU' ≫ f ≫ p) h (wA⁻¹ * (g * x).val * y) =
        subgroupConstantTerm F (iU' ≫ f ≫ p) h (wA⁻¹ * x.val * y) := by
    intro g hg x
    have hg' := ((mem_intertwiningRationalSubgroup_iff F (f ≫ p) iU' (iV' ≫ g' ≫ q) wA g).mp
      hg).2
    rw [hCeq, hCeq, Subgroup.coe_mul, show wA⁻¹ * (g.val * x.val) * y = (wA⁻¹ * g.val * wA) *
      (wA⁻¹ * x.val * y) by group]
    exact setIntegral_latticeOf_mul_left GF hR U'a hCU' hCU'c h hhR hg' _
  refine ⟨?_, ?_⟩
  · change Integrable _ (discreteQuotientMeasure _ hΓ'd
      (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV' ≫ g' ≫ q))))
    rw [integrable_discreteQuotientMeasure_out_iff _ hΓ'd _
      (fun x : V'a => subgroupConstantTerm F (iU' ≫ f ≫ p) h (wA⁻¹ * x.val * y)) hRm hRinv,
      hfdR, hμV']
    simp_rw [hCeq]
    exact hI
  · change ∫ x, _ ∂(discreteQuotientMeasure _ hΓ'd
      (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)))) =
      ∫ x, _ ∂(discreteQuotientMeasure _ hΓd
        (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))))
    rw [integral_discreteQuotientMeasure_out _ hΓ'd _
      (fun x : V'a => subgroupConstantTerm F (iU' ≫ f ≫ p) h (wA⁻¹ * x.val * y)) hRm hRinv,
      integral_discreteQuotientMeasure_out _ hΓd _
      (fun v : Va => h (wA⁻¹ * v.val * y)) hLm hLinv, hfdR, hμV', hfdL, hμV]
    simp_rw [hCeq]
    exact hE

end Langlands.Global
