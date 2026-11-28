import Langlands.Global.AdelicCharacteristicSplitVolume
import Langlands.Global.AdelicCharacteristicShellIntegral
import Langlands.Global.LeftCosetImageMajorant
import Langlands.Global.AdelicFiniteVolumeProof

/-! # Integrating a minimal-height majorant on a characteristic shell -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Classical ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace Langlands.Global.LeftCosetSpace

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {Γ Λ : Subgroup H}

/-- A restriction of a smaller quotient dominates the quotient measure restricted to its image.
The bound holds even when more than one point of the smaller quotient has the same image. -/
theorem restrict_le_map_projectionOfLE_restrict
    (hle : Γ ≤ Λ) (hΓ : IsDiscrete (Γ : Set H)) (hΛ : IsDiscrete (Λ : Set H))
    (dh : Measure H) [dh.IsMulLeftInvariant] {A : Set (LeftCosetSpace Γ)}
    (hA : MeasurableSet A) (hImage : MeasurableSet (projectionOfLE hle '' A)) :
    (discreteQuotientMeasure Λ hΛ dh).restrict (projectionOfLE hle '' A) ≤
      Measure.map (projectionOfLE hle) ((discreteQuotientMeasure Γ hΓ dh).restrict A) := by
  let D := fundamentalDomain Γ hΓ
  let q := projectionOfLE hle
  have hq : Measurable q := measurable_projectionOfLE hle
  let : Countable Λ := countable_of_isDiscrete Λ hΛ
  let : SMulInvariantMeasure Λ H dh := ⟨fun d E _ => measure_preimage_mul dh d.val E⟩
  refine Measure.le_iff.mpr fun E hE => ?_
  let S := (mk Γ ⁻¹' (q ⁻¹' E ∩ A)) ∩ D
  have heq : mk Λ '' S = E ∩ q '' A := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg.1.1, mk Γ g, hg.1.2, rfl⟩
    · rintro ⟨hx, y, hy, rfl⟩
      obtain ⟨g, rfl⟩ := mk_surjective Γ y
      obtain ⟨d, hd, _⟩ := fundamentalDomain_unique Γ hΓ g
      refine ⟨d.val * g, ⟨?_, hd⟩, congrArg q (mk_subgroup_mul Γ d g)⟩
      change mk Γ (d.val * g) ∈ q ⁻¹' E ∩ A
      rw [mk_subgroup_mul]
      exact ⟨hx, hy⟩
  rw [Measure.map_apply hq hE, Measure.restrict_apply (hq hE), Measure.restrict_apply hE]
  unfold discreteQuotientMeasure
  rw [quotientMeasure_apply Γ dh D ((hq hE).inter hA), ← heq]
  exact quotientMeasure_mk_image_le Λ dh (isFundamentalDomain Λ hΛ dh)
    (heq.symm ▸ hE.inter hImage)

private theorem preimage_image_mk_of_invariant {G : Type} [Group G] (Δ : Subgroup G)
    (S : Set G) (hS : ∀ d : Δ, ∀ z, d.val * z ∈ S ↔ z ∈ S) :
    mk Δ ⁻¹' (mk Δ '' S) = S := by
  ext z
  constructor
  · rintro ⟨g, hg, heq⟩
    let d : Δ := ⟨z * g⁻¹, (mk_eq_mk_iff Δ g z).mp heq⟩
    have he : d.val * g = z := by simp [d, mul_assoc]
    exact he ▸ (hS d g).mpr hg
  · intro hz
    exact ⟨z, hz, rfl⟩

end Langlands.Global.LeftCosetSpace

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative
  ArthurTruncation ArthurParabolicSpaces AdelicSiegelFactors AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "p" => fam.p fam.bot
local notation "u" => fam.iU fam.bot
local notation "l" => fam.l fam.bot
local notation "a" => fam.a fam.bot
local notation "M" => fam.M fam.bot
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (u ≫ p))
local notation "B" => relativePositiveSubgroup (l ≫ p) a
local notation "M₁" => normOneSubgroup F M
local notation "X" => (N × (B × M₁)) × K
local notation "G₁" => normOneSubgroup F G
local notation "Γ[" b "]" => parabolicRationalNormOneSubgroup (F := F) (fam.p b)
local notation "Q[" b "]" => LeftCosetSpace (Γ[b])
local notation "dQ[" b "]" => LeftCosetSpace.haarQuotientMeasure (Γ[b])
  (isDiscrete_parabolicRationalNormOneSubgroup (fam.p b))
local notation "ΓN" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (u ≫ p))
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "DN" => LeftCosetSpace.fundamentalDomain ΓN
  (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (u ≫ p)))
local notation "DM" => LeftCosetSpace.fundamentalDomain ΓM (isDiscrete_rationalNormOneSubgroup F M)
local notation "H₀" => fam.minimalHeight hK
local notation "Hb[" b "]" => H₀ (fam.relativeSplitPoint fam.bot b)
local notation "ψ" => fam.characteristicShellCoordinates fam.bot hK
local notation "δ" => relativePositiveDensity p l a
local notation "sq[" b "]" => (fam.halfModulus fam.bot (fam.relativeParabolicSplitPoint fam.bot b) ^ 2)
local notation "dK" => compactHaarProbability F G K hK.isCompact
local notation "dM" => normOneRationalQuotientHaarMeasure F M

local instance : IsClosedImmersion (p).hom.hom.left := fam.isClosedImmersion_p fam.bot
local instance : IsClosedImmersion (u ≫ p).hom.hom.left := fam.closedU fam.bot
local instance : IsAffineHom (M).X.hom := (fam.isCompatible fam.bot).levi.isConnectedReductive.isAffineHom
local instance : IsIso (subgroupMultiplication l u) :=
  Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
    (⟨⟨T, fam.i, fam.ν, ∅, fam.f fam.bot⟩, fam.isCompatible fam.bot⟩ : ParabolicRootPresentation p l a)
    fam.connectedReductive (fam.isUnipotentRadical fam.bot)

private theorem minimalRational_le : Γ[fam.bot] ≤ Γ[J] := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  let j := fam.nestedParabolicHom (show fam.bot ≤ J from empty_subset _)
  refine ⟨rationalNormOne F (fam.P J) ((fam.P fam.bot).affinePointsTarget j _ q),
    ⟨_, rfl⟩, Subtype.ext ?_⟩
  change map F (fam.P J) G (fam.p J)
      (rational F (fam.P J) ((fam.P fam.bot).affinePointsTarget j _ q)) =
    map F (fam.P fam.bot) G p (rational F (fam.P fam.bot) q)
  rw [← map_rational, ← map_comp_apply_of_hom, fam.nestedParabolicHom_comp]

private theorem minimalHeight_invariant_rational (d : Γ[fam.bot]) (x : G₁) :
    H₀ (d.val * x).val = H₀ x.val := by
  obtain ⟨y, ⟨q, rfl⟩, hq⟩ := d.property
  have hmap : (d.val : AdelicGroupPoints F G) = map F (fam.P fam.bot) G p (rational F (fam.P fam.bot) q) :=
    congrArg Subtype.val hq.symm
  have hp : SubgroupFunctor.range p = SubgroupFunctor.range (Standard.parabolicHom fam.i fam.ν ∅) :=
    (fam.isCompatible fam.bot).parabolic_eq.trans
      (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm
  have hr : rationalImage F p ≤ rationalImage F (Standard.parabolicHom fam.i fam.ν ∅) :=
    rationalImage_le_of_range_le _ _ hp.le
  obtain ⟨r, hr⟩ := hr (show (d.val : AdelicGroupPoints F G) ∈ rationalImage F p from ⟨q, hmap.symm⟩)
  change map F (Standard.parabolicScheme fam.i fam.ν ∅) G (Standard.parabolicHom fam.i fam.ν ∅)
    (rational F (Standard.parabolicScheme fam.i fam.ν ∅) r) = d.val.val at hr
  change H₀ (d.val.val * x.val) = H₀ x.val
  rw [← hr, fam.minimalHeight_map_mul hK]
  simp only [minimalHeight, ArthurTruncation.height, (fam.isIwasawaCompact_standardBot hK).height_map,
    characterLog_rational]
  have hzero : toA0 fam.maximalSplit.isSplitSubtorus.1 fam.bijective_restrictToTorus_bot 0 = 0 := by
    apply (isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1).bijective_right.injective
    apply LinearMap.ext
    intro χ
    obtain ⟨χ₀, rfl⟩ := fam.bijective_restrictToTorus_bot.surjective χ
    simp only [pair_toA0, LinearMap.flip_apply, map_zero, LinearMap.zero_apply]
  rw [hzero, zero_add]

private theorem minimalHeight_shellRepresentative (x : X) :
    H₀ (fam.characteristicShellRepresentative fam.bot hK x).val = Hb[x.1.2.1] := by
  rw [fam.characteristicShellRepresentative_val]
  obtain ⟨_, h⟩ := fam.relativeIwasawaHeight fam.bot hK
  obtain ⟨heq, hm⟩ := h x.1.1 x.1.2.1 x.1.2.2 x.2
  rw [heq]
  have hb : corootSubspace D fam.bot.val = ⊥ := by
    change Submodule.span ℝ ((D).realCorootsOf ∅) = ⊥
    simp [RelativeRootReflectionData.realCorootsOf]
  rw [hb, Submodule.mem_bot] at hm
  rw [hm, add_zero]

private theorem continuous_functional_minimalHeight (L : V T →ₗ[ℝ] ℝ) :
    Continuous fun g : AdelicGroupPoints F G => L (H₀ g) := by
  obtain ⟨χ, hχ⟩ := (isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1).bijective_left.surjective L
  obtain ⟨χ₀, hχ₀⟩ := fam.bijective_restrictToTorus_bot.surjective χ
  rw [← hχ, ← hχ₀]
  change Continuous fun g => pair T (restrictToTorus F fam.i fam.ν ∅ χ₀)
    (height fam.maximalSplit (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot g)
  simp_rw [height, pair_toA0]
  exact (InducedInnerProductSesquilinear.continuous_realParameterPairing F _ χ₀).comp
    (fam.isIwasawaCompact_standardBot hK).continuous_height

private theorem measurableSet_minimalHeight_shell (T₀ Tp S : V T) :
    MeasurableSet {x : G₁ | H₀ x.val ∈ characteristicShell fam.connectedReductive fam.maximalSplit D J T₀ Tp S} := by
  let A := characteristicShell fam.connectedReductive fam.maximalSplit D J T₀ Tp S
  let H (g : G₁) := H₀ g.val
  let π := levelProjection fam.connectedReductive fam.maximalSplit fam.ν D J.val
  let D₀ := simpleFinset fam.ν fam.connectedReductive fam.maximalSplit
  let w := weight fam.connectedReductive fam.maximalSplit fam.ν D
  have hlin (L : V T →ₗ[ℝ] ℝ) : Continuous (fun x : G₁ => L (H x)) :=
    (fam.continuous_functional_minimalHeight hK L).comp continuous_subtype_val
  have haff (L : V T →ₗ[ℝ] ℝ) (v : V T) : Continuous (fun x : G₁ => L (H x - v)) := by
    simp only [map_sub]
    exact (hlin L).sub continuous_const
  let pr := (D).realCorootSpan.subtype.comp (toCorootSpan fam.connectedReductive fam.maximalSplit D)
  have hClosed : IsClosed {x : G₁ | H x ∈ (D).realCorootSpan} := by
    have heq : {x : G₁ | H x ∈ (D).realCorootSpan} =
        ⋂ χ : Vstar T, {x | pair T χ (H x) = pair T χ (pr (H x))} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro hx χ
        have he : pr (H x) = H x := congrArg Subtype.val
          (toCorootSpan_apply_coe fam.connectedReductive fam.maximalSplit D (⟨H x, hx⟩ : (D).realCorootSpan))
        rw [he]
      · intro hx
        have he : H x = pr (H x) :=
          (isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1).bijective_right.injective
            (LinearMap.ext fun χ => hx χ)
        rw [he]
        exact (toCorootSpan fam.connectedReductive fam.maximalSplit D (H x)).property
    rw [heq]
    exact isClosed_iInter fun χ => isClosed_eq (hlin (pair T χ)) (hlin ((pair T χ).comp pr))
  let : Finite J.val := ((fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).subset J.property).to_subtype
  let : Finite (Δ \ J.val : Set _) := ((fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).sdiff (t := J.val)).to_subtype
  let R := ⋂ α : D₀, {x : G₁ | 0 ≤ eval T α.val (H x - T₀) ∧
    w (D₀ : Set _) α.val (H x - (Tp + S)) ≤ 0}
  let L := ⋂ α : J.val, {x : G₁ | w J.val α.val (H x - Tp) ≤ 0}
  let U := ⋂ α : (Δ \ J.val : Set _), {x : G₁ | 0 < (eval T α.val ∘ₗ π) (H x - Tp)}
  have hR : MeasurableSet R := MeasurableSet.iInter fun α =>
    ((isClosed_le continuous_const (haff (eval T α.val) T₀)).inter
      (isClosed_le (haff (w (D₀ : Set _) α.val) (Tp + S)) continuous_const)).measurableSet
  have hL : MeasurableSet L := MeasurableSet.iInter fun α =>
    (isClosed_le (haff (w J.val α.val) Tp) continuous_const).measurableSet
  have hU : MeasurableSet U := MeasurableSet.iInter fun α =>
    (isOpen_lt continuous_const (haff (eval T α.val ∘ₗ π) Tp)).measurableSet
  have he : {x : G₁ | H x ∈ A} = {x | H x ∈ (D).realCorootSpan} ∩ R ∩ L ∩ U := by
    ext x
    change (H x ∈ characteristicChamber fam.ν fam.connectedReductive fam.maximalSplit D T₀ (Tp + S) ∧
      H x ∈ parabolicCharacteristicChamber fam.connectedReductive fam.maximalSplit D J T₀ Tp) ↔ _
    simp only [mem_inter_iff, mem_ofPred_eq]
    have hΔ (α : characterLattice T) : α ∈ D₀ ↔ α ∈ Δ := mem_simpleFinset _ _
    constructor
    · intro hx
      refine ⟨⟨⟨hx.1.1, mem_iInter.mpr fun α => hx.1.2 α.val α.property⟩,
        mem_iInter.mpr fun α => hx.2.2.2.1 α.val α.property⟩,
        mem_iInter.mpr fun α => hx.2.2.2.2 α.val α.property⟩
    · rintro ⟨⟨⟨hs, hR'⟩, hL'⟩, hU'⟩
      have hR'' (α : characterLattice T) (hα : α ∈ D₀) :
          0 ≤ eval T α (H x - T₀) ∧ w (D₀ : Set _) α (H x - (Tp + S)) ≤ 0 :=
        mem_iInter.mp hR' ⟨α, hα⟩
      exact ⟨⟨hs, hR''⟩, hs, fun α hα => (hR'' α ((hΔ α).mpr hα)).1,
        fun α hα => mem_iInter.mp hL' ⟨α, hα⟩, fun α hα => mem_iInter.mp hU' ⟨α, hα⟩⟩
  change MeasurableSet {x : G₁ | H x ∈ A}
  rw [he]
  exact ((hClosed.measurableSet.inter hR).inter hL).inter hU

variable (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
  (Standard.leviScheme fam.i fam.ν ∅))

local notation "pJ" => LeftCosetSpace.projectionOfLE (fam.minimalRational_le J)
local notation "Sh" => characteristicShell fam.connectedReductive fam.maximalSplit D J
set_option quotPrecheck false in
local notation "L₀[" T₀ "," Tp "," S "]" => LeftCosetSpace.mk (Γ[fam.bot]) ''
  {x : G₁ | H₀ x.val ∈ Sh T₀ Tp S}

private theorem minimalProjection_shellLift (hcov : IsRationalCovering C) (T₀ Tp S : V T) :
    pJ '' L₀[T₀,Tp,S] = fam.presentedCharacteristicShellLift J hK C T₀ Tp S := by
  rw [Set.image_image]
  change LeftCosetSpace.mk (Γ[J]) '' {x : G₁ | H₀ x.val ∈ Sh T₀ Tp S} =
    LeftCosetSpace.mk (Γ[J]) '' (Subtype.val ⁻¹'
      characteristicHeightProduct fam.maximalSplit (fam.isIwasawaCompact_standardBot hK)
        fam.bijective_restrictToTorus_bot C (Sh T₀ Tp S))
  exact (fam.characteristicHeightLift hK J C hcov (Sh T₀ Tp S)).symm

private theorem preimage_minimalShellLift (T₀ Tp S : V T) :
    ψ ⁻¹' L₀[T₀,Tp,S] = (Set.univ ×ˢ ({b : B | Hb[b] ∈ Sh T₀ Tp S} ×ˢ Set.univ)) ×ˢ Set.univ := by
  let S₀ := {g : G₁ | H₀ g.val ∈ Sh T₀ Tp S}
  let rep := fam.characteristicShellRepresentative fam.bot hK
  change rep ⁻¹' (LeftCosetSpace.mk (Γ[fam.bot]) ⁻¹' (LeftCosetSpace.mk (Γ[fam.bot]) '' S₀)) = _
  rw [LeftCosetSpace.preimage_image_mk_of_invariant _ _ (by
    intro d g
    change H₀ (d.val * g).val ∈ Sh T₀ Tp S ↔ H₀ g.val ∈ Sh T₀ Tp S
    rw [fam.minimalHeight_invariant_rational hK])]
  ext x
  change H₀ (fam.characteristicShellRepresentative fam.bot hK x).val ∈ Sh T₀ Tp S ↔ _
  rw [fam.minimalHeight_shellRepresentative hK]
  simp only [mem_prod, mem_univ, true_and, and_true, mem_ofPred_eq]

private theorem exists_minimalCoordinateMeasure (dn : Measure N) [dn.IsHaarMeasure] :
    ∃ da : Measure B, da.IsHaarMeasure ∧ SigmaFinite da ∧
      MeasurePreserving ψ (fam.characteristicShellCoordinateMeasure fam.bot hK dn da) (dQ[fam.bot]) := by
  obtain ⟨⟨z, hz⟩, cmp⟩ := standardCocharacter F G fam.connectedReductive T fam.i
    fam.maximalSplit fam.ν fam.generic fam.bot.val fam.bot.property
  let χ := CommGroupScheme.groupHom z ≫ fam.i
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p := by
    rw [← (cmp z hz).1, ← (fam.isCompatible fam.bot).parabolic_eq]
    exact (fam.isCompatible fam.bot).parabolic.isClosedSubgroup.isRepresentedBy_range
  have hN : (Dynamic.unipotent χ).IsRepresentedBy (u ≫ p) := by
    rw [← (cmp z hz).2.2, ← fam.range_radical_eq_standardUnipotent fam.bot]
    exact IsClosedSubgroup.isRepresentedBy_range (fam.closedU fam.bot)
  obtain ⟨da, hda, hsf, hmap⟩ := relativeParabolicQuotientMeasure p u l
    (fam.isUnipotentRadical fam.bot) a (fam.isCompatible fam.bot).levi.isConnectedReductive
    (fam.isCompatible fam.bot).splitComponent fam.connectedReductive hP hN hK dn
  exact ⟨da, hda, hsf, ⟨measurable_normOneRelativeParabolicQuotientCoordinates p u l
    (fam.isUnipotentRadical fam.bot) a (fam.isCompatible fam.bot).levi.isConnectedReductive
    (fam.isCompatible fam.bot).splitComponent hK.isCompact, hmap.symm⟩⟩

private theorem measurable_minimalHalfModulus_sq : Measurable fun b : B => ENNReal.ofReal ‖sq[b]‖ := by
  have h : Continuous fun b : B => fam.relativeParabolicSplitPoint fam.bot b :=
    (map F M (fam.P fam.bot) l).continuous.comp
      ((positivePointMap F M (fam.A fam.bot) a).continuous.comp continuous_subtype_val)
  exact ENNReal.measurable_ofReal.comp
    ((((InducedInnerProductSesquilinear.continuous_parameterPower F (fam.P fam.bot)
      (halfModulusParameter F (fam.P fam.bot))).comp h).pow 2).norm.measurable)

private theorem lintegral_minimalHalfModulus_sq (da : Measure B) (A : Set B) (hA : MeasurableSet A) :
    (∫⁻ b in A, ENNReal.ofReal ‖sq[b]‖ ∂(da.withDensity δ)) = da A := by
  have hd : Measurable (δ : B → ℝ≥0∞) :=
    ENNReal.measurable_ofReal.comp ((continuous_inverseModulus l).measurable.comp
      ((positivePointMap F M (fam.A fam.bot) a).continuous.measurable.comp measurable_subtype_coe))
  rw [setLIntegral_withDensity_eq_setLIntegral_mul da hd fam.measurable_minimalHalfModulus_sq hA]
  have hδ (b : B) : δ b ≠ ∞ := ENNReal.ofReal_ne_top
  have he : (δ * (fun b : B => ENNReal.ofReal ‖sq[b]‖)) = 1 := by
    funext b
    have hn : ‖sq[b]‖ ≠ 0 := norm_ne_zero_iff.mpr (pow_ne_zero 2 (parameterPower_ne_zero _ _))
    have hh := congrArg Norm.norm (fam.relativePositiveDensity_toReal fam.bot b)
    rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, norm_inv] at hh
    change δ b * ENNReal.ofReal ‖sq[b]‖ = 1
    rw [← ENNReal.ofReal_toReal (hδ b), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      hh, inv_mul_cancel₀ hn, ENNReal.ofReal_one]
  rw [he]
  change (∫⁻ b in A, (1 : ℝ≥0∞) ∂da) = da A
  rw [lintegral_const, one_mul, Measure.restrict_apply_univ]

private theorem splitHeightRegion_subset_of_shell {T₀ T₁ Tp S : V T}
    (hT₁ : ∀ x α, α ∈ Δ → 0 ≤ eval T α (x - T₀) → 0 < eval T α (x - T₁)) :
    {b : B | Hb[b] ∈ Sh T₀ Tp S} ⊆
      fam.characteristicSplitHeightRegion fam.bot hK T₁ (Tp + S - T₁) := by
  intro b hb
  have hπ (x : V T) : levelProjection fam.connectedReductive fam.maximalSplit fam.ν D fam.bot.val x = x := by
    rw [← levelProjection_eq_projectionOnto fam.connectedReductive fam.maximalSplit fam.generic D fam.bot.property,
      Submodule.projectionOnto_apply_of_mem_left]
    exact (mem_rootAnnihilator _ _).mpr fun _ h => (Set.notMem_empty _ h).elim
  change Hb[b] ∈ Sh T₀ Tp S at hb
  change Hb[b] ∈ characteristicSplitShell fam.connectedReductive fam.maximalSplit D fam.bot T₁ _
  have hΔ : (simpleFinset fam.ν fam.connectedReductive fam.maximalSplit : Set (characterLattice T)) = Δ :=
    Set.ext fun _ => mem_simpleFinset _ _
  refine ⟨⟨hb.1.1, (mem_rootAnnihilator _ _).mpr fun _ h => (Set.notMem_empty _ h).elim,
    fun α hα => ?_⟩, fun α hα => ?_⟩
  · rw [hπ]
    exact hT₁ _ α hα.1 (hb.2.2.1 α hα.1)
  · rw [hπ, add_sub_cancel]
    have h := (hb.1.2 α ((mem_simpleFinset _ _).mpr hα.1)).2
    simpa only [hΔ] using h

/-- A measurable function on the rational parabolic shell with a bound by the squared
minimal half modulus times a scalar has a shell integral bounded by that scalar times
polynomial volume. The hypothesis is checked on the actual minimal Iwasawa representatives. -/
def CharacteristicShellErrorIntegralStatement {n : ℕ} (eT : V T ≃ₗ[ℝ] (Fin n → ℝ)) : Prop :=
  IsRationalCovering C → ∀ T₀ : V T, ∃ T₁ : V T, ∃ A > (0 : ℝ), ∀ Tp S : V T,
    ∀ (f : Q[J] → ℂ), Measurable f → ∀ E : ℝ, 0 ≤ E →
      (∀ x : X, Hb[x.1.2.1] ∈ Sh T₀ Tp S →
        ‖f (pJ (ψ x))‖ ≤ ‖sq[x.1.2.1]‖ * E) →
      let L := fam.presentedCharacteristicShellLift J hK C T₀ Tp S
      IntegrableOn f L (dQ[J]) ∧
        ‖∫ q in L, f q ∂(dQ[J])‖ ≤
          A * (1 + ‖eT (Tp + S - T₁)‖) ^ Fintype.card (fam.relativeSimpleRoots fam.bot) * E

set_option maxHeartbeats 3500000 in
theorem characteristicShellErrorIntegral {n : ℕ} (eT : V T ≃ₗ[ℝ] (Fin n → ℝ)) :
    fam.CharacteristicShellErrorIntegralStatement J hK C eT := by
  intro hcov T₀
  obtain ⟨T₁, hT₁⟩ := exists_strict_lower_cutoff (i := fam.i) (ν := fam.ν) T₀
  obtain ⟨dn, hdn, hnm⟩ := fam.exists_normalized_shell_radicalHaar fam.bot
  let : dn.IsHaarMeasure := hdn
  obtain ⟨da, hda, hsf, hψ⟩ := fam.exists_minimalCoordinateMeasure hK dn
  let : SigmaFinite da := hsf
  obtain ⟨_, A₀, hA₀, hvol⟩ := fam.characteristicSplitVolume fam.bot hK eT
  obtain ⟨c, hc, hcvol⟩ := hvol da hda
  let d := Fintype.card (fam.relativeSimpleRoots fam.bot)
  let dn' := dn.restrict DN
  let dm' := (Measure.haar : Measure M₁).restrict DM
  let : IsProbabilityMeasure dn' := ⟨(Measure.restrict_apply_univ _).trans hnm⟩
  let : IsProbabilityMeasure dK := compactHaarProbability_isProbabilityMeasure _ _ _ _
  let : IsFiniteMeasure dM := isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive
    F M (fam.isCompatible fam.bot).levi.isConnectedReductive
  have hmvol : dm' univ = dM univ := by
    have hm : MeasurePreserving (LeftCosetSpace.mk ΓM) dm' dM :=
      LeftCosetSpace.measurePreserving_mk ΓM Measure.haar DM
    simpa only [preimage_univ] using hm.measure_preimage MeasurableSet.univ.nullMeasurableSet
  let : IsFiniteMeasure dm' := ⟨hmvol ▸ measure_lt_top dM univ⟩
  let A : ℝ := (1 + (dM univ).toReal) * (c : ℝ) * A₀ ^ d
  have hA : 0 < A := mul_pos (mul_pos (by positivity) (NNReal.coe_pos.mpr hc)) (pow_pos hA₀ _)
  refine ⟨T₁, A, hA, fun Tp S f hf E hE hfbd => ?_⟩
  let L := fam.presentedCharacteristicShellLift J hK C T₀ Tp S
  let Y := {b : B | Hb[b] ∈ Sh T₀ Tp S}
  have hL₀ : MeasurableSet (L₀[T₀,Tp,S]) := by
    let : Countable (Γ[fam.bot]) := LeftCosetSpace.countable_of_isDiscrete _
      (isDiscrete_parabolicRationalNormOneSubgroup p)
    exact LeftCosetSpace.measurableSet_image_mk (Γ[fam.bot]) (fam.measurableSet_minimalHeight_shell J hK T₀ Tp S)
  have hProj := fam.minimalProjection_shellLift J hK C hcov T₀ Tp S
  have hL : MeasurableSet L := by
    let : Countable (Γ[J]) := LeftCosetSpace.countable_of_isDiscrete _
      (isDiscrete_parabolicRationalNormOneSubgroup (fam.p J))
    change MeasurableSet (fam.presentedCharacteristicShellLift J hK C T₀ Tp S)
    rw [← hProj, Set.image_image]
    exact LeftCosetSpace.measurableSet_image_mk (Γ[J]) (fam.measurableSet_minimalHeight_shell J hK T₀ Tp S)
  have hdom := LeftCosetSpace.restrict_le_map_projectionOfLE_restrict (fam.minimalRational_le J)
    (isDiscrete_parabolicRationalNormOneSubgroup p)
    (isDiscrete_parabolicRationalNormOneSubgroup (fam.p J)) (Measure.haar : Measure G₁) hL₀
    (hProj.symm ▸ hL)
  rw [hProj] at hdom
  have hprojMeas : Measurable pJ := LeftCosetSpace.measurable_projectionOfLE _
  have hPre := fam.preimage_minimalShellLift J hK T₀ Tp S
  have hY : MeasurableSet Y := by
    let bsec : B → X := fun b => ((1, (b, 1)), 1)
    have hsec : Measurable bsec := (measurable_const.prodMk (measurable_id.prodMk measurable_const)).prodMk
      measurable_const
    have he : Y = bsec ⁻¹' (ψ ⁻¹' L₀[T₀,Tp,S]) := by
      rw [hPre]
      ext b
      simp only [bsec, mem_preimage, mem_prod, mem_univ, mem_ofPred_eq, and_true, true_and, Y]
    rw [he]
    exact hsec (hψ.measurable hL₀)
  let da' := (da.withDensity δ).restrict Y
  let dprod := (dn'.prod (da'.prod dm')).prod dK
  have hMeq : (fam.characteristicShellCoordinateMeasure fam.bot hK dn da).restrict
      (ψ ⁻¹' L₀[T₀,Tp,S]) = dprod := by
    rw [hPre, characteristicShellCoordinateMeasure, ← Measure.prod_restrict, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ, Measure.restrict_univ]
  have hψ' : MeasurePreserving ψ dprod ((dQ[fam.bot]).restrict L₀[T₀,Tp,S]) :=
    hMeq ▸ (hψ.restrict_preimage hL₀)
  have hs : ∀ᵐ x : X ∂dprod, Hb[x.1.2.1] ∈ Sh T₀ Tp S := by
    rw [← hMeq]
    filter_upwards [ae_restrict_mem (hψ.measurable hL₀)] with x hx
    rw [hPre] at hx
    exact hx.1.2.1
  let W : B → ℝ≥0∞ := fun b => ENNReal.ofReal ‖sq[b]‖
  have hW : Measurable W := fam.measurable_minimalHalfModulus_sq
  have hInt : (∫⁻ q in L, ENNReal.ofReal ‖f q‖ ∂(dQ[J])) ≤ da Y * dM univ * ENNReal.ofReal E := by
    calc
      _ ≤ ∫⁻ q, ENNReal.ofReal ‖f q‖ ∂(Measure.map pJ ((dQ[fam.bot]).restrict L₀[T₀,Tp,S])) :=
        lintegral_mono' hdom le_rfl
      _ = ∫⁻ x : X, ENNReal.ofReal ‖f (pJ (ψ x))‖ ∂dprod := by
        have h₁ : Measurable (fun q : Q[J] => ENNReal.ofReal ‖f q‖) :=
          ENNReal.measurable_ofReal.comp hf.norm
        have h₂ : Measurable (fun q : Q[fam.bot] => ENNReal.ofReal ‖f (pJ q)‖) := h₁.comp hprojMeas
        exact (lintegral_map h₁ hprojMeas).trans (hψ'.lintegral_comp h₂).symm
      _ ≤ ∫⁻ x : X, W x.1.2.1 * ENNReal.ofReal E ∂dprod :=
        lintegral_mono_ae (hs.mono fun x hx => by
          rw [← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hfbd x hx))
      _ = da Y * dM univ * ENNReal.ofReal E := by
        have hw₁ : Measurable (fun v : N × (B × M₁) => W v.2.1) :=
          hW.comp (measurable_fst.comp measurable_snd)
        change (∫⁻ x : X, W x.1.2.1 * ENNReal.ofReal E ∂(dn'.prod (da'.prod dm')).prod dK) = _
        rw [lintegral_prod_mul hw₁.aemeasurable
            (g := fun _ => ENNReal.ofReal E) measurable_const.aemeasurable,
          lintegral_const, measure_univ, mul_one]
        have hw₂ : Measurable (fun w : B × M₁ => W w.1) := hW.comp measurable_fst
        have h₁ : (∫⁻ v : N × (B × M₁), W v.2.1 ∂dn'.prod (da'.prod dm')) =
            1 * (∫⁻ w : B × M₁, W w.1 ∂da'.prod dm') := by
          simpa only [one_mul, lintegral_const, measure_univ] using
            (lintegral_prod_mul («μ» := dn') (ν := da'.prod dm') (f := fun _ => 1)
              measurable_const.aemeasurable hw₂.aemeasurable)
        have h₂ : (∫⁻ w : B × M₁, W w.1 ∂da'.prod dm') = da Y * dM univ := by
          simpa only [mul_one, lintegral_const, one_mul, hmvol, da', W,
            fam.lintegral_minimalHalfModulus_sq da Y hY] using
            (lintegral_prod_mul («μ» := da') (ν := dm') (g := fun _ => 1)
              hW.aemeasurable measurable_const.aemeasurable)
        rw [h₁, one_mul, h₂]
  let P := 1 + ‖eT (Tp + S - T₁)‖
  have hP : 0 ≤ P := by positivity
  have hYvol : da Y ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((A₀ * P) ^ d) :=
    (measure_mono (fam.splitHeightRegion_subset_of_shell J hK hT₁)).trans
      (hcvol T₁ (Tp + S - T₁)).2
  have hmfin : dM univ ≠ ∞ := measure_ne_top _ _
  have hInt' : (∫⁻ q in L, ENNReal.ofReal ‖f q‖ ∂(dQ[J])) ≤ ENNReal.ofReal (A * P ^ d * E) := by
    refine hInt.trans ?_
    rw [← ENNReal.ofReal_toReal hmfin]
    have hMle : ENNReal.ofReal (dM univ).toReal ≤ ENNReal.ofReal (1 + (dM univ).toReal) :=
      ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left zero_le_one)
    calc
      _ ≤ (↑c * ENNReal.ofReal ((A₀ * P) ^ d)) *
          ENNReal.ofReal (1 + (dM univ).toReal) * ENNReal.ofReal E := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ← ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) (pow_nonneg (mul_nonneg hA₀.le hP) _)),
          ← ENNReal.ofReal_mul (by positivity), mul_pow]
        congr 1
        dsimp [A]
        ring
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_norm f).mpr
    (hInt'.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  refine (norm_integral_le_lintegral_norm f).trans ?_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hInt').trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hA.le (pow_nonneg hP _)) hE))

end Langlands.Global.StandardParabolicFamily
