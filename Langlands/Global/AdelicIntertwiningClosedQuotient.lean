import Langlands.Global.AdelicIntertwiningStabilizer
import Langlands.Global.LeftCosetClosedQuotientMeasure
import Langlands.Global.DiscreteLeftCosetMeasureTransport
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.LeftQuotientProduct

/-! # The closed-quotient measure of the adelic intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology TopologicalSpace
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
local notation "Γ" => intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
local notation "H" => intertwiningAdelicStabilizer p iU j w

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine V.X.left]
  [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom] [IsClosedImmersion j.hom.hom.left] in
/-- The rational subgroup lies in the closed stabilizer. -/
theorem intertwiningRationalSubgroup_le_adelicStabilizer : Γ ≤ H := by
  rw [intertwiningRationalSubgroup_eq_rational_inf_stabilizer]
  exact inf_le_right

/-- The actual rational-quotient measure pushes forward to a measure on the
full stabilizer quotient with the stated automorphism change of variables. -/
def IntertwiningClosedQuotientStatement : Prop :=
  ∀ (hi : IsClosedSubgroup (iU ≫ p)), Smooth V.X.hom → ConnectedSpace V.X.left →
    ∀ (hVu : IsUnipotent V),
    let hj : IsClosedSubgroup j := (inferInstance : IsClosedImmersion j.hom.hom.left)
    let hV := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    let hH := (intertwiningStabilizer p iU j w hj hi hVu).1
    haveI : LocallyCompactSpace Vₐ := hV.locallyCompactSpace
    haveI : LocallyCompactSpace H := hH.locallyCompactSpace
    ∃ ν : Measure (LeftCosetSpace H),
      MeasurePreserving
        (LeftCosetSpace.projectionOfLE (intertwiningRationalSubgroup_le_adelicStabilizer p iU j w))
        (intertwiningMeasure F p iU j (innerAdelicPoint F G w)) ν ∧
      ∀ (α : Vₐ ≃ₜ* Vₐ) (hα : ∀ x : Vₐ, α x ∈ H ↔ x ∈ H),
        Measure.map (quotientAutomorphism H α hα) ν =
          ((mulEquivHaarChar (subgroupAutomorphism H α hα) / mulEquivHaarChar α : ℝ≥0) : ℝ≥0∞) • ν ∧
        ∀ f : LeftCosetSpace H → ℂ,
          (∫ q, f ((quotientAutomorphism H α hα).symm q) ∂ν) =
            (((mulEquivHaarChar α / mulEquivHaarChar (subgroupAutomorphism H α hα) : ℝ≥0) : ℝ) : ℂ) *
              ∫ q, f q ∂ν

private theorem normalizedHaarMeasure_fundamentalDomain
    (W : SubgroupFunctor G)
    [hClosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G W : Set (AdelicGroupPoints F G))]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G W)] :
    AdelicSubgroupPoints.normalizedHaarMeasure F G W
      (LeftCosetSpace.fundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F G W)
        (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G W)) = 1 := by
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G W) := hClosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G W) := hClosed.polishSpace
  have h := (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G W).measure_univ
  rw [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
    AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, Measure.smul_apply,
    LeftCosetSpace.quotientMeasure_univ] at h
  rw [AdelicSubgroupPoints.normalizedHaarMeasure, Measure.smul_apply]
  exact h

private theorem normalizedHaarMeasure_isHaar
    (W : SubgroupFunctor G)
    [hClosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G W : Set (AdelicGroupPoints F G))]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G W)] :
    (AdelicSubgroupPoints.normalizedHaarMeasure F G W).IsHaarMeasure := by
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G W) := hClosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G W) := hClosed.polishSpace
  exact Measure.IsHaarMeasure.smul _ (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G W)
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G W)

omit [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom] in
/-- The actual intertwining measure is locally finite on the rational quotient. -/
theorem isLocallyFiniteMeasure_intertwiningMeasure
    (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left) (hVu : IsUnipotent V) :
    IsLocallyFiniteMeasure (intertwiningMeasure F p iU j (innerAdelicPoint F G w)) := by
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  let : PolishSpace Vₐ := hClosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hVs hVc hVu
  let : (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)).IsHaarMeasure :=
    normalizedHaarMeasure_isHaar (SubgroupFunctor.range j)
  exact LeftCosetSpace.isLocallyFiniteMeasure_discreteQuotientMeasure Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
    (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j))

theorem intertwiningClosedQuotient : IntertwiningClosedQuotientStatement p iU j w := by
  intro hi hVs hVc hVu
  let hVclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hVclosed
  let : LocallyCompactSpace Vₐ := hVclosed.locallyCompactSpace
  let : PolishSpace Vₐ := hVclosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hVs hVc hVu
  let k := intertwiningStabilizerHom p iU j w
  let W := SubgroupFunctor.range k
  have hj : IsClosedSubgroup j := (inferInstance : IsClosedImmersion j.hom.hom.left)
  obtain ⟨hk, -, -, -⟩ := intertwiningStabilizer_geometry p iU j w hj hi hVu
  obtain ⟨hH, ⟨hComp⟩, hRat⟩ := intertwiningStabilizer p iU j w hj hi hVu
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G W) := hComp
  let : IsClosedImmersion k.hom.hom.left := hk
  let : IsAffine (IntertwiningStabilizer p iU j w).X.left := isAffine_of_isAffineHom k.hom.hom.left
  let Wₐ := AdelicSubgroupPoints.adelicPoints F G W
  let hW := AdelicSubgroupPoints.isClosed_adelicPoints_range F G k
  let : IsClosed (Wₐ : Set (AdelicGroupPoints F G)) := hW
  let : LocallyCompactSpace Wₐ := hW.locallyCompactSpace
  let : PolishSpace Wₐ := hW.polishSpace
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : PolishSpace H := hH.polishSpace
  let : SecondCountableTopology H := secondCountableTopology_induced _ Vₐ Subtype.val
  let : BorelSpace (LeftCosetSpace H) := by
    let : T2Space (LeftCosetSpace H) := leftQuotient_t2Space H hH
    let : SecondCountableTopology (LeftCosetSpace H) :=
      (leftQuotient_isOpenQuotientMap H).secondCountableTopology
    exact LeftCosetSpace.quotient_borelSpace H
  let e := intertwiningStabilizerEquiv p iU j w
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G W
  let Λ := (Γ).comap (H).subtype
  let hΔ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G W
  let hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have hΛ : IsDiscrete (Λ : Set H) :=
    hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  have he (x : Wₐ) : e x ∈ Λ ↔ x ∈ Δ := by
    change e x ∈ ((Γ).comap (H).subtype) ↔ x ∈ Δ
    rw [← hRat, Subgroup.mem_map_equiv]
    exact Iff.rfl
  let μW := AdelicSubgroupPoints.normalizedHaarMeasure F G W
  let μV := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  let μH : Measure H := Measure.map e μW
  let : IsHaarMeasure μW := normalizedHaarMeasure_isHaar W
  let : IsHaarMeasure μV := normalizedHaarMeasure_isHaar (SubgroupFunctor.range j)
  let : IsHaarMeasure μH := e.isHaarMeasure_map μW
  let : (Measure.haar : Measure Wₐ).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G W
  let : (Measure.haar : Measure Vₐ).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G (SubgroupFunctor.range j)
  let : μW.IsMulRightInvariant := by dsimp only [μW, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let : μV.IsMulRightInvariant := by dsimp only [μV, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let : μH.IsMulRightInvariant := isMulRightInvariant_of_continuousMulEquiv e.symm μW μH
  let : μW.Regular := by
    exact Measure.Regular.smul (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G W)
  let : μV.Regular := by
    exact Measure.Regular.smul (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G (SubgroupFunctor.range j))
  let : μH.Regular := Measure.Regular.map e.toHomeomorph
  let hMe : MeasurePreserving e μW μH := ⟨e.continuous.measurable, rfl⟩
  have hQuot := LeftCosetSpace.measurePreserving_discreteQuotientMeasure e Δ Λ he hΔ hΛ μW μH hMe
  have hMass : μH (LeftCosetSpace.fundamentalDomain Λ hΛ) = 1 := by
    have h := congrArg (fun ν : Measure (LeftCosetSpace Λ) => ν univ) hQuot.map_eq
    rw [Measure.map_apply hQuot.measurable MeasurableSet.univ, preimage_univ,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ, LeftCosetSpace.quotientMeasure_univ] at h
    exact h.symm.trans (normalizedHaarMeasure_fundamentalDomain W)
  obtain ⟨ν, hν⟩ := compatibleMeasureExists H hH μV μH
  refine ⟨ν, ?_, ?_⟩
  · exact LeftCosetSpace.measurePreserving_projectionOfLE
      (intertwiningRationalSubgroup_le_adelicStabilizer p iU j w) hΓ μV μH ν
      hH hν _ (LeftCosetSpace.isFundamentalDomain Λ hΛ μH) hMass
  · intro α hα
    exact compatibleQuotientAutomorphismScaling H hH μV μH ν hν α hα

/-- The closed-quotient change of variables moves a left translate in the
external argument to the input function and preserves integrability. -/
def IntertwiningIntegralConjugationStatement : Prop :=
  ∀ (hi : IsClosedSubgroup (iU ≫ p)), Smooth V.X.hom → ConnectedSpace V.X.left →
    ∀ (hVu : IsUnipotent V),
    let hj : IsClosedSubgroup j := (inferInstance : IsClosedImmersion j.hom.hom.left)
    let hV := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    let hH := (intertwiningStabilizer p iU j w hj hi hVu).1
    haveI : LocallyCompactSpace Vₐ := hV.locallyCompactSpace
    haveI : LocallyCompactSpace H := hH.locallyCompactSpace
    ∀ (a : AdelicGroupPoints F G) (α : Vₐ ≃ₜ* Vₐ) (hα : ∀ x : Vₐ, α x ∈ H ↔ x ∈ H),
      (∀ x : Vₐ, (α x).val = a * x.val * a⁻¹) →
      ∀ [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
        (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
        (φ : AdelicGroupPoints F G → ℂ),
        Continuous φ → IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ →
        IsUnipotent U → ∀ lam : ComplexCharacterParameter F P, ∀ g : AdelicGroupPoints F G,
          let wA := innerAdelicPoint F G w
          let measure := intertwiningMeasure F p iU j wA
          let moved := fun q : LeftCosetSpace Γ => hK.parameterTwist φ lam
            (wA⁻¹ * a * (Quotient.out q : Vₐ).val * g)
          hK.intertwiningIntegral iU j w φ lam (a * g) =
            (((mulEquivHaarChar α / mulEquivHaarChar (subgroupAutomorphism H α hα) : ℝ≥0) : ℝ) : ℂ) *
              (∫ q, moved q ∂measure) ∧
          (Integrable (hK.intertwiningIntegrand iU j w φ lam (a * g)) measure ↔
            Integrable moved measure) ∧
          (∫⁻ q, ‖moved q‖ₑ ∂measure) =
            ((mulEquivHaarChar (subgroupAutomorphism H α hα) / mulEquivHaarChar α : ℝ≥0) : ℝ≥0∞) *
              (∫⁻ q, ‖hK.intertwiningIntegrand iU j w φ lam (a * g) q‖ₑ ∂measure)

theorem intertwiningIntegralConjugation : IntertwiningIntegralConjugationStatement p iU j w := by
  intro hi hVs hVc hVu hj hV hH a α hα hαact _ _ K hK φ hφc hφ hU lam g wA measure moved
  let : LocallyCompactSpace Vₐ := hV.locallyCompactSpace
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let f := hK.parameterTwist φ lam
  have hf : Continuous f := hK.continuous_parameterTwist hφc lam
  have hInv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) f := by
    rintro _ ⟨u, rfl⟩ z
    have hu : map F U G (iU ≫ p) u ∈ parabolicUnipotentImage F p iU := ⟨u, rfl⟩
    change hK.parameterTwist φ lam (map F U G (iU ≫ p) u * z) = hK.parameterTwist φ lam z
    unfold IsIwasawaCompact.parameterTwist
    rw [hφ _ hu, hK.heightPower_unipotent_mul hU]
  have hαinv (x : Vₐ) : (α.symm x).val = a⁻¹ * x.val * a := by
    conv_rhs => rw [← show (α (α.symm x)).val = x.val from congrArg Subtype.val (α.apply_symm_apply x)]
    rw [hαact]
    group
  let lhs := fun x : Vₐ => f (wA⁻¹ * x.val * (a * g))
  let rhs := fun x : Vₐ => f (wA⁻¹ * a * x.val * g)
  have hComp (x : Vₐ) : lhs x = rhs (α.symm x) := by
    dsimp only [lhs, rhs]
    rw [hαinv]
    congr 1
    group
  have hInvL (z : H) (x : Vₐ) : lhs (z.val * x) = lhs x := by
    have hz : wA⁻¹ * z.val.val * wA ∈ parabolicUnipotentImage F p iU :=
      (mem_intertwiningAdelicStabilizer_iff p iU j w z.val).mp z.property
    dsimp only [lhs, Subgroup.coe_mul]
    rw [show wA⁻¹ * (z.val.val * x.val) * (a * g) =
      (wA⁻¹ * z.val.val * wA) * (wA⁻¹ * x.val * (a * g)) by group, hInv _ hz]
  have hInvR (z : H) (x : Vₐ) : rhs (z.val * x) = rhs x := by
    have hz : α z.val ∈ H := (hα _).mpr z.property
    have hu : wA⁻¹ * (a * z.val.val * a⁻¹) * wA ∈ parabolicUnipotentImage F p iU := by
      rw [← hαact]
      exact (mem_intertwiningAdelicStabilizer_iff p iU j w (α z.val)).mp hz
    dsimp only [rhs, Subgroup.coe_mul]
    rw [show wA⁻¹ * a * (z.val.val * x.val) * g =
      (wA⁻¹ * (a * z.val.val * a⁻¹) * wA) * (wA⁻¹ * a * x.val * g) by group, hInv _ hu]
  let L := LeftCosetSpace.lift H lhs hInvL
  let R := LeftCosetSpace.lift H rhs hInvR
  have hVclosed : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hV
  let : PolishSpace Vₐ := hVclosed.polishSpace
  let : BorelSpace (LeftCosetSpace H) := by
    let : T2Space (LeftCosetSpace H) := leftQuotient_t2Space H hH
    let : SecondCountableTopology (LeftCosetSpace H) :=
      (leftQuotient_isOpenQuotientMap H).secondCountableTopology
    exact LeftCosetSpace.quotient_borelSpace H
  have hLc : Continuous L := LeftCosetSpace.continuous_lift H lhs hInvL
    (hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hRc : Continuous R := LeftCosetSpace.continuous_lift H rhs hInvR
    (hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
  obtain ⟨ν, hν, hScale⟩ := intertwiningClosedQuotient p iU j w hi hVs hVc hVu
  let proj := LeftCosetSpace.projectionOfLE (intertwiningRationalSubgroup_le_adelicStabilizer p iU j w)
  have hL (q : LeftCosetSpace Γ) : L (proj q) = lhs (Quotient.out q) := by
    exact congrArg (L ∘ proj) (Quotient.out_eq q).symm
  have hR (q : LeftCosetSpace Γ) : R (proj q) = rhs (Quotient.out q) := by
    exact congrArg (R ∘ proj) (Quotient.out_eq q).symm
  have hLC (q : LeftCosetSpace H) : L q = R ((quotientAutomorphism H α hα).symm q) := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective H q
    exact hComp x
  have hMap (T : LeftCosetSpace H → ℂ) (hT : Continuous T) :
      (∫ q, T (proj q) ∂measure) = ∫ q, T q ∂ν := by
    rw [← hν.map_eq]
    exact (integral_map hν.measurable.aemeasurable hT.aestronglyMeasurable).symm
  let β := quotientAutomorphism H α hα
  have hLR (x : LeftCosetSpace H) : L (β x) = R x := by
    rw [hLC, β.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · change (∫ q, lhs (Quotient.out q) ∂measure) = _ * ∫ q, rhs (Quotient.out q) ∂measure
    simp_rw [← hL, ← hR]
    rw [hMap L hLc, hMap R hRc]
    simp_rw [hLC]
    exact (hScale α hα).2 R
  · change (Integrable (fun q => lhs (Quotient.out q)) measure ↔
      Integrable (fun q => rhs (Quotient.out q)) measure)
    simp_rw [← hL, ← hR]
    have hMapInt (T : LeftCosetSpace H → ℂ) (hT : Continuous T) :
        Integrable (fun q => T (proj q)) measure ↔ Integrable T ν := by
      rw [← hν.map_eq]
      exact (integrable_map_measure hT.aestronglyMeasurable hν.measurable.aemeasurable).symm
    rw [hMapInt L hLc, hMapInt R hRc]
    have hMapL : Integrable L (Measure.map β ν) ↔ Integrable (fun q => L (β q)) ν :=
      integrable_map_measure hLc.aestronglyMeasurable β.continuous.measurable.aemeasurable
    have hpos : mulEquivHaarChar (subgroupAutomorphism H α hα) / mulEquivHaarChar α ≠ 0 :=
      div_ne_zero (mulEquivHaarChar_pos _).ne' (mulEquivHaarChar_pos _).ne'
    rw [show Measure.map β ν = _ from (hScale α hα).1,
      integrable_smul_measure (ENNReal.coe_ne_zero.mpr hpos) ENNReal.coe_ne_top] at hMapL
    simpa only [hLR] using hMapL
  · change (∫⁻ q, ‖rhs (Quotient.out q)‖ₑ ∂measure) =
      _ * (∫⁻ q, ‖lhs (Quotient.out q)‖ₑ ∂measure)
    simp_rw [← hL, ← hR]
    have hLower (T : LeftCosetSpace H → ℂ) (hT : Continuous T) :
        (∫⁻ q, ‖T (proj q)‖ₑ ∂measure) = ∫⁻ q, ‖T q‖ₑ ∂ν := by
      rw [← hν.map_eq]
      exact (lintegral_map hT.measurable.enorm hν.measurable).symm
    rw [hLower L hLc, hLower R hRc]
    calc
      _ = ∫⁻ q, ‖L (β q)‖ₑ ∂ν := lintegral_congr fun q => congrArg _ (hLR q).symm
      _ = ∫⁻ q, ‖L q‖ₑ ∂Measure.map β ν :=
        (lintegral_map hLc.measurable.enorm β.continuous.measurable).symm
      _ = _ := by rw [show Measure.map β ν = _ from (hScale α hα).1,
          lintegral_smul_measure, smul_eq_mul]

end Langlands.Global.AdelicGroupPoints
