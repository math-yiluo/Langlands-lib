import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicCharacterParameterEquivalences
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Lebesgue coordinates for the split centre in wave packet pairings -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Module TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal ENNReal CompactlySupported

namespace Langlands.Global

open GroupScheme RealTorusSpace AdelicGroupPoints PositiveRealTorus RestrictionSplitCentre

local notation "Z(" F ", " G ")" => canonicalTorus F G
local notation "j₀(" F ", " G ")" => canonicalComponent F G
local notation "A₊(" F ", " G ")" => intrinsicSubgroup F (Z(F, G))
local notation "N₁(" F ", " G ")" => normOneSubgroup F G
local notation "Q₁(" F ", " G ")" => NormOneRationalQuotient F G
local notation "Γ₁(" F ", " G ")" => rationalNormOneSubgroup F G
local notation "Γ(" F ", " G ")" => AdelicGroupPoints.rationalSubgroup F G

section Chart

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

/-- The split-torus logarithm functional realizes the perfect pairing with real cocharacters. -/
private def cocharacterLogEquiv {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (hA : IsSplitTorus A.toGrp) : V A ≃ₗ[ℝ] RealCharacterDual F A.toGrp := by
  let := isPerfPair_of_isSplitTorus hA
  exact (pair A).flip.toPerfPair.trans realCharacterDualEquivParameterDual.symm

omit [NumberField F] in
private theorem cocharacterLogEquiv_apply {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (hA : IsSplitTorus A.toGrp) (w : V A) : cocharacterLogEquiv hA w = cocharacterFunctional w := rfl

private def positiveCentralChart [Mono i.hom.hom.left] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (f : Z(F, G) ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
    (hf : CommGroupScheme.groupHom f ≫ i = j₀(F, G))
    {m : ℕ} (b : Basis (Fin m) ℝ (relativeCentralDirections i))
    {I : Type} [Fintype I] (e : (Z(F, G)).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) :
    Multiplicative (Fin m → ℝ) ≃ₜ* A₊(F, G) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let hZ := isSplitComponent_canonicalComponent F G
  let L := b.equivFun.symm.trans
    ((hZ.cocharacterEquivCentralDirections rootAnnihilatorCentrality hT f hf).symm.trans
      (cocharacterLogEquiv hZ.1.1.1))
  let ψ := dualCoordinatesContinuousEquiv F (Z(F, G)) I e
  let l := (L.trans ψ.toLinearEquiv).toContinuousLinearEquiv.trans ψ.symm
  let lₘ : Multiplicative (Fin m → ℝ) ≃ₜ* Multiplicative (RealCharacterDual F (Z(F, G)).toGrp) :=
    { toFun := fun y => Multiplicative.ofAdd (l y.toAdd)
      invFun := fun y => Multiplicative.ofAdd (l.symm y.toAdd)
      left_inv := fun y => l.left_inv y.toAdd
      right_inv := fun y => l.right_inv y.toAdd
      map_mul' := fun y y' => l.map_add y.toAdd y'.toAdd
      continuous_toFun := l.continuous
      continuous_invFun := l.symm.continuous }
  exact lₘ.trans (positiveLogEquiv F (Z(F, G)) I e).symm

private theorem positiveCentralChart_log [Mono i.hom.hom.left] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (f : Z(F, G) ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
    (hf : CommGroupScheme.groupHom f ≫ i = j₀(F, G))
    {m : ℕ} (b : Basis (Fin m) ℝ (relativeCentralDirections i))
    {I : Type} [Fintype I] (e : (Z(F, G)).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (y : Fin m → ℝ) :
    characterLog F T.toGrp (map F (Z(F, G)).toGrp T.toGrp (CommGroupScheme.groupHom f)
      (positiveCentralChart hG hT f hf b e (Multiplicative.ofAdd y))) =
      cocharacterFunctional (∑ r, y r • (b r : V T)) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let hZ := isSplitComponent_canonicalComponent F G
  let w := (hZ.cocharacterEquivCentralDirections rootAnnihilatorCentrality hT f hf).symm (b.equivFun.symm y)
  have hlog : characterLog F (Z(F, G)).toGrp
      (positiveCentralChart hG hT f hf b e (Multiplicative.ofAdd y)) =
      cocharacterFunctional w := by
    rw [← positiveLogEquiv_apply F (Z(F, G)) I e]
    simp only [positiveCentralChart, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply]
    let ψ := dualCoordinatesContinuousEquiv F (Z(F, G)) I e
    change ψ.symm (ψ (cocharacterLogEquiv hZ.1.1.1 w)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, cocharacterLogEquiv_apply]
  rw [characterLog_map, hlog, ← cocharacterFunctional_cocharacterMapReal]
  congr 1
  calc
    cocharacterMapReal f w = (b.equivFun.symm y : V T) := by
      change (hZ.cocharacterEquivCentralDirections rootAnnihilatorCentrality hT f hf w : V T) = _
      rw [show hZ.cocharacterEquivCentralDirections rootAnnihilatorCentrality hT f hf w =
        b.equivFun.symm y from LinearEquiv.apply_symm_apply _ _]
    _ = _ := by rw [Basis.equivFun_symm_apply, Submodule.coe_sum]; rfl

end Chart

/-- Exact ambient and quotient product normalizations for Lebesgue coordinates in a basis of
    the real split central cocharacters. -/
def WavePacketCentreCoordinatesStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (_hi : IsMaximalSplitTorus i) (m : ℕ) (b : Basis (Fin m) ℝ (relativeCentralDirections i)),
    ∃ (f : Z(F, G) ⟶ T) (a : (Fin m → ℝ) → A₊(F, G)),
      CommGroupScheme.groupHom f ≫ i = j₀(F, G) ∧
      (∀ y, characterLog F T.toGrp
        (map F (Z(F, G)).toGrp T.toGrp (CommGroupScheme.groupHom f) (a y)) =
          cocharacterFunctional (∑ r, y r • (b r : V T))) ∧
      ∃ μ₁ : Measure (N₁(F, G)), μ₁.IsHaarMeasure ∧
        (∀ φ : C_c(AdelicGroupPoints F G, ℂ),
          (∫ g, φ g ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
            ∫ y, ∫ x, φ ((x : AdelicGroupPoints F G) *
              positivePointMap F G (Z(F, G)) (j₀(F, G)) (a y)) ∂μ₁) ∧
        ∃ H : ((Fin m → ℝ) × Q₁(F, G)) ≃ₜ RationalQuotient F G,
          (∀ y (q : Q₁(F, G)), H (y, q) = LeftCosetSpace.mk (Γ(F, G))
            ((q.out : N₁(F, G)).val * positivePointMap F G (Z(F, G)) (j₀(F, G)) (a y))) ∧
          MeasurePreserving H ((volume : Measure (Fin m → ℝ)).prod
            (LeftCosetSpace.discreteQuotientMeasure (Γ₁(F, G)) (isDiscrete_rationalNormOneSubgroup F G) μ₁))
            (rationalQuotientHaarMeasure F G)

/-- Transport the positive Haar scalar into the same norm-one measures at both levels. -/
theorem wavePacketCentreCoordinates : WavePacketCentreCoordinatesStatement := by
  intro F _ _ G _ _ hG T i _ hi m b
  let Z := Z(F, G)
  let j₀ := j₀(F, G)
  let Apos := A₊(F, G)
  let N₁ := N₁(F, G)
  let Γ₁ := Γ₁(F, G)
  let := hG.isAffineHom
  let hZ := isSplitComponent_canonicalComponent F G
  obtain ⟨f, hf, hfc, _⟩ := hZ.exists_commFactor_of_isMaximalSplitTorus hi
  let : IsClosedImmersion (CommGroupScheme.groupHom f).hom.hom.left := hfc
  let hT := hi.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := hZ.1.1.1
  let := Fintype.ofFinite I
  let hres := canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  let := canonical_finiteIndex F G hG
  let a := positiveCentralChart hG hT f hf b e
  let hc := hZ.1.2
  let μA := normalizedPositiveHaarMeasure F G Z j₀ hres I e hc
  let μN : Measure N₁ := Measure.haar
  let μQ := normOneRationalQuotientHaarMeasure F G
  let tag : (Fin m → ℝ) ≃ₜ Multiplicative (Fin m → ℝ) := Homeomorph.refl _
  let vol : Measure (Fin m → ℝ) := volume
  let volMul := Measure.map tag vol
  let : volMul.IsHaarMeasure := by
    refine
      { toIsMulLeftInvariant := ⟨?_⟩
        toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map vol tag
        toIsOpenPosMeasure := tag.continuous.isOpenPosMeasure_map tag.surjective }
    intro g
    have hmul : Measurable (fun x : Multiplicative (Fin m → ℝ) => g * x) :=
      (continuous_const.mul continuous_id).measurable
    have hadd : Measurable (fun x : Fin m → ℝ => g.toAdd + x) :=
      (continuous_const.add continuous_id).measurable
    change Measure.map (g * ·) (Measure.map tag vol) = Measure.map tag vol
    rw [Measure.map_map hmul tag.continuous.measurable]
    change Measure.map (tag ∘ (g.toAdd + ·)) vol = _
    rw [← Measure.map_map tag.continuous.measurable hadd]
    have hinv : Measure.map (fun x => g.toAdd + x) vol = vol :=
      Measure.IsAddLeftInvariant.map_add_left_eq_self g.toAdd
    rw [hinv]
  let := positiveIsTopologicalGroup F Z I e
  let : μA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G Z j₀ hres I e hc
  let μY := Measure.map a.symm μA
  let : μY.IsHaarMeasure := a.symm.isHaarMeasure_map μA
  let c : ℝ≥0 := Measure.haarScalarFactor μY volMul
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μY volMul).ne'
  have hμY : μY = (c : ℝ≥0∞) • volMul := Measure.isMulLeftInvariant_eq_smul μY volMul
  have ha : MeasurePreserving a ((c : ℝ≥0∞) • volMul) μA := by
    rw [← hμY]
    exact MeasurePreserving.symm a.symm.toMeasurableEquiv ⟨a.symm.continuous.measurable, rfl⟩
  have htag : MeasurePreserving tag ((c : ℝ≥0∞) • vol) ((c : ℝ≥0∞) • volMul) :=
    ⟨tag.continuous.measurable, Measure.map_smul _ tag.continuous.measurable.aemeasurable⟩
  let μ₁ : Measure N₁ := (c : ℝ≥0∞) • μN
  let μQ₁ := LeftCosetSpace.discreteQuotientMeasure Γ₁ (isDiscrete_rationalNormOneSubgroup F G) μ₁
  have hQ₁ : μQ₁ = (c : ℝ≥0∞) • μQ :=
    LeftCosetSpace.quotientMeasure_smul Γ₁ μN
      (LeftCosetSpace.fundamentalDomain Γ₁ (isDiscrete_rationalNormOneSubgroup F G)) _
  let a₀ : (Fin m → ℝ) ≃ₜ Apos := tag.trans a.toHomeomorph
  let L := normOneDecomposition F G Z j₀ hres I e
  let H := rationalQuotientDecomposition F G Z j₀ hres I e hc
  have hL : MeasurePreserving (L ∘ Prod.map a₀ id) ((volume : Measure (Fin m → ℝ)).prod μ₁)
      (Measure.haar : Measure (AdelicGroupPoints F G)) := by
    change MeasurePreserving _ (vol.prod ((c : ℝ≥0∞) • μN)) _
    rw [Measure.prod_smul_right, ← Measure.prod_smul_left]
    exact (measurePreserving_normOneDecomposition F G Z j₀ hres I e hc).comp
      ((ha.comp htag).prod (MeasurePreserving.id μN))
  have hH : MeasurePreserving (H ∘ Prod.map a₀ id) ((volume : Measure (Fin m → ℝ)).prod μQ₁)
      (rationalQuotientHaarMeasure F G) := by
    rw [hQ₁, Measure.prod_smul_right, ← Measure.prod_smul_left]
    exact (measurePreserving_rationalQuotientDecomposition F G Z j₀ hres I e hc).comp
      ((ha.comp htag).prod (MeasurePreserving.id μQ))
  refine ⟨f, a₀, hf, positiveCentralChart_log hG hT f hf b e, μ₁,
    Measure.IsHaarMeasure.smul μN (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top, ?_,
    (a₀.prodCongr (Homeomorph.refl _)).trans H, ?_, hH⟩
  · intro φ
    let L₀ := (a₀.prodCongr (Homeomorph.refl N₁)).trans L
    have hφ : Integrable φ (Measure.haar : Measure (AdelicGroupPoints F G)) :=
      φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    calc
      _ = ∫ z, (φ ∘ L ∘ Prod.map a₀ id) z ∂((volume : Measure (Fin m → ℝ)).prod μ₁) :=
        (hL.integral_comp L₀.toMeasurableEquiv.measurableEmbedding φ).symm
      _ = _ := by
        rw [integral_prod _ (hL.integrable_comp_of_integrable hφ)]
        apply integral_congr_ae
        filter_upwards with y
        apply integral_congr_ae
        filter_upwards with x
        change φ (positivePointMap F G Z j₀ (a₀ y) * x.val) =
          φ (x.val * positivePointMap F G Z j₀ (a₀ y))
        rw [(positivePointMap_commute F G Z j₀ hc (a₀ y) (x : AdelicGroupPoints F G)).eq]
  · intro y q
    change H (a₀ y, q) = _
    have hq : LeftCosetSpace.mk Γ₁ q.out = q := Quotient.out_eq q
    conv_lhs => rw [← hq]
    rw [rationalQuotientDecomposition_mk, (positivePointMap_commute F G Z j₀ hc (a₀ y) q.out.val).eq]

end Langlands.Global
