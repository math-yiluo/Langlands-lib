import Langlands.Global.AdelicEisensteinImaginaryHolomorphyReduction
import Langlands.Global.AdelicEisensteinJointRootHyperplaneReduction
import Langlands.Global.AdelicIntertwiningL2Estimate
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.Global.AdelicPositiveChamberProof
import Langlands.Global.AdelicWavePacketTranslationAnalyticReduction
import Langlands.Global.BoundedWavePacketReduction
import Langlands.Global.InducedInnerProductSesquilinearProof

/-! # Translation of symmetric wave packets from a one-packet norm bound -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Convolution

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "H" => AdelicGroupPoints F G
local notation "Q" => RationalQuotient F G
local notation "Γ" => rationalSubgroup F G
local notation "μQ" => rationalQuotientHaarMeasure F G

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Right convolution by a continuous compactly supported kernel preserves square
integrability on the rational quotient. -/
theorem memLp_rightConvolution_rationalQuotient (hG : IsConnectedReductive G)
    {Θ kernel : H → ℂ} (hΘc : Continuous Θ)
    (hΘinv : IsLeftInvariantUnder F G Γ Θ)
    (hΘ : MemLp (fun z : Q => Θ z.out) 2 μQ)
    (hk : Continuous kernel) (hks : HasCompactSupport kernel) :
    MemLp (fun z : Q => rightConvolution F G kernel Θ z.out) 2 μQ := by
  let f : Q → ℂ := LeftCosetSpace.lift Γ Θ (fun gamma x => hΘinv gamma gamma.property x)
  have hrep (z : Q) : f z = Θ z.out := by
    change f z = f (LeftCosetSpace.mk Γ z.out)
    exact congrArg f (Quotient.out_eq z).symm
  have hfc : Continuous f := LeftCosetSpace.continuous_lift Γ Θ _ hΘc
  have hfL : MemLp f 2 μQ :=
    hΘ.ae_eq (Filter.Eventually.of_forall fun z => (hrep z).symm)
  let translated (h : H) (z : Q) := f (LeftCosetSpace.rightTranslate Γ h z)
  have hq : Continuous (fun zh : Q × H => LeftCosetSpace.rightTranslate Γ zh.2 zh.1) :=
    continuous_rationalQuotient_rightTranslate_uncurry (F := F) (G := G)
  have hqm : Measurable (fun zh : Q × H => LeftCosetSpace.rightTranslate Γ zh.2 zh.1) :=
    hq.measurable
  have hfm : Measurable f := hfc.measurable
  have hmeas : Measurable (fun hz : H × Q => translated hz.1 hz.2) := by
    have heq : (fun hz : H × Q => translated hz.1 hz.2) =
        (f ∘ (fun zh : Q × H => LeftCosetSpace.rightTranslate Γ zh.2 zh.1)) ∘ Prod.swap :=
      funext fun ⟨h, z⟩ => rfl
    rw [heq]
    exact (hfm.comp hqm).comp measurable_swap
  have hB : (∫⁻ z, ‖f z‖ₑ ^ 2 ∂μQ) ≠ ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ENNReal) ≠ 0) (by simp) hfL.eLpNorm_lt_top).ne
  have hsection (h : H) : (∫⁻ z, ‖translated h z‖ₑ ^ 2 ∂μQ) ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μQ :=
    le_of_eq ((measurePreserving_rationalQuotient_rightTranslate hG h).lintegral_comp
      (hfc.measurable.enorm.pow_const 2))
  have hSquare := integrable_sq_norm_kernelIntegral («μ» := (Measure.haar : Measure H)) hk.measurable
    (hk.integrable_of_hasCompactSupport hks) hmeas hB hsection
  have hIntegrand : Measurable
      (Function.uncurry fun (h : H) (z : Q) => kernel h * translated h z) :=
    (hk.measurable.comp measurable_fst).mul hmeas
  have hIntegral : StronglyMeasurable (fun z : Q => ∫ h, kernel h * translated h z
      ∂(Measure.haar : Measure H)) := hIntegrand.stronglyMeasurable.integral_prod_left
  have hconv : MemLp (fun z : Q => ∫ h, kernel h * translated h z
      ∂(Measure.haar : Measure H)) 2 μQ :=
    (memLp_two_iff_integrable_sq_norm hIntegral.aestronglyMeasurable).2 hSquare
  refine hconv.ae_eq (Filter.Eventually.of_forall fun z => ?_)
  unfold rightConvolution
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun h => ?_
  have hpoint : translated h z = Θ (z.out * h) := by
    change f (LeftCosetSpace.rightTranslate Γ h z) = Θ (z.out * h)
    rw [rationalQuotient_rightTranslate_eq_mk_out_mul]
    rfl
  exact congrArg (kernel h * ·) hpoint

end Convolution

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Square integrability of each packet follows from the local norm bound. Convolution
stability and test-function separation then give the symmetric translation approximation. -/
theorem wavePacketTranslation_of_convolution_of_localNormBound
    (hNorm : LocalWavePacketNormBoundStatement)
    (hConv : SymmetricWavePacketConvolutionStatement) : WavePacketTranslationStatement := by
  intro F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    hG hUR hMul hπ K hK N d rho hsmooth hcalc hKm hrho μM _ hμM n e β hβ T _ w cw hW hinj hsurj
    hw nP μG Mop hMop Φ k v c E D hΦ hE y ε hε
  let : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i) (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  let Θ := wavePacketSumOnGroup e nP c E
  have hData := hConv F G I P M U A p iU l a r hA hT π hG hUR hMul hπ
    K hK rho hsmooth hcalc hKm hrho μM hμM n e β hβ T w cw hW hinj hsurj hw Mop hMop
    Φ k v c E D hΦ hE
  obtain ⟨hΘc, hΘinv, hΘconv⟩ := hData
  have hComponent (i : I) : MemLp (fun z : RationalQuotient F G =>
      ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) z.out
        ∂(spectralMeasure (n i))) 2 μG := by
    let S := ⋃ j, tsupport (c i j)
    have hS : IsCompact S := isCompact_iUnion fun j => (hΦ.2.1 i j).2
    have hcS (j : Fin (k i)) (x : Fin (n i) → ℝ) (hx : x ∉ S) : c i j x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (mem_iUnion.2 ⟨j, h⟩)
    exact (hNorm F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i)
      (hA i) (hT i) (π i) hG (hUR i) (hπ i) K (hK i) rho hsmooth hcalc hKm hrho
      (μM i) (hμM i) (e i) (β i) (hβ i).1 (hβ i).2.1 (hβ i).2.2.2 (k i) (v i) (c i) S
      (E i) (D i) (hΦ.1 i) hS (fun j => ⟨(hΦ.2.1 i j).1, hcS j⟩)
      (fun _ ⟨x, _, hx⟩ => hx ▸ (hE i).1 ⟨e i x, rfl⟩) (hE i).2.1 (hE i).2.2).2.1
  have hΘL : MemLp (fun z : RationalQuotient F G => Θ z.out) 2 μG := by
    change MemLp (fun z : RationalQuotient F G => ∑ i, (nP i : ℂ)⁻¹ *
      ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) z.out
        ∂(spectralMeasure (n i))) 2 μG
    exact memLp_finsetSum Finset.univ fun i _ => (hComponent i).const_mul ((nP i : ℂ)⁻¹)
  have happ := leftFiniteConvolutionApproximation rightTranslationTestFunctionSeparation
    F G hG K hKm Θ hΘc hΘinv hΘL
    (fun kernel hk => memLp_rightConvolution_rationalQuotient (F := F) (G := G)
      (Θ := Θ) (kernel := kernel) hG hΘc hΘinv hΘL hk.1 hk.2.1)
    y ε hε
  obtain ⟨kernel, hker, herr⟩ := happ
  have hNew := hΘconv kernel hker
  obtain ⟨Ψ, k', v', c', E', D', hΨ, hE', hEq⟩ := hNew
  refine ⟨Ψ, k', v', c', E', D', hΨ, hE', ?_⟩
  have hfun : (fun z : RationalQuotient F G => wavePacketSum e nP c E
      (LeftCosetSpace.mk (rationalSubgroup F G) (z.out * y)) - wavePacketSum e nP c' E' z) =
        fun z => Θ (z.out * y) - rightConvolution F G kernel Θ z.out := by
    funext z
    change Θ (LeftCosetSpace.mk (rationalSubgroup F G) (z.out * y)).out -
      wavePacketSumOnGroup e nP c' E' z.out = Θ (z.out * y) - rightConvolution F G kernel Θ z.out
    rw [LeftCosetSpace.out_mk_of_invariant _ Θ hΘinv]
    exact congrArg (fun q : ℂ => Θ (z.out * y) - q) (congrFun hEq z.out).symm
  rw [hfun]
  exact herr

/-- The local norm bound supplies both square integrability for translation and the bound
used to prove imaginary-axis holomorphy from root hyperplanes. -/
def WavePacketTranslationNormBoundReductionStatement : Prop :=
  NormalizedConvolutionImaginarySpanStatement →
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinRootHyperplaneStatement.{0} →
  IntertwiningSquareIntegrableExpansionStatement → LocalWavePacketNormBoundStatement →
  WavePacketTranslationStatement

theorem wavePacketTranslationNormBoundReduction : WavePacketTranslationNormBoundReductionStatement := by
  intro hSpan hMero hRoot hExp hNorm
  have hHolo := eisensteinImaginaryAxisHolomorphyReduction
    (eisensteinJointRootHyperplaneReduction positiveChamberNonempty hMero hRoot)
    (boundedWavePacketNormBound_of_local hNorm inducedInnerProductSesquilinear)
    iwasawaCompatibleMeasureExistence
  exact wavePacketTranslation_of_convolution_of_localNormBound hNorm
    (symmetricWavePacketConvolution_of_finiteExpansions
      (normalizedConvolutionFiniteSpan_of_imaginarySpan hSpan)
      (imaginaryEisensteinConvolution_of_meromorphicContinuation hMero)
      hExp (eisensteinImaginaryContinuationBridge hMero hHolo eisensteinAbsoluteConvergence))

end Langlands.Global
