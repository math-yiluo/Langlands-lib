import Langlands.TraceFormula.AdelicFixedLevelSmoothing
import Langlands.Analysis.TraceClassIdealProof

/-! # Trace class for fixed-level adelic smoothing tensors -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme Langlands.Global.PositiveRealTorus
open Langlands.Global.AdelicGroupPoints
open Langlands.Analysis Langlands.Analysis.OperatorIdeals Langlands.Hecke
open Langlands.Automorphic.GroupSchemeFunctions

universe u

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A" => AdelicGroupPoints F G

private local instance finiteMeasurableSpace : MeasurableSpace Af := borel _
private local instance finiteBorelSpace : BorelSpace Af := ⟨rfl⟩

variable (mInf : Measure (InfiniteAdelicGroupPoints F G)) [mInf.IsHaarMeasure]
  (mFin : Measure (FiniteAdelicGroupPoints F G)) [mFin.IsHaarMeasure]
  (m : Measure (AdelicGroupPoints F G))
  (hProduct : MeasurePreserving (AdelicGroupPoints.split F G).symm (mInf.prod mFin) m)
  {f : InfiniteAdelicGroupPoints F G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hz : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
  (K : OpenSubgroup (FiniteAdelicGroupPoints F G))
  (hK : IsCompact (K : Set (FiniteAdelicGroupPoints F G)))

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hz
local notation "R" => adelicSmoothingAction F G mInf mFin m hProduct hf hs hPD hG Z i hi I e hz

/-- Trace class of the smoothing operator with the normalized level indicator implies
trace class of every smoothing tensor with the same infinite function and a finite test
invariant under the level on both sides. -/
def AdelicSmoothingTraceClassStatement (g : HeckeAlgebra mFin) : Prop :=
  (∀ a : K, ∀ x, g ((a : Af) * x) = g x) →
  (∀ a : K, ∀ x, g (x * (a : Af)) = g x) →
  IsTraceClass (R (HeckeAlgebra.normalizedIndicator mFin K hK) 0) →
  ∀ k : ℕ, IsTraceClass (R g k)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem adelicSmoothingTraceClass (g : HeckeAlgebra mFin) :
    AdelicSmoothingTraceClassStatement F G mInf mFin m hProduct hf hs hPD hG Z i hi I e hz
      K hK g := by
  intro hgLeft hgRight hLevel k
  let q := HeckeAlgebra.normalizedIndicator mFin K hK
  let π := fullAEL2CuspidalBoundedRightAction F G hPD hG Z i hi I e hz
  let jInf := AdelicGroupPoints.ofInfinite F G
  let jFin := AdelicGroupPoints.ofFinite F G
  let πFin := π.comp jFin.toMonoidHom
  have hπNorm : ∀ a x, ‖π a x‖ = ‖x‖ :=
    norm_fullAEL2CuspidalBoundedRightAction F G hPD hG Z i hi I e hz
  have hπMeas := fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG Z i hi I e hz m
  have hπFinNorm : ∀ b x, ‖πFin b x‖ = ‖x‖ := fun b x => hπNorm (jFin b) x
  have hπFinMeas (x : S) : AEStronglyMeasurable (fun b => πFin b x) mFin := by
    have : SecondCountableTopologyEither Af S := secondCountableTopologyEither_of_left _ _
    exact ((fullAEL2CuspidalOrbitMap F G hPD hG Z i hi I e hz x).continuous.comp
      jFin.continuous).stronglyMeasurable.aestronglyMeasurable
  have hFinInt (g' : HeckeAlgebra mFin) : Integrable g' mFin :=
    HarmonicAnalysis.SchwartzBruhat.integrable (HeckeAlgebra.toTestFunction mFin g') mFin
  let B (g' : HeckeAlgebra mFin) :=
    integratedIsometricAction mFin πFin hπFinNorm hπFinMeas g' (hFinInt g')
  have hMul : B (q * g) = B q * B g := by
    obtain ⟨_, h⟩ := integratedActionConvolution Af S mFin πFin hπFinNorm hπFinMeas q g
      (hFinInt q) (hFinInt g)
    exact h
  have hHecke : q * g = g :=
    HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant mFin K hK g hgLeft
  have hFixed : B q * B g = B g := by
    rw [← hMul, hHecke]
  have hSep (g' : HeckeAlgebra mFin) (x : S) :
      R g' 0 x = ∫ a, f a • π (jInf a) (B g' x) ∂mInf := by
    let splitInv := (AdelicGroupPoints.split F G).symm
    have hEmb : MeasurableEmbedding splitInv := splitInv.toHomeomorph.measurableEmbedding
    let weight := adelicSmoothingWeight F G mInf f g' 0
    let kernel : A → S := fun a => weight a • π a x
    have hWeight := adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hs g' 0
    have hIntegral : Integrable kernel m :=
      isometricActionIntegrand_integrable m π hπNorm hπMeas weight hWeight x
    change (∫ a, kernel a ∂m) = _
    rw [← hProduct.integral_comp hEmb kernel]
    change (∫ z, (kernel ∘ splitInv) z ∂(mInf.prod mFin)) = _
    rw [integral_prod _ ((hProduct.integrable_comp_emb hEmb).2 hIntegral)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    have hKernel (b : Af) : kernel (splitInv (a, b)) =
        f a • π (jInf a) (g' b • πFin b x) := by
      change adelicSmoothingWeight F G mInf f g' 0 (AdelicGroupPoints.pair F G a b) •
        π (AdelicGroupPoints.pair F G a b) x = _
      have hPair : jInf a * jFin b = AdelicGroupPoints.pair F G a b := by
        rw [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.ofFinite_eq_pair,
          AdelicGroupPoints.pair_mul, mul_one, one_mul]
      rw [adelicSmoothingWeight, AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair,
        positiveConvolutionPower_zero, ← hPair, map_mul, mul_apply_eq_comp, mul_smul, map_smul]
      rfl
    change (∫ b, kernel (splitInv (a, b)) ∂mFin) = _
    simp only [hKernel]
    rw [integral_smul, ContinuousLinearMap.integral_comp_comm _
      (isometricActionIntegrand_integrable mFin πFin hπFinNorm hπFinMeas g' (hFinInt g') x)]
    rfl
  have hFactor : R g 0 = (R q 0).comp (B g) := by
    ext1 x
    rw [ContinuousLinearMap.comp_apply, hSep g x, hSep q (B g x)]
    have hFix := congrArg (fun C : S →L[ℂ] S => C x) hFixed
    change B q (B g x) = B g x at hFix
    rw [hFix]
  have hZero : IsTraceClass (R g 0) := by
    rw [hFactor]
    exact isTraceClass_precomp (R q 0) (B g) hLevel
  have hPower : R g 0 * (R q 0) ^ k = R g k := by
    simpa only [mul_one] using adelicFixedLevelSmoothingPowers F G mInf mFin m hProduct hf hs
      hPD hG Z i hi I e hz K hK g hgRight 1 (Commute.one_left (R q 0)) k
  rw [← hPower]
  exact isTraceClass_precomp (R g 0) ((R q 0) ^ k) hZero

end Langlands.TraceFormula
