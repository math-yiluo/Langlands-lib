import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.TraceFormula.FixedLevelSmoothingPowers
import Langlands.TraceFormula.GroupSchemeTwistedCuspidalSpectralExpansionProof

/-! # Fixed-level smoothing on the actual cuspidal Hilbert space -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.Global.PositiveRealTorus
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis Langlands.Hecke

universe u

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A" => AdelicGroupPoints F G

private local instance finiteAdelicMeasurableSpace : MeasurableSpace Af := borel _
private local instance finiteAdelicBorelSpace : BorelSpace Af := ⟨rfl⟩

/-- The infinite convolution power tensored with a fixed finite test,
pulled back to the original full adelic point group. -/
def adelicSmoothingWeight (mInf : Measure A∞) (f : A∞ → ℂ) (g : Af → ℂ)
    (k : ℕ) (x : A) : ℂ :=
  positiveConvolutionPower mInf f k (AdelicGroupPoints.infinite F G x) *
    g (AdelicGroupPoints.finite F G x)

variable (mInf : Measure (InfiniteAdelicGroupPoints F G)) [mInf.IsHaarMeasure]
  (mFin : Measure (FiniteAdelicGroupPoints F G)) [mFin.IsHaarMeasure]
  (m : Measure (AdelicGroupPoints F G))
  (hProduct : MeasurePreserving (AdelicGroupPoints.split F G).symm (mInf.prod mFin) m)
  {f : InfiniteAdelicGroupPoints F G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)

include hProduct hf hc in
theorem adelicSmoothingWeight_integrable (g : HeckeAlgebra mFin) (k : ℕ) :
    Integrable (adelicSmoothingWeight F G mInf f g k) m := by
  obtain ⟨hcont, hsupp⟩ := positiveConvolutionPower_continuous_hasCompactSupport mInf hf hc k
  apply (hProduct.integrable_comp_emb (AdelicGroupPoints.split F G).symm.toHomeomorph.measurableEmbedding).mp
  have hInf : Integrable (positiveConvolutionPower mInf f k) mInf :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hp := hInf.mul_prod
      (HarmonicAnalysis.SchwartzBruhat.integrable (HeckeAlgebra.toTestFunction mFin g) mFin)
  convert hp using 1
  funext x
  change adelicSmoothingWeight F G mInf f g k (AdelicGroupPoints.pair F G x.1 x.2) = _
  rw [adelicSmoothingWeight, AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair]
  rfl

section Cuspidal

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hz : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hz
local notation "π" => fullAEL2CuspidalBoundedRightAction F G hPD hG Z i hi I e hz

/-- The tensor test integrated on the actual full almost-everywhere cuspidal space. -/
def adelicSmoothingAction (g : HeckeAlgebra mFin) (k : ℕ) : S →L[ℂ] S :=
  fullAEL2CuspidalIntegratedAction F G hPD hG Z i hi I e hz m
    (adelicSmoothingWeight F G mInf f g k)
    (adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g k)

/-- A positive power of the fixed-level smoothing operator increases the
infinite convolution power of the actual cuspidal test. -/
def AdelicFixedLevelSmoothingStatement
    (K : OpenSubgroup Af) (hK : IsCompact (K : Set Af))
    (g : HeckeAlgebra mFin) : Prop :=
  (∀ k : K, ∀ x, g (x * k) = g x) →
  let R := adelicSmoothingAction F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz
  let T := R (HeckeAlgebra.normalizedIndicator mFin K hK) 0
  ∀ U : S →L[ℂ] S, Commute U T → ∀ k : ℕ, (R g 0 * U) * T ^ k = R g k * U

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem adelicFixedLevelSmoothingPowers (K : OpenSubgroup Af) (hK : IsCompact (K : Set Af))
    (g : HeckeAlgebra mFin) :
    AdelicFixedLevelSmoothingStatement F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz K hK g := by
  intro hg R T U hU k
  let a := (AdelicGroupPoints.split F G).symm
  have ha : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  let ρ := (π).comp a.toMonoidHom
  let hn := norm_fullAEL2CuspidalBoundedRightAction F G hPD hG Z i hi I e hz
  let hm := fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG Z i hi I e hz m
  have hr (g' : HeckeAlgebra mFin) (j : ℕ) :
      smoothingPowerTensorAction mInf mFin ρ (fun x y => hn (a x) y)
        (fun x => (hm x).comp_measurePreserving hProduct) hf hc g' j = R g' j := by
    have hw := adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g' j
    have h := integratedIsometricAction_pullback m π hn hm _ hw (mInf.prod mFin) a.toMulEquiv ha hProduct
    have hWeight : adelicSmoothingWeight F G mInf f g' j ∘ a.toMulEquiv =
        fun x => positiveConvolutionPower mInf f j x.1 * g' x.2 := by
      funext x
      change adelicSmoothingWeight F G mInf f g' j (AdelicGroupPoints.pair F G x.1 x.2) = _
      simp only [adelicSmoothingWeight, AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair]
    ext1 x
    have hx := congrArg (fun B : S →L[ℂ] S => B x) h
    simp only [integratedIsometricAction_apply] at hx
    rw [hWeight] at hx
    exact hx
  have hU' :
      Commute U (smoothingPowerTensorAction mInf mFin ρ (fun x y => hn (a x) y)
        (fun x => (hm x).comp_measurePreserving hProduct) hf hc
        (HeckeAlgebra.normalizedIndicator mFin K hK) 0) := by
    rw [hr]
    exact hU
  simpa only [hr] using fixedLevelSmoothingPowers A∞ Af mInf mFin S ρ
    (fun x y => hn (a x) y) (fun x => (hm x).comp_measurePreserving hProduct) f hf hc K hK g hg U hU' k

/-- Every complete subspace invariant under adelic right translation is
invariant under each actual smoothing tensor. -/
theorem adelicSmoothingAction_mem_of_invariant (P : Submodule ℂ S) [CompleteSpace P]
    (hP : ∀ a x, x ∈ P → π a x ∈ P) (g : HeckeAlgebra mFin) (k : ℕ)
    (x : S) (hx : x ∈ P) :
    adelicSmoothingAction F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz g k x ∈ P :=
  integral_mem_of_forall_mem P
    (fullAEL2CuspidalActionIntegrand_integrable F G hPD hG Z i hi I e hz m _
      (adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g k) x)
    (fun a => P.smul_mem _ (hP a x hx))

end Cuspidal

end Langlands.TraceFormula
