import Langlands.TraceFormula.AdelicFixedLevelSmoothing

/-! # Convolution factors of an adelic smoothing weight -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme Langlands.Hecke Langlands.Analysis

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
  (mFin : Measure (FiniteAdelicGroupPoints F G))
  {f : InfiniteAdelicGroupPoints F G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)

set_option maxHeartbeats 800000 in
/-- The actual smoothing weight as a continuous compactly supported test. -/
def adelicSmoothingCompactTest (g : HeckeAlgebra mFin) (k : ℕ) : C_c(A, ℂ) := by
  obtain ⟨hc, hcs⟩ := positiveConvolutionPower_continuous_hasCompactSupport mInf hf hs k
  let g₀ := HeckeAlgebra.toTestFunction mFin g
  let weight : A∞ × Af → ℂ := fun p => positiveConvolutionPower mInf f k p.1 * g₀ p.2
  have hweight : HasCompactSupport weight := by
    apply HasCompactSupport.of_support_subset_isCompact (hcs.prod g₀.hasCompactSupport)
    intro p hp
    obtain ⟨hi, ht⟩ := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport _ hi, subset_tsupport _ ht⟩
  let split := (AdelicGroupPoints.split F G).toHomeomorph
  exact ⟨⟨weight ∘ split,
    ((hc.comp continuous_fst).mul (g₀.continuous.comp continuous_snd)).comp split.continuous⟩,
    hweight.comp_homeomorph split⟩

@[simp]
theorem adelicSmoothingCompactTest_apply (g : HeckeAlgebra mFin) (k : ℕ) (x : A) :
    adelicSmoothingCompactTest F G mInf mFin hf hs g k x =
      adelicSmoothingWeight F G mInf f g k x := rfl

variable [mFin.IsHaarMeasure] (m : Measure (AdelicGroupPoints F G))
  (K : OpenSubgroup (FiniteAdelicGroupPoints F G))
  (hK : IsCompact (K : Set (FiniteAdelicGroupPoints F G)))
  (g : HeckeAlgebra mFin) (k : ℕ)

/-- A smoothing weight with `k + 2` infinite factors is the adelic convolution of the
one-factor level kernel and the weight with `k + 1` infinite factors and finite test `g`.
The finite test is fixed by left averaging at the chosen level. -/
def AdelicSmoothingConvolutionStatement : Prop :=
  MeasurePreserving (AdelicGroupPoints.split F G).symm (mInf.prod mFin) m →
  (∀ a : K, ∀ x, g ((a : Af) * x) = g x) →
  convolutionIntegral m
    (adelicSmoothingCompactTest F G mInf mFin hf hs
      (HeckeAlgebra.normalizedIndicator mFin K hK) 0)
    (adelicSmoothingCompactTest F G mInf mFin hf hs g k) =
  adelicSmoothingWeight F G mInf f g (k + 1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem adelicSmoothingConvolution :
    AdelicSmoothingConvolutionStatement F G mInf mFin hf hs m K hK g k := by
  intro hProduct hg
  let e := AdelicGroupPoints.split F G
  let q := HeckeAlgebra.normalizedIndicator mFin K hK
  let a : A∞ × Af → ℂ := fun p => positiveConvolutionPower mInf f 0 p.1 * q p.2
  let b : A∞ × Af → ℂ := fun p => positiveConvolutionPower mInf f k p.1 * g p.2
  have hm : m.map e = mInf.prod mFin := by
    have he : Measurable (e : A → A∞ × Af) := e.continuous.measurable
    have he' : Measurable (e.symm : A∞ × Af → A) := e.symm.continuous.measurable
    have hm' : (mInf.prod mFin).map e.symm = m := hProduct.map_eq
    rw [← hm', Measure.map_map he he']
    simp only [Function.comp_def, e.apply_symm_apply, Measure.map_id']
  funext x
  change convolutionIntegral m (a ∘ e) (b ∘ e) x = _
  rw [convolutionIntegral_comp_continuousMulEquiv e, hm]
  change convolutionIntegral (mInf.prod mFin) _ _ (e x) = _
  rw [show a = _ from rfl, show b = _ from rfl, convolutionIntegral_prod_tensor,
    convolutionIntegral_positiveConvolutionPower mInf hf hs, Nat.zero_add]
  have he : convolutionIntegral mFin q g (e x).2 = g (e x).2 :=
    congrArg (fun g' : HeckeAlgebra mFin => g' (e x).2)
      (HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant mFin K hK g hg)
  rw [he]
  rfl

end Langlands.TraceFormula
