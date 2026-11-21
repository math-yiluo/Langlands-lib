import Langlands.Automorphic.CuspidalWhittakerSmoothExtension
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerEvaluation

/-! # Actual Whittaker extension families supplied by the band bound -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField MeasureTheory
  Langlands.Archimedean Langlands.Archimedean.MixedSmooth Langlands.HarishChandraSchwartz

universe u v

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  (hL2 : ∀ x : T.Space,
    MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))))
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "S" => Langlands.Archimedean.smoothVectors I π
local notation "ρ" => T.realization.finiteRepresentation
local notation "K" => CompactOpenSubgroup (FiniteAdelicGL F (r + 1))

/-- The actual band bound gives one derivative-continuous extension at
each finite argument and each compact open level. -/
theorem nonempty_evaluationExtensions_of_bandBound
    (j : T.Space →ₗ[ℂ] S) (hbound : CuspidalWhittakerBandBound F T hL2 ψ)
    (hj : Function.Injective j)
    (hnorm : ∀ v : T.Space,
      ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
        (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2 v‖ = ‖(j v).val‖)
    (hgen : ∀ (X : RealLieAlgebra F (r + 1)) (w : T.Space),
      (j (T.realization.envelopingAction
        (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w)).val =
        lieDerivative I π (realLieAlgebraToMatrix F (r + 1) X) (j w)) :
    Nonempty (EvaluationExtensions (A := ArchimedeanMatrix F (r + 1)) (G := ArchimedeanGL F (r + 1))
      ρ π j (finiteWhittakerEvaluation T ψ hψ)) := by
  have he (d : FiniteAdelicGL F (r + 1)) (J : K) :
      ∃ L : S →ₗ[ℂ] ℂ, IsContinuousOnSmoothVectors I π L ∧
        ∀ v ∈ Langlands.fixedVectors ρ J.toSubgroup,
          L (j v) = finiteWhittakerEvaluation T ψ hψ d v := by
    let g := adelicPoint F (r + 1) 1 d
    have hb := exists_cuspWhittaker_smoothExtensions_of_bandBound
      (𝔤 := ArchimedeanMatrix F (r + 1)) (H := ArchimedeanMatrix F (r + 1))
      (G := ArchimedeanGL F (r + 1)) (E := E)
      F T hL2 ψ I π j (realLieAlgebraToMatrix F (r + 1))
    have hJo : IsOpen (J.toSubgroup : Set (FiniteAdelicGL F (r + 1))) := J.val.isOpen
    have hJc : IsCompact (J.toSubgroup : Set (FiniteAdelicGL F (r + 1))) := J.property
    let Q : Set (Points F (r + 1)) := {g}
    have hQ : IsCompact Q := isCompact_singleton
    have hbound' := hb hψ hbound hj hnorm hgen
    have hext := hbound' J.toSubgroup hJo hJc Q hQ
    obtain ⟨_, _, _, hc⟩ := hext
    have hg : g ∈ Q := Set.mem_singleton g
    have hLg := hc g hg
    obtain ⟨L, hL, _, hcont⟩ := hLg
    refine ⟨L, hcont, ?_⟩
    intro w hw
    exact (hL w hw).trans (finiteWhittakerEvaluation_apply T ψ hψ d w).symm
  choose L hL hc using he
  exact ⟨{ level := L, continuous_level := hL, agrees := hc }⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
