import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerFunctionalStatement
import Langlands.Global.RankinSelberg.SelfPairPositiveData

/-! # The genuine Whittaker functional obtained from the band bound -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 85000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField MeasureTheory
  Langlands.Archimedean Langlands.Archimedean.MixedSmooth

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
  (ψ : AddChar (Adeles F) ℂ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "ρ" => T.realization.finiteRepresentation
local notation "S" => Langlands.Archimedean.smoothVectors I π

/-- Choose the band-bound extensions, glue them, and take the identity
evaluation. The cuspidal Whittaker expansion proves its nonvanishing. -/
theorem cuspidalMixedWhittakerFunctional :
    CuspidalMixedWhittakerFunctionalStatement T hL2 ψ σ π hcomm := by
  intro hψ hbound j hjinj hnorm hπ hdense hj hd hK hgen
  have hgen' := fun (X : RealLieAlgebra F (r + 1)) (w : T.Space) =>
    congrArg (fun v : S => v.val) (hgen X w)
  have hex := nonempty_evaluationExtensions_of_bandBound (E := E) T hL2 ψ hψ π j
    hbound hjinj hnorm hgen'
  obtain ⟨exts⟩ := hex
  let P := mixedWhittakerEvaluation T ψ hψ σ π hcomm j exts hd 1
  have hval := mixedWhittakerEvaluation_translated_value T ψ hψ σ π hcomm j exts hd
    hj hπ hdense hK hgen
  have hcov := mixedWhittakerEvaluation_unipotent T ψ hψ σ π hcomm j exts hd
    hj hπ hdense hK hgen
  have hcont : IsContinuousAtEachLevel (A := ArchimedeanMatrix F (r + 1)) σ π hcomm P :=
    isContinuousAtEachLevel_extendedEvaluation (A := ArchimedeanMatrix F (r + 1))
      (G := ArchimedeanGL F (r + 1)) (V₀ := T.Space) ρ σ π hcomm j
      (finiteWhittakerEvaluation T ψ hψ) exts hd 1
  refine ⟨P, ⟨hcont, hcov⟩, hval, ?_⟩
  intro w hw hzero
  obtain ⟨g, hg⟩ := SelfPair.exists_cuspWhittaker_ne_zero T ψ hψ hw
  let a := archPart F (r + 1) g
  let d := finPart F (r + 1) g
  have he : adelicPoint F (r + 1) a d = g :=
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
      ((adelicEquiv_adelicPoint F (r + 1) a d).trans (adelicEquiv_eq_pair F (r + 1) g).symm)
  have h := hval w a d
  change P _ = cuspWhittaker F T ψ w (adelicPoint F (r + 1) a d) at h
  rw [hzero, LinearMap.zero_apply, he] at h
  exact hg h.symm

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
