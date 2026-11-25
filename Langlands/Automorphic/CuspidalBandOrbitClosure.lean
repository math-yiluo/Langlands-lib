import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientStatement
import Langlands.Automorphic.CuspidalTranslatedHilbertEmbedding
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Actual Hilbert orbit containment from smooth scalar coefficients -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands

universe uV uH

/-- Inner-product annihilators detect the actual Hilbert closure of a linear image. -/
theorem mem_closure_range_of_inner_annihilators
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : V →ₗ[ℂ] H) (x : H)
    (hx : ∀ w : H, (∀ v, Inner.inner ℂ w (j v) = 0) → Inner.inner ℂ w x = 0) :
    x ∈ (LinearMap.range j).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply ((LinearMap.range j)ᗮ.mem_orthogonal x).mpr
  intro w hw
  exact hx w fun v => ((LinearMap.range j).mem_orthogonal' w).mp hw (j v) ⟨v, rfl⟩

end Langlands

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory
universe u

variable {F : Type u} [Field F] [NumberField F]
  [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance closureRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance closureContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance closureSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance closureFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance closureStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance closureSpaceGroup (T : CuspidalOperatorRealization F r) :
    AddCommGroup T.Space := Submodule.addCommGroup _

namespace CuspidalHilbertOrbitCoefficient

variable (T : CuspidalOperatorRealization F r)

/-- At a standard compact element the integral uses an actual original compact
translate, which stays in the source carrier. -/
theorem coefficient_compact (w : BandHilbertSpace F r) (f : T.Space)
    (k : standardInfiniteCompact F (r + 1)) :
    coefficient T w f k.val =
      ∫ q, Inner.inner ℂ (w q) (OperatorDeterminantSlice.toQuotient F (r + 1)
        T.realization (T.realization.compactRepresentation k f) q) ∂bandMeasure F r := by
  apply integral_congr_ae
  exact ae_of_all _ fun q => congrArg (Inner.inner ℂ (w q))
    (OperatorDeterminantSlice.toQuotient_compact F (r + 1) T.realization k f q).symm

/-- Smooth joint-finite actual coefficients whose original functional vanishes
on the source vanish on every archimedean translate. -/
theorem coefficient_eq_zero_of_source_annihilator
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (w : BandHilbertSpace F r)
    (hw : ∀ f : T.Space,
      (∫ q, Inner.inner ℂ (w q)
        (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization f q)
        ∂bandMeasure F r) = 0)
    (f : T.Space) (g : InfiniteAdelicGL F (r + 1)) :
    coefficient T w f g = 0 := by
  obtain ⟨_hint, C, hC, hD, hJ⟩ := hcoeff F r T hT w
  have han := ArchimedeanGL.jointFiniteAnalyticity F (r + 1) (C f) (hJ f)
  obtain ⟨k, hgk⟩ := ArchimedeanGL.compactComponentCoverage F (r + 1) g
  have hzero (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) :
      (ArchimedeanGL.envelopingAction F (r + 1) a (C f)).val k.val = 0 :=
    (congrArg (fun s : ArchimedeanGL.SmoothFunctions F (r + 1) => s.val k.val)
      (hD a f).symm).trans
      ((hC (T.realization.envelopingAction a f) k.val).trans
        ((coefficient_compact T w (T.realization.envelopingAction a f) k).trans (hw _)))
  have hjet := ArchimedeanGL.envelopingZeroJet F (r + 1) (C f) k.val hzero
  have hg := ArchimedeanGL.analyticMatrixJetUniqueness F (r + 1) (C f) k.val han hjet g hgk
  exact (hC f g).symm.trans hg

end CuspidalHilbertOrbitCoefficient

namespace OperatorDeterminantSlice

variable (T : CuspidalOperatorRealization F r)

/-- Pairing an arbitrary band `L²` vector with the prescribed translated `Lp`
vector is precisely the actual coefficient integral. -/
theorem inner_translatedToL2_left
    (w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r)
    (a : AdelicGL F (r + 1)) (f : T.Space) :
    Inner.inner ℂ w (translatedToL2 T.realization T.cuspidal a f) =
      ∫ q, Inner.inner ℂ (w q) (toQuotient F (r + 1) T.realization f
        (translate F (r + 1) a q))
        ∂CuspidalHilbertOrbitCoefficient.bandMeasure F r := by
  refine (L2.inner_def w (translatedToL2 T.realization T.cuspidal a f)).trans ?_
  apply integral_congr_ae
  filter_upwards [(memLp_translate_of_cuspidal T.realization T.cuspidal a f).coeFn_toLp]
    with q hq
  exact congrArg (Inner.inner ℂ (w q)) hq

/-- The actual Hilbert closure of the source's original band image. -/
def sourceBandClosure :
    Submodule ℂ (CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r) :=
  (LinearMap.range (translatedToL2 T.realization T.cuspidal 1)).topologicalClosure

/-- All translated original vectors lie in the same source band closure, under
the explicit open scalar-coefficient premise. -/
theorem translatedToL2_mem_sourceBandClosure_of_coefficients
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (g : InfiniteAdelicGL F (r + 1)) (f : T.Space) :
    translatedToL2 T.realization T.cuspidal (AdelicGL.ofInfinite F (r + 1) g) f ∈
      sourceBandClosure T := by
  apply Langlands.mem_closure_range_of_inner_annihilators
  intro w hw
  have hw' (v : T.Space) :
      (∫ q, Inner.inner ℂ (w q) (toQuotient F (r + 1) T.realization v q)
        ∂CuspidalHilbertOrbitCoefficient.bandMeasure F r) = 0 := by
    have h := inner_translatedToL2_left T w 1 v
    simp only [translate_one] at h
    exact h.symm.trans (hw v)
  exact (inner_translatedToL2_left T w (AdelicGL.ofInfinite F (r + 1) g) f).trans
    (CuspidalHilbertOrbitCoefficient.coefficient_eq_zero_of_source_annihilator
      T hcoeff hT w hw' f g)

end OperatorDeterminantSlice

/-- The actual archimedean translated algebraic image lies in the original
source's Hilbert-band closure. -/
def CuspidalBandOrbitClosureStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      ∀ (g : InfiniteAdelicGL F (r + 1)) (f : T.Space),
        OperatorDeterminantSlice.translatedToL2 T.realization T.cuspidal
          (AdelicGL.ofInfinite F (r + 1) g) f ∈ OperatorDeterminantSlice.sourceBandClosure T

/-- Analytic annihilator reduction to the explicit smooth coefficient statement. -/
theorem cuspidalBandOrbitClosure_of_coefficients
    (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u}) :
    CuspidalBandOrbitClosureStatement.{u} := by
  intro F _ _ _ r T hT g f
  exact OperatorDeterminantSlice.translatedToL2_mem_sourceBandClosure_of_coefficients
    T hcoeff hT g f

/-- The unproved smooth coefficient input is retained as a named premise of
this Hilbert closure reduction. -/
def CuspidalBandOrbitClosureReductionStatement : Prop :=
  CuspidalHilbertOrbitCoefficientStatement.{u} → CuspidalBandOrbitClosureStatement.{u}

/-- Actual Hilbert-band orbit containment follows from the retained coefficient input. -/
theorem cuspidalBandOrbitClosureReduction : CuspidalBandOrbitClosureReductionStatement.{u} :=
  cuspidalBandOrbitClosure_of_coefficients

end Langlands.Automorphic
