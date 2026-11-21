import Langlands.Automorphic.AdelicCompletionMixedIntertwiner
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModel

/-! # Comparing Whittaker models on adelic form completions -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.OperatorDeterminantSlice
  Langlands.Automorphic.CuspidalFixedSmoothDensity Langlands.Automorphic.HilbertCoefficientComparison

universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T T' : CuspidalOperatorRealization F r)
  (b : T.realization.UnitaryForm) (b' : T'.realization.UnitaryForm)
  (B : OperatorUnitaryFormCore.AdelicCompletion b) (B' : OperatorUnitaryFormCore.AdelicCompletion b')

local notation "U" => OperatorUnitaryFormCore.AdelicCompletion.action B
local notation "U'" => OperatorUnitaryFormCore.AdelicCompletion.action B'
local notation "σ" => finiteHilbertAction F (r + 1) U
local notation "π" => infiniteHilbertAction F (r + 1) U
local notation "c" => hilbertCoordinateActions_commute F (r + 1) U
local notation "σ'" => finiteHilbertAction F (r + 1) U'
local notation "π'" => infiniteHilbertAction F (r + 1) U'
local notation "c'" => hilbertCoordinateActions_commute F (r + 1) U'

set_option maxHeartbeats 40000 in
/-- A bounded full adelic comparison of two compatible source maps
determines a single scalar on the original Whittaker values. -/
def CompletionWhittakerValuesProportional : Prop :=
  ∀ (hs : B.HasSmoothCoordinateSource) (hs' : B'.HasSmoothCoordinateSource)
    (ψ : AddChar (Adeles F) ℂ) (e : T.Space →ₗ[ℂ] T'.Space)
    (L : b.finiteForm.HilbertCompletion →L[ℂ] b'.finiteForm.HilbertCompletion),
    AdelicIntertwines (E := b.finiteForm.HilbertCompletion) (H := b'.finiteForm.HilbertCompletion)
      U U' L →
    (∀ v, L (b.finiteForm.toHilbert v) = b'.finiteForm.toHilbert (e v)) →
    HasMixedWhittakerModel (E := b.finiteForm.HilbertCompletion) T ψ σ π c
      (B.coordinateMixedSource hs T.realization.finiteRepresentation_isSmooth).toLinearMap →
    HasMixedWhittakerModel (E := b'.finiteForm.HilbertCompletion) T' ψ σ' π' c'
      (B'.coordinateMixedSource hs' T'.realization.finiteRepresentation_isSmooth).toLinearMap →
    MixedWhittakerUniqueness (r := r) (E := b.finiteForm.HilbertCompletion) ψ σ π c →
    ∃ s : ℂ, ∀ (v : T.Space) (g : Points F (r + 1)),
      cuspWhittaker F T' ψ (e v) g = s * cuspWhittaker F T ψ v g

/-- Restrict the completed map to mixed vectors and compare there. -/
theorem exists_proportional_whittaker_of_adelicCompletions :
    CompletionWhittakerValuesProportional T T' b b' B B' := by
  intro hs hs' ψ e L hL he hm hm' huniq
  exact @exists_proportional_whittaker_of_mixed_models F _ _ _ r T ψ
    b.finiteForm.HilbertCompletion _ _ σ π c b'.finiteForm.HilbertCompletion _ _ σ' π' c' L
    (fun d x => hL (AdelicGL.ofFinite F (r + 1) d) x)
    (fun a x => hL (infiniteCoordinateInclusion F (r + 1) a) x)
    T' e (B.coordinateMixedSource hs T.realization.finiteRepresentation_isSmooth).toLinearMap
    (B'.coordinateMixedSource hs' T'.realization.finiteRepresentation_isSmooth).toLinearMap
    (B.coordinateMixedMap_source B' L hL hs hs' T.realization.finiteRepresentation_isSmooth
      T'.realization.finiteRepresentation_isSmooth e he) hm hm' huniq

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
