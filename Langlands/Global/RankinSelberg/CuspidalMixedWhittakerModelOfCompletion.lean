import Langlands.Automorphic.AdelicCompletionSmoothSource
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModelOfSource

/-! # Compatible Whittaker source data from an adelic form completion -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global Langlands.Automorphic.OperatorDeterminantSlice
  Langlands.Automorphic.CuspidalFixedSmoothDensity Langlands.Archimedean
  Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

universe u uV uX

attribute [local instance] finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)

local notation "σ" => finiteHilbertAction F n (AdelicCompletion.action B)
local notation "π" => infiniteHilbertAction F n (AdelicCompletion.action B)
local notation "c" => hilbertCoordinateActions_commute F n (AdelicCompletion.action B)

/-- The coordinate actions and smooth embedding of an adelic form completion
satisfy the source hypotheses for Whittaker extension. -/
theorem coordinateWhittakerData
    (hs : B.HasSmoothCoordinateSource) (hρ : Langlands.IsSmooth ρ)
    (ζ : X → ArchimedeanMatrix F n) (sourceNorm : V → ℝ)
    (hnorm : ∀ w, sourceNorm w = ‖b.toHilbert w‖)
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hrec : b.JointVectorRecovery)
    (hgen : RealGeneratorCompatibility π b.toHilbert (fun X w => D X w) ζ) :
    SmoothSourceWhittakerData σ π c ρ κ D ζ sourceNorm
      (B.coordinateSmoothSource hs) (B.coordinateMixedSource hs hρ).toLinearMap where
  smoothValue := B.coordinateMixedSource_val hs hρ
  injective := B.coordinateSmoothSource_injective hs
  norm_eq := hnorm
  unitary := hπ
  denseSmooth := B.coordinateSmoothSource_dense hs
  finiteAction := B.coordinateActions_toHilbert.1
  denseAtLevel := B.coordinateDenseFixedImages hs hrec
  compactAction := B.coordinateActions_toHilbert.2
  generator := hgen

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
