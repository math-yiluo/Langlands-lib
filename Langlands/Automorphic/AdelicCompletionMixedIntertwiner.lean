import Langlands.Automorphic.AdelicCompletionSmoothSource
import Langlands.Representation.Archimedean.MixedSmoothIntertwiner

/-! # Full adelic intertwiners on the mixed source maps -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global Langlands.Archimedean Langlands.Automorphic.HilbertCoefficientComparison
  Langlands.Automorphic.CuspidalFixedSmoothDensity Langlands.Automorphic.OperatorDeterminantSlice

universe u uV uW uX uY

attribute [local instance] finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {Y : Type uY}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {ρ' : Representation ℂ (FiniteAdelicGL F n) W}
  {κ' : Representation ℂ (standardInfiniteCompact F n) W} {D' : Y → Module.End ℂ W}
  {b : OperatorUnitaryFormCore ρ κ D} {b' : OperatorUnitaryFormCore ρ' κ' D'}
  (B : AdelicCompletion b) (B' : AdelicCompletion b')

local notation "σ" => finiteHilbertAction F n (AdelicCompletion.action B)
local notation "π" => infiniteHilbertAction F n (AdelicCompletion.action B)
local notation "c" => hilbertCoordinateActions_commute F n (AdelicCompletion.action B)
local notation "σ'" => finiteHilbertAction F n (AdelicCompletion.action B')
local notation "π'" => infiniteHilbertAction F n (AdelicCompletion.action B')
local notation "c'" => hilbertCoordinateActions_commute F n (AdelicCompletion.action B')

variable (L : b.HilbertCompletion →L[ℂ] b'.HilbertCompletion)
  (hL : AdelicIntertwines B.action B'.action L)

/-- A full adelic intertwiner induces the mixed smooth intertwiner on the
two coordinate restrictions. -/
def coordinateMixedMap :=
  MixedSmooth.map (A := ArchimedeanMatrix F n) σ π c σ' π' c' L
    (fun d x => hL (AdelicGL.ofFinite F n d) x)
    (fun a x => hL (infiniteCoordinateInclusion F n a) x)

/-- On original vectors, the mixed smooth intertwiner agrees with the source
map extended by the bounded adelic intertwiner. -/
theorem coordinateMixedMap_source
    (hs : B.HasSmoothCoordinateSource) (hs' : B'.HasSmoothCoordinateSource)
    (hρ : Langlands.IsSmooth ρ) (hρ' : Langlands.IsSmooth ρ')
    (e : V → W) (he : ∀ v, L (b.toHilbert v) = b'.toHilbert (e v)) (v : V) :
    coordinateMixedMap B B' L hL (B.coordinateMixedSource hs hρ v) =
      B'.coordinateMixedSource hs' hρ' (e v) :=
  Subtype.ext (Subtype.ext (he v))

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
