import Langlands.Automorphic.CuspidalFixedSmoothAgreement
import Langlands.Automorphic.CuspidalFixedSmoothDensityStatement
import Langlands.Automorphic.CuspidalHilbertSmoothEmbedding
import Langlands.Automorphic.OperatorCompletedSourceActions
import Langlands.Global.HeckeDeterminantLocalConstancy
import Langlands.Representation.Archimedean.MixedSmoothExtension

/-! # Smooth source maps for an adelic form completion -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Automorphic.CuspidalFixedSmoothDensity
  Langlands.Archimedean Langlands.Archimedean.MixedSmooth Langlands.Automorphic.OperatorDeterminantSlice

universe u uV uX

attribute [local instance] finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)

local notation "σ" => finiteHilbertAction F n B.action
local notation "π" => infiniteHilbertAction F n B.action
local notation "hcomm" => hilbertCoordinateActions_commute F n B.action
local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F n)

/-- The original embedded vectors have genuine smooth orbits. -/
def HasSmoothCoordinateSource : Prop :=
  ∀ v : V, Langlands.Archimedean.IsSmoothVector I π (b.toHilbert v)

/-- The canonical embedding into genuine infinite smooth vectors. -/
def coordinateSmoothSource (hs : B.HasSmoothCoordinateSource) :
    V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π :=
  linearSmoothEmbedding π b.toHilbert hs

local notation "j" hs => coordinateSmoothSource B hs

/-- The original finite action corresponds to the bounded finite action. -/
theorem coordinateSmoothSource_finite (hs : B.HasSmoothCoordinateSource) (d : FiniteAdelicGL F n) (v : V) :
    finiteOnSmooth (A := ArchimedeanMatrix F n) σ π hcomm d ((j hs) v) = (j hs) (ρ d v) :=
  Subtype.ext (B.coordinateActions_toHilbert.1 d v)

/-- The original compact action corresponds to the bounded infinite action. -/
theorem coordinateSmoothSource_compact (hs : B.HasSmoothCoordinateSource)
    (k : standardInfiniteCompact F n) (v : V) :
    (j hs) (κ k v) = smoothRepresentation I π (archimedeanGLCoordinates F n k.val) ((j hs) v) :=
  Subtype.ext (B.coordinateActions_toHilbert.2 k v)

/-- Agreement of the real generators gives the same identity after
restricting the carrier to genuine smooth vectors. -/
theorem coordinateSmoothSource_generator (hs : B.HasSmoothCoordinateSource)
    (ζ : X → ArchimedeanMatrix F n)
    (hgen : RealGeneratorCompatibility π b.toHilbert (fun x v => D x v) ζ)
    (x : X) (v : V) :
    (j hs) (D x v) = smoothLieDerivative I π (ζ x) ((j hs) v) :=
  Subtype.ext (hgen x v)

/-- The smooth embedding remains injective. -/
theorem coordinateSmoothSource_injective (hs : B.HasSmoothCoordinateSource) :
    Function.Injective (j hs) :=
  linearSmoothEmbedding_injective π b.toHilbert hs b.toHilbert_injective

/-- The underlying Hilbert vectors of the smooth part contain the dense source image. -/
theorem coordinateSmoothSource_dense (hs : B.HasSmoothCoordinateSource) :
    DenseRange (Subtype.val : Langlands.Archimedean.smoothVectors I π → b.HilbertCompletion) :=
  b.denseRange_toHilbert.mono (Set.range_subset_iff.mpr fun w => ⟨(j hs) w, rfl⟩)

/-- A smooth original finite action gives the canonical mixed embedding. -/
def coordinateMixedSource (hs : B.HasSmoothCoordinateSource) (hρ : Langlands.IsSmooth ρ) :
    ρ.IntertwiningMap (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F n) σ π hcomm) :=
  sourceToMixed ρ σ π hcomm (j hs) hρ (B.coordinateSmoothSource_finite hs)

@[simp]
theorem coordinateMixedSource_val (hs : B.HasSmoothCoordinateSource) (hρ : Langlands.IsSmooth ρ) (v : V) :
    (B.coordinateMixedSource hs hρ v).val = (j hs) v :=
  rfl

/-- Joint vector recovery gives density of the smooth source in the
genuine derivative topology at every finite level. -/
theorem coordinateDenseFixedImages
    (hs : B.HasSmoothCoordinateSource) (hrec : b.JointVectorRecovery) :
    DenseFixedImages (A := ArchimedeanMatrix F n) ρ σ π (j hs) := by
  intro J
  exact b.dense_fixedSmoothImageOf σ J.val π
    (dense_fixedSmoothImage_of_jointRecovery F n b B.action B.boundedCompatibility J.val hrec)
    (j hs) (fun _ => rfl)

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
