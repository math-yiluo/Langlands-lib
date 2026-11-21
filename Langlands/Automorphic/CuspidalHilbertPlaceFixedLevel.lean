import Langlands.Automorphic.AdelicHilbertPlaceFixedLevel
import Langlands.Automorphic.CuspidalHilbertPlaceRealization

/-! # Fixed-level smooth embeddings for actual cuspidal place components -/

noncomputable section
universe u
open scoped Classical ContDiff Manifold Matrix.Norms.Operator NumberField TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
set_option Elab.async false

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global ArchimedeanGL OperatorDeterminantSlice Langlands.Archimedean

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance fixedSmoothRationalGroup (m : ℕ) : AddCommGroup (RationalInvariantFunctions F m) :=
  Submodule.addCommGroup _
local instance fixedSmoothContinuousGroup (m : ℕ) : AddCommGroup (ContinuousRationalFunctions F m) :=
  Submodule.addCommGroup _
local instance fixedSmoothFiniteSmoothGroup (m : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F m) :=
  Submodule.addCommGroup _
local instance fixedSmoothFormsGroup (m : ℕ) : AddCommGroup (AutomorphicForms F m) :=
  Submodule.addCommGroup _
local instance fixedSmoothStableGroup (m : ℕ) : AddCommGroup (StableAutomorphicFunctions F m) :=
  Submodule.addCommGroup _
local instance fixedSmoothSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- In the actual cuspidal form completion every irreducible admissible real
or complex component fixed at a finite level has a smooth comparison at that level. -/
def CuspidalHilbertPlaceFixedLevelStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : ComputesBandInnerProduct T.realization b),
    let B := adelicCompletion T χ hχ hTχ b hb
    (∀ w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal v},
      B.SupportsRealPlaceFixedSmoothRealization w (T.realization.realPlaceLieAction w)) ∧
    ∀ w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex v},
      B.SupportsComplexPlaceFixedSmoothRealization w (T.realization.complexPlaceLieAction w)

theorem cuspidalHilbertPlaceFixedLevel : CuspidalHilbertPlaceFixedLevelStatement.{u} := by
  intro K _ _ _ r T χ hχ hTχ b hb
  let B := adelicCompletion T χ hχ hTχ b hb
  have hR := cuspidalHilbertPlaceRealization K r T χ hχ hTχ b hb
  have hinner := (adelicHilbertRepresentation_realizes T cuspidalHilbertOrbitCoefficient
    χ hχ hTχ b hb).2
  have hs := toHilbert_isSmoothVector T cuspidalHilbertOrbitCoefficient
    χ hχ hTχ b hb hilbertSmoothKernel
  exact ⟨fun w => B.supportsRealPlaceFixedSmoothRealization hinner hs w
      (T.realization.realPlaceLieAction w) (hR.1 w),
    fun w => B.supportsComplexPlaceFixedSmoothRealization hinner hs w
      (T.realization.complexPlaceLieAction w) (hR.2 w)⟩

end Langlands.Automorphic.OperatorRealization
