import Langlands.Automorphic.CuspidalHilbertAdelicCompletion
import Langlands.Automorphic.HilbertPlaceRealizationData
import Langlands.Automorphic.CuspidalHilbertContinuity
import Langlands.Representation.Archimedean.HilbertSmoothKernelProof

/-! # Irreducible Hilbert realizations of actual cuspidal place components -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator NumberField TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL OperatorDeterminantSlice Langlands.Archimedean

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance cuspidalPlaceHilbertRationalGroup (m : ℕ) : AddCommGroup (RationalInvariantFunctions F m) :=
  Submodule.addCommGroup _
local instance cuspidalPlaceHilbertContinuousGroup (m : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F m) := Submodule.addCommGroup _
local instance cuspidalPlaceHilbertFiniteSmoothGroup (m : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F m) := Submodule.addCommGroup _
local instance cuspidalPlaceHilbertFormsGroup (m : ℕ) : AddCommGroup (AutomorphicForms F m) :=
  Submodule.addCommGroup _
local instance cuspidalPlaceHilbertStableGroup (m : ℕ) : AddCommGroup (StableAutomorphicFunctions F m) :=
  Submodule.addCommGroup _
local instance cuspidalPlaceHilbertSpaceGroup {m : ℕ} (S : OperatorRealization F m) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

namespace OperatorRealization

/-- Each irreducible admissible real or complex place subspace has its
compatible irreducible unitary Hilbert realization on the actual closure. -/
def CuspidalHilbertPlaceRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : ComputesBandInnerProduct T.realization b),
    let A := adelicCompletion T χ hχ hTχ b hb
    (∀ w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal v},
      A.SupportsRealPlaceHilbertRealization w (T.realization.realPlaceLieAction w)) ∧
    ∀ w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex v},
      A.SupportsComplexPlaceHilbertRealization w (T.realization.complexPlaceLieAction w)

theorem cuspidalHilbertPlaceRealization : CuspidalHilbertPlaceRealizationStatement.{u} := by
  intro K _ _ _ r T χ hχ hTχ b hb
  let A := adelicCompletion T χ hχ hTχ b hb
  have hD : ∀ a v, A.differential a v = T.realization.envelopingAction a v := fun _ _ => rfl
  have hcont := jointlyContinuous_adelicHilbertRepresentation T cuspidalHilbertOrbitCoefficient
    χ hχ hTχ b hb
  have hinner := (adelicHilbertRepresentation_realizes T cuspidalHilbertOrbitCoefficient
    χ hχ hTχ b hb).2
  have hs := toHilbert_isSmoothVector T cuspidalHilbertOrbitCoefficient
    χ hχ hTχ b hb hilbertSmoothKernel
  refine ⟨fun w => A.supportsRealPlaceHilbertRealization hcont hinner hs w
    (T.realization.realPlaceLieAction w) ?_ (T.realization.realPlaceCompactRepresentation_isFiniteVector w),
    fun w => A.supportsComplexPlaceHilbertRealization hcont hinner hs w
      (T.realization.complexPlaceLieAction w) ?_
      (T.realization.complexPlaceCompactRepresentation_isFiniteVector w)⟩
  · intro Y v
    have hY := (realPlaceComplexLieInclusion_tmul K (r + 1) w 1 Y).trans
      (complexify_apply K (r + 1) (realPlaceLieInclusion K (r + 1) w Y)).symm
    exact (hD _ v).trans
      ((congrArg (fun Z => T.realization.envelopingAction (envelopingGenerator K (r + 1) Z) v) hY.symm).trans
        (realPlaceLieAction_apply T.realization w (1 ⊗ₜ[ℝ] Y) v).symm)
  · intro Y v
    have hY := (complexPlaceComplexLieInclusion_tmul K (r + 1) w 1 Y).trans
      (complexify_apply K (r + 1) (complexPlaceLieInclusion K (r + 1) w Y)).symm
    exact (hD _ v).trans
      ((congrArg (fun Z => T.realization.envelopingAction (envelopingGenerator K (r + 1) Z) v) hY.symm).trans
        (complexPlaceLieAction_apply T.realization w (1 ⊗ₜ[ℝ] Y) v).symm)

end OperatorRealization
end Langlands.Automorphic
