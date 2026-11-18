import Langlands.Automorphic.CuspidalHilbertSmoothEmbedding

/-! # Genuine real generators of the conditional actual Hilbert action -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField Matrix.Norms.Operator
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance hilbertScalarLiftsRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertScalarLiftsContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertScalarLiftsFiniteGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertScalarLiftsFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertScalarLiftsStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertScalarLiftsSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The named actual coefficient premise supplies scalar generator lifts on
the full band space, before comparing any vector derivatives. -/
theorem scalarGeneratorLifts_of_coefficients
    (hc : CuspidalHilbertOrbitCoefficientStatement.{u})
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T) :
    Langlands.Archimedean.ScalarGeneratorLifts
      (fun (w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r) (v : T.Space)
        (g : ArchimedeanGL F (r + 1)) => CuspidalHilbertOrbitCoefficient.coefficient T w v
          ((archimedeanGLCoordinates F (r + 1)).symm g))
      (fun X v => T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
        (ArchimedeanGL.complexify F (r + 1) X)) v)
      (ArchimedeanGL.realLieAlgebraToMatrix F (r + 1)) := by
  intro w
  refine Exists.elim (hc F r T hT w).2 fun C hC => ?_
  refine ⟨fun v g => (C v).val ((archimedeanGLCoordinates F (r + 1)).symm g),
    (fun v g => hC.1 v ((archimedeanGLCoordinates F (r + 1)).symm g)), ?_⟩
  intro X v
  exact (congrArg (C (T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
    (ArchimedeanGL.complexify F (r + 1) X)) v)).val
      (map_one (archimedeanGLCoordinates F (r + 1)).symm)).trans
    ((congrArg (fun s : ArchimedeanGL.SmoothFunctions F (r + 1) => s.val 1)
      (hC.2.1 (ArchimedeanGL.envelopingGenerator F (r + 1)
        (ArchimedeanGL.complexify F (r + 1) X)) v)).trans
          (smoothCoefficient_generator_one X (C v)))


end OperatorDeterminantSlice
end Langlands.Automorphic
