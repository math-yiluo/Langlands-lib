import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Global.ArchimedeanJointFinite

/-! # Actual determinant-band Hilbert orbit coefficients -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory

variable {F : Type u} [Field F] [NumberField F]

local instance coefficientRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace CuspidalHilbertOrbitCoefficient

/-- The actual canonical quotient Haar measure restricted to the determinant band. -/
def bandMeasure (F : Type u) [Field F] [NumberField F] (r : ℕ) :
    Measure (OperatorDeterminantSlice.Quotient F (r + 1)) :=
  (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
    (OperatorDeterminantSlice.band F (r + 1))

/-- The full actual determinant-band `L²` space, before choosing any realization. -/
abbrev BandHilbertSpace (F : Type u) [Field F] [NumberField F] (r : ℕ) :=
  Lp ℂ 2 (bandMeasure F r)

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

local instance coefficientSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _

/-- Pair a band `L²` vector with an actual archimedean translate of a cusp function. -/
def integrand (w : BandHilbertSpace F r) (f : T.Space)
    (g : InfiniteAdelicGL F (r + 1)) :
    OperatorDeterminantSlice.Quotient F (r + 1) → ℂ :=
  fun q => Inner.inner ℂ (w q)
    (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization f
      (OperatorDeterminantSlice.translate F (r + 1)
        (AdelicGL.ofInfinite F (r + 1) g) q))

/-- The actual scalar coefficient; its integrability is required in the statement. -/
def coefficient (w : BandHilbertSpace F r) (f : T.Space)
    (g : InfiniteAdelicGL F (r + 1)) : ℂ :=
  ∫ q, integrand T w f g q ∂bandMeasure F r

end CuspidalHilbertOrbitCoefficient

/-- Smoothness and genuine differential covariance of the actual scalar Hilbert
orbit coefficients, retaining unitary central character and all integrability. -/
def CuspidalHilbertOrbitCoefficientStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    ∀ w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r,
      (∀ f g, Integrable (CuspidalHilbertOrbitCoefficient.integrand T w f g)
        (CuspidalHilbertOrbitCoefficient.bandMeasure F r)) ∧
      ∃ C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1),
        (∀ f g, (C f).val g = CuspidalHilbertOrbitCoefficient.coefficient T w f g) ∧
        (∀ (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) (f : T.Space),
          C (T.realization.envelopingAction a f) =
            ArchimedeanGL.envelopingAction F (r + 1) a (C f)) ∧
        (∀ f, ArchimedeanGL.IsJointFinite F (r + 1) (C f))

end Langlands.Automorphic
