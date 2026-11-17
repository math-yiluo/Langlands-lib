import Langlands.Automorphic.OperatorDeterminantSliceMeasure

/-! # Compact Sobolev estimates on actual automorphic operator spaces

The finite compact open subgroup is fixed before the derivative operators and
constant are chosen. The norm is the actual determinant-band quotient `L²` norm.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions MeasureTheory
open scoped NumberField

local instance sobolevRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance sobolevContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance sobolevFiniteSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance sobolevFormGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance sobolevStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance sobolevSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Shalika's fixed-finite-level compact Sobolev estimate, expressed using the
actual operator realization, its genuine enveloping action, and the Library's
determinant-band Haar norm. The estimate itself remains unproved. -/
def OperatorCompactSobolevStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ)
    (S : OperatorRealization F (r + 1))
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ),
    (∀ z, ‖(χ z : ℂ)‖ = 1) → S.HasCentralCharacter χ →
    ∀ (hL2 : ∀ x : S.Space,
      MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) S x) 2
        ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))))
      (J : Subgroup (FiniteAdelicGL F (r + 1))),
      IsOpen (J : Set (FiniteAdelicGL F (r + 1))) →
      IsCompact (J : Set (FiniteAdelicGL F (r + 1))) →
      ∀ Q : Set (AdelicGL F (r + 1)), IsCompact Q →
        ∃ (D : Finset (ArchimedeanGL.EnvelopingAlgebra F (r + 1))) (C : ℝ),
          0 ≤ C ∧ ∀ x : S.Space,
            (∀ k : J, S.finiteRepresentation (k : FiniteAdelicGL F (r + 1)) x = x) →
            ∀ g ∈ Q, ‖evaluate F (r + 1) (S.toContinuous x) g‖ ≤
              C * ∑ d ∈ D,
                ‖OperatorDeterminantSlice.toL2 F (r + 1) S
                  (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2
                  (S.envelopingAction d x)‖

end Langlands.Automorphic
