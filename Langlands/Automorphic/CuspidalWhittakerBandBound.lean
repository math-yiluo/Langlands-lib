import Langlands.Automorphic.CuspidalWhittakerCompactDomination
import Langlands.Automorphic.CuspidalUnitaryForm

/-! # Actual band integrability and a Whittaker derivative-bound predicate -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.MonObj NumberField

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  ContinuousRationalFunctions MeasureTheory

local instance bandBoundRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance bandBoundContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance bandBoundFiniteSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance bandBoundFormGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance bandBoundStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance bandBoundSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- Every actual cusp vector is square integrable on the determinant band
for the canonical rational-quotient Haar measure. -/
theorem memLp_cuspidal_toQuotient_band (v : T.Space) :
    MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization v) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))) := by
  let : MeasurableSpace (AdelicGL F (r + 1)) := borel _
  have : BorelSpace (AdelicGL F (r + 1)) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ :=
    T.realization.exists_band_cover T.cuspidal (lo := 1) (hi := 2) one_pos
  exact OperatorDeterminantSlice.memLp_band_of_cover F (r + 1)
    T.realization t ht (fun x hx => hcover x hx.1 hx.2) v (hfinite _ v)

/-- At each fixed compact open finite level, actual Whittaker coefficients
on compact sets are bounded by finitely many genuine enveloping derivatives
in the actual determinant-band Haar `L²` norm. -/
def CuspidalWhittakerBandBound
    (hL2 : ∀ x : T.Space,
      MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
        ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))))
    (ψ : AddChar (Adeles F) ℂ) : Prop :=
  ∀ J : Subgroup (FiniteAdelicGL F (r + 1)),
    IsOpen (J : Set (FiniteAdelicGL F (r + 1))) →
    IsCompact (J : Set (FiniteAdelicGL F (r + 1))) →
    ∀ Q : Set (Points F (r + 1)), IsCompact Q →
      ∃ (D : Finset (ArchimedeanGL.EnvelopingAlgebra F (r + 1))) (C : ℝ),
        0 ≤ C ∧ ∀ v : T.Space,
          (∀ k : J, T.realization.finiteRepresentation
            (k : FiniteAdelicGL F (r + 1)) v = v) →
          ∀ g ∈ Q, ‖cuspWhittaker F T ψ v g‖ ≤
            C * ∑ d ∈ D,
              ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
                (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2
                (T.realization.envelopingAction d v)‖


end Langlands.Automorphic
