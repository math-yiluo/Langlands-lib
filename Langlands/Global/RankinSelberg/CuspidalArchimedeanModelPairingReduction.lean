import Langlands.Automorphic.FiniteAdelicTransposePairing
import Langlands.Automorphic.FiniteInfiniteTransposePairing
import Langlands.Global.RankinSelberg.CuspidalNonzeroTransposePairingReduction

/-! # Reduction of the exact cuspidal target to archimedean local model forms -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic

local instance modelReductionRationalGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance modelReductionContinuousGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance modelReductionSmoothGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance modelReductionFormsGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance modelReductionStableGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance modelReductionSpaceGroup
    {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance modelReductionSourceGroup
    {F : Type u} [Field F] [NumberField F] {n : ℕ} {S : OperatorRealization F n}
    (D : S.PlaceDensityModels) (i : InfinitePlaceFamily.Index F) :
    AddCommGroup (D.subspace i) := Submodule.addCommGroup _

/-- The sole open input is nonzero local transpose forms on the chosen actual
irreducible admissible archimedean source models. -/
def CuspidalArchimedeanModelPairingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      Archimedean.HasNonzeroTransposeGKPairing ℝ (r + 1)
        (T.placeDensityModels.sourceCompact (.inl v))
        (T.placeDensityModels.sourceLie (.inl v))) ∧
    (∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      Archimedean.HasNonzeroTransposeGKPairing ℂ (r + 1)
        (T.placeDensityModels.sourceCompact (.inr v))
        (T.placeDensityModels.sourceLie (.inr v)))

/-- Actual finite and all archimedean assembly reduce intrinsic global form
existence to the displayed local model premise. -/
theorem cuspidalNonzeroTransposePairing_of_archimedeanModels
    (h : CuspidalArchimedeanModelPairingStatement.{u}) :
    CuspidalNonzeroTransposePairingStatement.{u} := by
  intro F _ _ _ r T
  let A := T.finiteInfiniteDecomposition
  let P := T.placeDensityModels
  let C := FiniteAdelicGL.TransposePairing.pairing r A.finite.toSubmodule
    A.finite.toRepresentation A.admissible A.irreducible
  let B := P.fullTransposePairing A.finite T.irreducible A.nonzero
    A.irreducible A.admissible C.val C.property.1 C.property.2
    (h F r T).1 (h F r T).2
  exact ⟨B.val, B.property⟩

/-- Conditional reduction of the exact global target with only archimedean
local model form existence retained. -/
def CuspidalArchimedeanModelPairingReductionStatement : Prop :=
  CuspidalArchimedeanModelPairingStatement.{u} →
    CuspidalTransposeInverseContragredientStatement.{u}

/-- The actual finite-factor form and all-place assembly supply the intrinsic
form; the nonzero-form criterion and actual transpose supply the exact target. -/
theorem cuspidalArchimedeanModelPairingReduction :
    CuspidalArchimedeanModelPairingReductionStatement.{u} :=
  fun h => cuspidalNonzeroTransposePairingReduction
    (cuspidalNonzeroTransposePairing_of_archimedeanModels h)

end Langlands.Global.RankinSelbergGlobal
