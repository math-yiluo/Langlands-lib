import Langlands.Global.RankinSelberg.CuspidalArchimedeanModelPairingReduction
import Langlands.Representation.Archimedean.TransposePairingStatement

/-! # Exact cuspidal transpose reduction from the general local archimedean statements -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

local instance localGKReductionRationalGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localGKReductionContinuousGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localGKReductionSmoothGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localGKReductionFormsGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localGKReductionStableGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance localGKReductionSpaceGroup
    {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance localGKReductionSourceGroup
    {F : Type u} [Field F] [NumberField F] {n : ℕ} {S : OperatorRealization F n}
    (D : S.PlaceDensityModels) (i : InfinitePlaceFamily.Index F) :
    AddCommGroup (D.subspace i) := Submodule.addCommGroup _

/-- The general local statements apply to the actual chosen models: their
genuine GK axioms, irreducibility and admissibility have all been proved. -/
theorem cuspidalArchimedeanModelPairing_of_localGK
    (h : Archimedean.ArchimedeanTransposePairingStatement.{u}) :
    CuspidalArchimedeanModelPairingStatement.{u} := by
  intro F _ _ _ r T
  let P := T.placeDensityModels
  constructor
  · intro v
    exact h.1 r (P.subspace (.inl v)) (P.sourceCompact (.inl v)) (P.sourceLie (.inl v))
      (P.source_isRealGKModule v) (P.densityHyp (.inl v)).irreducible
      (P.densityHyp (.inl v)).admissible
  · intro v
    exact h.2 r (P.subspace (.inr v)) (P.sourceCompact (.inr v)) (P.sourceLie (.inr v))
      (P.source_isComplexGKModule v) (P.densityHyp (.inr v)).irreducible
      (P.densityHyp (.inr v)).admissible

/-- Only the named real and complex local archimedean pairing statements
remain in the reduction of the exact unconditional global target. -/
def CuspidalLocalGKTransposePairingReductionStatement : Prop :=
  Archimedean.ArchimedeanTransposePairingStatement.{u} →
    CuspidalTransposeInverseContragredientStatement.{u}

/-- All finite and global obligations are discharged; applying the two local
existence statements to the actual source models supplies the exact target. -/
theorem cuspidalLocalGKTransposePairingReduction :
    CuspidalLocalGKTransposePairingReductionStatement.{u} :=
  fun h => cuspidalArchimedeanModelPairingReduction
    (cuspidalArchimedeanModelPairing_of_localGK h)

end Langlands.Global.RankinSelbergGlobal
