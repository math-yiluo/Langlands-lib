import Langlands.Automorphic.CuspidalBlockCharacterSource
import Langlands.Global.Factors.CuspidalSupportSourceGK

/-! # Weak continuity on the selected cyclic period -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean Langlands.GeneralLinear ArchimedeanGL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 350000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}
  (B : BlockShape n) (S : OperatorRealization F n)

local instance periodGKRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance periodGKContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance periodGKSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance periodGKFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance periodGKStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance periodGKRealizationGroup {d : ℕ} (S' : OperatorRealization F d) :
    AddCommGroup S'.Space := Submodule.addCommGroup _
local instance periodGKOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

local notation "ρ" => translatedBlockTermCompactAction F B S

/-- The translated-period map intertwines the original compact action. -/
def blockTermCompactTranslation (z : Fin B.length → Ideles F) :
    Representation.IntertwiningMap S.compactRepresentation ρ where
  toLinearMap := (blockTermTranslationMap F B S z).toLinearMap
  isIntertwining' k := (blockTermTranslationMap F B S z).isIntertwining' (compactOperator F n k)

/-- Scalar compact orbits are continuous in the translated-period space. -/
theorem translatedBlockTerm_weaklyContinuousOrbits : HasWeaklyContinuousOrbits ρ := by
  refine HasWeaklyContinuousOrbits.of_spanning_ranges (fun _ => S.compactRepresentation) ρ
    (blockTermCompactTranslation F B S) ?_ ?_
  · exact blockTermTranslationMap_iSup_range F B S
  · exact fun _ w μ => S.continuous_dual_compactOrbit μ w

variable (v : Representation.asModule (AlgHom.toMonoidHom' (translatedBlockTermOperatorAction F B S)))

local notation "A" => blockTermCyclicAction F B S v
local notation "κ" => MonoidHom.comp (AlgHom.toMonoidHom' A) (compactOperator F n)

/-- Scalar compact orbits on the selected cyclic period are continuous. -/
theorem blockTermCyclic_weaklyContinuousOrbits : HasWeaklyContinuousOrbits κ := by
  let j := blockTermCyclicInclusion F B S v
  let jK : Representation.IntertwiningMap κ ρ :=
    { toLinearMap := j.toLinearMap
      isIntertwining' := fun k => j.isIntertwining' (compactOperator F n k) }
  refine HasWeaklyContinuousOrbits.of_injective_intertwiner jK ?_
    (translatedBlockTerm_weaklyContinuousOrbits F B S)
  exact Subtype.val_injective

end Langlands.Global
