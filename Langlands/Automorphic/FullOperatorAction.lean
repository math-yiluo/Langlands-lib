import Langlands.Automorphic.CompactAction
import Langlands.Automorphic.DifferentialInfiniteFiniteProof
import Langlands.Automorphic.DifferentialGrowthProof

/-! # The actual operator algebra acts on every automorphic form -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance fullOperatorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fullOperatorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullOperatorSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullOperatorFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance fullOperatorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- Published compact-finiteness and growth proofs give full differential closure. -/
theorem automorphicDifferentialPreservation :
    AutomorphicDifferentialPreservationStatement F n :=
  (automorphicDifferentialPreservation_iff F n).mpr
    ⟨automorphicDifferentialInfiniteFinite F n, automorphicDifferentialGrowth F n⟩

/-- The maximal stable core is the entire actual automorphic subspace. -/
theorem automorphicOperatorCore_eq :
    (automorphicOperatorCore F n).toSubmodule =
      (automorphicSubrepresentation F n).toSubmodule :=
  (automorphicOperatorCore_eq_iff_differential F n).mpr
    (automorphicDifferentialPreservation F n)

/-- Equality of actual subspaces gives a continuous identification with every form. -/
def stableAutomorphicEquiv :
    StableAutomorphicFunctions F n ≃L[ℂ] AutomorphicForms F n :=
  ContinuousLinearEquiv.ofEq _ _ (automorphicOperatorCore_eq F n)

@[simp] theorem stableAutomorphicEquiv_apply (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEquiv F n f = stableAutomorphicInclusion F n f := by
  apply Subtype.ext
  rfl

@[simp] theorem stableAutomorphicEquiv_symm_val (f : AutomorphicForms F n) :
    ((stableAutomorphicEquiv F n).symm f).val = f.val := rfl

/-- The original actual form subspace is invariant under the whole concrete algebra. -/
def fullAutomorphicSubrepresentation :
    Subrepresentation (automorphicOperatorAction F n) where
  toSubmodule := (automorphicSubrepresentation F n).toSubmodule
  apply_mem_toSubmodule a f hf :=
    (operatorCore_eq_iff F n _).mp (automorphicOperatorCore_eq F n) a f hf

/-- Restrict the actual ambient operators to all automorphic forms. -/
def fullAutomorphicAction :
    Representation ℂ (automorphicOperatorAlgebra F n) (AutomorphicForms F n) :=
  (fullAutomorphicSubrepresentation F n).toRepresentation

@[simp] theorem fullAutomorphicAction_val (a : automorphicOperatorAlgebra F n)
    (f : AutomorphicForms F n) :
    (fullAutomorphicAction F n a f).val = a.val f.val := rfl

/-- Restriction preserves the complete complex algebra structure of the operators. -/
def fullAutomorphicAlgebraAction :
    automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ (AutomorphicForms F n) where
  toFun := fullAutomorphicAction F n
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl

/-- The genuine enveloping differential action on the entire actual form space. -/
def automorphicEnvelopingAction :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ (AutomorphicForms F n) :=
  (fullAutomorphicAlgebraAction F n).comp (differentialOperator F n)

@[simp] theorem automorphicEnvelopingAction_val
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : AutomorphicForms F n) :
    (automorphicEnvelopingAction F n a f).val =
      finiteSmoothEnvelopingAction F n a f.val := rfl

@[simp] theorem fullAutomorphicAction_finiteOperator (d : FiniteAdelicGL F n)
    (f : AutomorphicForms F n) :
    fullAutomorphicAction F n (finiteOperator F n d) f =
      automorphicFiniteRightAction F n d f := rfl

@[simp] theorem fullAutomorphicAction_compactOperator (k : standardInfiniteCompact F n)
    (f : AutomorphicForms F n) :
    fullAutomorphicAction F n (compactOperator F n k) f =
      automorphicCompactRightAction F n k f := rfl

@[simp] theorem fullAutomorphicAction_differentialOperator
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : AutomorphicForms F n) :
    fullAutomorphicAction F n (differentialOperator F n a) f =
      automorphicEnvelopingAction F n a f := rfl

/-- The faithful ambient inclusion intertwines every concrete operator. -/
def fullAutomorphicFiniteSmoothInclusion :
    (fullAutomorphicAction F n).IntertwiningMap (automorphicOperatorAction F n) where
  toLinearMap := (automorphicSubrepresentation F n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem fullAutomorphicFiniteSmoothInclusion_injective :
    Function.Injective (fullAutomorphicFiniteSmoothInclusion F n) := Subtype.val_injective

/-- The core-to-form identification respects the entire operator algebra. -/
def stableAutomorphicOperatorEquiv :
    (stableAutomorphicAction F n).Equiv (fullAutomorphicAction F n) :=
  Representation.Equiv.mk (stableAutomorphicEquiv F n).toLinearEquiv (by
    intro a
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl)

@[simp] theorem stableAutomorphicEquiv_operatorAction (a : automorphicOperatorAlgebra F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEquiv F n (stableAutomorphicAction F n a f) =
      fullAutomorphicAction F n a (stableAutomorphicEquiv F n f) := by
  apply Subtype.ext
  rfl

@[simp] theorem stableAutomorphicEquiv_finiteAction (d : FiniteAdelicGL F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEquiv F n (stableAutomorphicFiniteAction F n d f) =
      automorphicFiniteRightAction F n d (stableAutomorphicEquiv F n f) := by
  apply Subtype.ext
  rfl

@[simp] theorem stableAutomorphicEquiv_compactAction (k : standardInfiniteCompact F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEquiv F n (stableAutomorphicCompactAction F n k f) =
      automorphicCompactRightAction F n k (stableAutomorphicEquiv F n f) := by
  apply Subtype.ext
  rfl

@[simp] theorem stableAutomorphicEquiv_envelopingAction
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEquiv F n (stableAutomorphicEnvelopingAction F n a f) =
      automorphicEnvelopingAction F n a (stableAutomorphicEquiv F n f) := by
  apply Subtype.ext
  rfl

/-- Finite translation commutes with the genuine enveloping action on every form. -/
theorem automorphicFiniteRightAction_envelopingAction (d : FiniteAdelicGL F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : AutomorphicForms F n) :
    automorphicFiniteRightAction F n d (automorphicEnvelopingAction F n a f) =
      automorphicEnvelopingAction F n a (automorphicFiniteRightAction F n d f) := by
  apply Subtype.ext
  exact finiteSmoothFiniteRightAction_envelopingAction F n d a f.val

end Langlands.Automorphic
