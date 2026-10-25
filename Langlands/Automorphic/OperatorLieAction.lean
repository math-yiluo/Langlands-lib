import Langlands.Automorphic.OperatorEquivalence
import Langlands.Global.ArchimedeanCompactLieAlgebra

/-! # Lie actions on actual automorphic realizations -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance operatorLieRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance operatorLieContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorLieSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorLieFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance operatorLieStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance operatorLieSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance operatorLieSpaceAddCommGroup' : AddCommGroup T.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The genuine complex Lie algebra acts through the existing enveloping action. -/
def complexLieAction : ArchimedeanGL.ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.envelopingAction.toLieHom.comp (ArchimedeanGL.envelopingGenerator F n)

@[simp]
theorem complexLieAction_apply (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.complexLieAction X f = S.envelopingAction (ArchimedeanGL.envelopingGenerator F n X) f :=
  rfl

/-- Restrict the same action along the actual complexified compact Lie inclusion. -/
def compactLieAction : ArchimedeanGL.CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.complexLieAction.comp (ArchimedeanGL.compactComplexInclusion F n)

@[simp]
theorem compactLieAction_apply (X : ArchimedeanGL.CompactComplexLieAlgebra F n) (f : S.Space) :
    S.compactLieAction X f =
      S.complexLieAction (ArchimedeanGL.compactComplexInclusion F n X) f := rfl

instance complexLieRingModule : LieRingModule (ArchimedeanGL.ComplexLieAlgebra F n) S.Space :=
  LieRingModule.compLieHom S.Space S.complexLieAction

instance complexLieModule : LieModule ℂ (ArchimedeanGL.ComplexLieAlgebra F n) S.Space :=
  LieModule.compLieHom S.Space S.complexLieAction

instance compactLieRingModule :
    LieRingModule (ArchimedeanGL.CompactComplexLieAlgebra F n) S.Space :=
  LieRingModule.compLieHom S.Space (ArchimedeanGL.compactComplexInclusion F n)

instance compactLieModule : LieModule ℂ (ArchimedeanGL.CompactComplexLieAlgebra F n) S.Space :=
  LieModule.compLieHom S.Space (ArchimedeanGL.compactComplexInclusion F n)

@[simp]
theorem complex_lie_eq (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    ⁅X, f⁆ = S.complexLieAction X f := rfl

@[simp]
theorem compact_lie_eq (X : ArchimedeanGL.CompactComplexLieAlgebra F n) (f : S.Space) :
    ⁅X, f⁆ = S.compactLieAction X f := rfl

/-- The constructed infinitesimal action is the restriction of the actual differential operator. -/
theorem inclusion_complexLieAction (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.inclusion (S.complexLieAction X f) =
      stableAutomorphicEnvelopingAction F n (ArchimedeanGL.envelopingGenerator F n X)
        (S.inclusion f) := rfl

/-- Finite adelic translations commute with the actual complex Lie action. -/
theorem finiteRepresentation_complexLieAction (d : FiniteAdelicGL F n)
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) :
    S.finiteRepresentation d (S.complexLieAction X f) =
      S.complexLieAction X (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (ArchimedeanGL.envelopingGenerator F n X) f

namespace Intertwiner

variable {S T}

/-- A full intertwiner preserves the complex Lie algebra action. -/
def complexLieRestriction (L : S.Intertwiner T) :
    S.Space →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ T.Space where
  toLinearMap := L.toLinearMap
  map_lie' := L.differential _ _

/-- The same full intertwiner preserves the restricted compact Lie action. -/
def compactLieRestriction (L : S.Intertwiner T) :
    S.Space →ₗ⁅ℂ, ArchimedeanGL.CompactComplexLieAlgebra F n⁆ T.Space where
  toLinearMap := L.toLinearMap
  map_lie' := L.differential _ _

@[simp]
theorem complexLieRestriction_apply (L : S.Intertwiner T) (f : S.Space) :
    L.complexLieRestriction f = L f := rfl

@[simp]
theorem compactLieRestriction_apply (L : S.Intertwiner T) (f : S.Space) :
    L.compactLieRestriction f = L f := rfl

end Intertwiner

namespace Equivalence

variable {S T}

/-- Full equivalence retains the actual complex Lie module, on the same vectors. -/
def complexLieRestriction (e : S.Equivalence T) :
    S.Space ≃ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with map_lie' := Intertwiner.differential e.toIntertwiningMap _ _ }

/-- Full equivalence also retains the actual compact Lie module. -/
def compactLieRestriction (e : S.Equivalence T) :
    S.Space ≃ₗ⁅ℂ, ArchimedeanGL.CompactComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with map_lie' := Intertwiner.differential e.toIntertwiningMap _ _ }

@[simp]
theorem complexLieRestriction_apply (e : S.Equivalence T) (f : S.Space) :
    e.complexLieRestriction f = e f := rfl

@[simp]
theorem compactLieRestriction_apply (e : S.Equivalence T) (f : S.Space) :
    e.compactLieRestriction f = e f := rfl

end Equivalence
end OperatorRealization
end Langlands.Automorphic
