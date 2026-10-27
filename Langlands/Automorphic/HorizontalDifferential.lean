import Langlands.Automorphic.ReducedCochainCompactDifferentiation
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Cohomology.Lie.HorizontalDifferential

/-! # The actual horizontal differential on an automorphic realization -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Restrict the genuine differential action to the actual reduced algebra. -/
def reducedLieAction : ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.complexLieAction.comp (reducedComplexInclusion F n)

@[simp]
theorem reducedLieAction_apply (X : ReducedComplexLieAlgebra F n) (f : S.Space) :
    S.reducedLieAction X f = S.complexLieAction (reducedComplexInclusion F n X) f := rfl

instance reducedLieRingModule : LieRingModule (ReducedComplexLieAlgebra F n) S.Space :=
  LieRingModule.compLieHom S.Space (reducedComplexInclusion F n)

instance reducedLieModule : LieModule ℂ (ReducedComplexLieAlgebra F n) S.Space :=
  LieModule.compLieHom S.Space (reducedComplexInclusion F n)

@[simp]
theorem reduced_lie_eq (X : ReducedComplexLieAlgebra F n) (f : S.Space) :
    ⁅X, f⁆ = S.reducedLieAction X f := rfl

/-- Restriction through the compact image agrees with the existing compact action. -/
theorem reducedLieAction_compact (Y : CompactComplexLieAlgebra F n) :
    S.reducedLieAction (compactToReducedComplex F n Y) = S.compactLieAction Y := by
  change S.complexLieAction (reducedComplexInclusion F n
    (compactToReducedComplex F n Y)) = _
  rw [reducedComplexInclusion_compact]
  rfl

/-- The reduced action commutes with actual finite adelic translation. -/
theorem finiteRepresentation_reducedLieAction (d : FiniteAdelicGL F n)
    (X : ReducedComplexLieAlgebra F n) (f : S.Space) :
    S.finiteRepresentation d (S.reducedLieAction X f) =
      S.reducedLieAction X (S.finiteRepresentation d f) :=
  S.finiteRepresentation_complexLieAction d (reducedComplexInclusion F n X) f

/-- Full compact covariance is inherited from the proved enveloping covariance. -/
theorem compactRepresentation_reducedLieAction (k : standardInfiniteCompact F n)
    (X : ReducedComplexLieAlgebra F n) (f : S.Space) :
    S.compactRepresentation k (S.reducedLieAction X f) =
      S.reducedLieAction (reducedCompactRepresentation F n k X)
        (S.compactRepresentation k f) := by
  simpa only [reducedLieAction_apply, reducedCompactRepresentation_apply,
    reducedComplexInclusion_conjugation] using
    S.compactRepresentation_complexLieAction k (reducedComplexInclusion F n X) f

namespace Intertwiner

variable {S T}

/-- The same full operator intertwiner is a map of reduced Lie modules. -/
def reducedLieRestriction (A : S.Intertwiner T) :
    S.Space →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ T.Space where
  toLinearMap := A.toLinearMap
  map_lie' := A.differential _ _

@[simp]
theorem reducedLieRestriction_apply (A : S.Intertwiner T) (f : S.Space) :
    A.reducedLieRestriction f = A f := rfl

end Intertwiner

namespace Equivalence

variable {S T}

/-- A full equivalence retains the actual reduced Lie action. -/
def reducedLieRestriction (e : S.Equivalence T) :
    S.Space ≃ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with
    map_lie' := Intertwiner.differential e.toIntertwiningMap _ _ }

@[simp]
theorem reducedLieRestriction_apply (e : S.Equivalence T) (f : S.Space) :
    e.reducedLieRestriction f = e f := rfl

end Equivalence

variable [NeZero n]

/-- Derive the horizontal insertion identity from actual full compact equivariance. -/
theorem horizontalCochain_infinitesimal (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ horizontalEquivariantSubmodule F n S.compactRepresentation q)
    (Y : ReducedComplexLieAlgebra F n) (hY : Y ∈ compactInReducedSubmodule F n)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    ⁅Y, f X⁆ = ∑ i, f (Function.update X i ⁅Y, X i⁆) := by
  obtain ⟨Z, rfl⟩ := hY
  change S.complexLieAction
    (reducedComplexInclusion F n (compactToReducedComplex F n Z)) (f X) = _
  rw [reducedComplexInclusion_compact]
  exact S.reducedCochain_compact_complex q f hf.2 Z X

/-- The actual coefficient differential restricted to the full compact horizontal space. -/
def horizontalDifferential (q : ℕ) :
    horizontalEquivariantSubmodule F n S.compactRepresentation q →ₗ[ℂ]
      horizontalEquivariantSubmodule F n S.compactRepresentation (q + 1) :=
  Langlands.Cohomology.Lie.horizontalEquivariantDifferential
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    S.compactRepresentation
    (fun k X Y => (reducedComplexLieConjugation F n k.val).map_lie X Y)
    (S.compactRepresentation_reducedLieAction) q (S.horizontalCochain_infinitesimal q)

@[simp]
theorem horizontalDifferential_val (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    (S.horizontalDifferential q f).val =
      Langlands.Cohomology.Lie.differential q f.val := rfl

@[simp]
theorem horizontalDifferential_apply (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q)
    (X : Fin (q + 1) → ReducedComplexLieAlgebra F n) :
    (S.horizontalDifferential q f).val X =
      Langlands.Cohomology.Lie.differential q f.val X := rfl

end OperatorRealization
end Langlands.Automorphic
