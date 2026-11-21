import Langlands.Global.EisensteinOperatorCoefficients

/-! # Descent from free operator modules to actual irreducible automorphic subquotients -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000

namespace Langlands.Automorphic

/-- The module structure given by a complex algebra action. -/
abbrev moduleOfAlgebraAction {R W : Type*} [Ring R] [Algebra ℂ R] [AddCommMonoid W]
    [Module ℂ W] (a : R →ₐ[ℂ] Module.End ℂ W) : Module R W :=
  Module.compHom W a.toRingHom

section AlgebraAction

variable {R W : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup W] [Module ℂ W]

private theorem isScalarTower_of_algebraAction (a : R →ₐ[ℂ] Module.End ℂ W) :
    letI := moduleOfAlgebraAction a
    IsScalarTower ℂ R W := by
  let := moduleOfAlgebraAction a
  refine ⟨fun c r v => ?_⟩
  change a (c • r) v = c • a r v
  rw [map_smul, LinearMap.smul_apply]

/-- For an algebra action, invariant complex subspaces are exactly the operator submodules. -/
def submoduleOrderIsoOfAlgebraAction (a : R →ₐ[ℂ] Module.End ℂ W) :
    letI := moduleOfAlgebraAction a
    Submodule R W ≃o Subrepresentation a.toMonoidHom := by
  letI := moduleOfAlgebraAction a
  letI := isScalarTower_of_algebraAction a
  exact
    { toFun S := ⟨S.restrictScalars ℂ, fun r _ hv => S.smul_mem r hv⟩
      invFun S :=
        { carrier := S.toSubmodule
          zero_mem' := S.toSubmodule.zero_mem
          add_mem' := fun hv hw => S.toSubmodule.add_mem hv hw
          smul_mem' := fun r _ hv => S.apply_mem_toSubmodule r hv }
      left_inv _ := SetLike.ext fun _ => Iff.rfl
      right_inv _ := SetLike.ext fun _ => Iff.rfl
      map_rel_iff' := Iff.rfl }

/-- Simplicity for the algebra is irreducibility of its multiplicative representation. -/
theorem isSimpleModule_iff_irreducible_algebraAction (a : R →ₐ[ℂ] Module.End ℂ W) :
    letI := moduleOfAlgebraAction a
    IsSimpleModule R W ↔ Representation.IsIrreducible a.toMonoidHom := by
  let := moduleOfAlgebraAction a
  rw [isSimpleModule_iff]
  exact (submoduleOrderIsoOfAlgebraAction a).isSimpleOrder_iff

end AlgebraAction

open Langlands.Global EisensteinJet

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "Operators" => FreeOperatorAlgebra F (r + 1)
local notation "Stable" => StableAutomorphicFunctions F (r + 1)

local instance descentRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance descentContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance descentSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance descentStableAddCommGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance descentStableComplexModule : Module ℂ Stable := Submodule.module _

/-- A simple quotient of a stable free-operator submodule descends to an
actual automorphic quotient and retains the finite adelic representation. -/
theorem exists_irreducibleOperatorSubquotient_of_freeModule
    {W : Type*} [AddCommGroup W] [Module ℂ W] (a : Operators →ₐ[ℂ] Module.End ℂ W)
    (ha : Representation.IsIrreducible a.toMonoidHom) (fin : Representation ℂ (FiniteAdelicGL F (r + 1)) W)
    (hfin : ∀ g, a (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) = fin g) :
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
    letI := moduleOfAlgebraAction a
    ∀ (S : Submodule Operators Stable) (q : S →ₗ[Operators] W), Function.Surjective q →
      ∃ Q : IrreducibleOperatorSubquotient F r, Nonempty (Q.subquotient.finiteRepresentation.Equiv fin) := by
  let := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
  let := moduleOfAlgebraAction a
  let := isScalarTower_of_algebraAction (stableFreeOperatorAction F (r + 1))
  let := isScalarTower_of_algebraAction a
  intro S q hq
  let P := freeOperatorProjection F (r + 1)
  let U : Subrepresentation ((stableAutomorphicAction F (r + 1)).comp P.toMonoidHom) :=
    { toSubmodule := S.restrictScalars ℂ
      apply_mem_toSubmodule b v hv := by
        change stableAutomorphicAction F (r + 1) (P b) v ∈ S
        rw [← stableFreeOperatorAction_apply]
        exact S.smul_mem b hv }
  let q' : U.toRepresentation.IntertwiningMap a.toMonoidHom :=
    { toLinearMap := q.restrictScalars ℂ
      isIntertwining' := by
        intro b
        apply LinearMap.ext
        intro v
        have hval : (U.toRepresentation b v : Stable) = b • (v : Stable) :=
          (stableFreeOperatorAction_apply F (r + 1) b v.val).symm
        have hv : U.toRepresentation b v = (b • (v : S) : S) := Subtype.ext hval
        change q (U.toRepresentation b v) = a b (q v)
        rw [hv]
        exact q.map_smul b (v : S) }
  exact exists_irreducibleOperatorSubquotient_of_pullback P.toMonoidHom
    (freeOperatorProjection_surjective F (r + 1)) ha U q' hq
    (fun g => FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g)))
    (fun g => freeOperatorProjection_ι F (r + 1) (Sum.inl (Sum.inl g))) fin hfin

end Langlands.Automorphic
