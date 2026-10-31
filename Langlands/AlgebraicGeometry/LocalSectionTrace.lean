import Langlands.AlgebraicGeometry.LocalSectionIso
import Mathlib.LinearAlgebra.Trace

/-! # Traces on actual local module sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    {I : Type u} [Fintype I] {M N : X.Modules}

local instance : DecidableEq I := Classical.decEq I

/-- The matrix trace of an actual sheaf endomorphism in a finite free chart. -/
def localSectionTrace
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : End (M.over U)) (V : Over U) : Γ(X, V.left) :=
  Matrix.trace (LinearMap.toMatrix (localSectionBasis e V) (localSectionBasis e V)
    (localSectionEndomorphism M V f))

/-- The constructed trace is the intrinsic trace of the actual section action. -/
theorem localSectionTrace_eq_trace
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : End (M.over U)) (V : Over U) :
    localSectionTrace e f V =
      LinearMap.trace Γ(X, V.left) Γ(M, V.left) (localSectionEndomorphism M V f) :=
  (LinearMap.trace_eq_matrix_trace _ (localSectionBasis e V) _).symm

/-- Any finite basis of the actual section module computes the same trace. -/
theorem localSectionTrace_eq_basis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : End (M.over U)) (V : Over U)
    {J : Type u} [Fintype J] [DecidableEq J]
    (b : Module.Basis J Γ(X, V.left) Γ(M, V.left)) :
    localSectionTrace e f V =
      Matrix.trace (LinearMap.toMatrix b b (localSectionEndomorphism M V f)) := by
  rw [localSectionTrace_eq_trace, LinearMap.trace_eq_matrix_trace _ b]

/-- Finite charts with different index types give the same trace. -/
theorem localSectionTrace_trivialization_independent
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U)
    (f : End (M.over U)) (V : Over U) :
    localSectionTrace e f V = localSectionTrace e' f V := by
  rw [localSectionTrace_eq_trace, localSectionTrace_eq_trace]

/-- The trace is additive in the actual sheaf endomorphism. -/
def localSectionTraceAddHom
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) : End (M.over U) →+ Γ(X, V.left) :=
  (LinearMap.traceAux Γ(X, V.left) (localSectionBasis e V)).toAddMonoidHom.comp
    (localSectionEndomorphism M V).toAddMonoidHom

@[simp]
theorem localSectionTraceAddHom_apply
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) (f : End (M.over U)) :
    localSectionTraceAddHom e V f = localSectionTrace e f V :=
  rfl

/-- The trace of the identity records the size of the finite free chart. -/
@[simp]
theorem localSectionTrace_one
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) :
    localSectionTrace e 1 V = (Fintype.card I : Γ(X, V.left)) := by
  unfold localSectionTrace
  rw [map_one, LinearMap.toMatrix_one]
  simp

/-- The trace restricts through the actual structure-sheaf restriction map. -/
theorem localSectionTrace_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (f : End (M.over U)) {V W : Over U} (j : V ⟶ W) :
    X.presheaf.map j.left.op (localSectionTrace e f W) = localSectionTrace e f V := by
  simp only [localSectionTrace, Matrix.trace, Matrix.diag_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    (localSectionEndomorphism_toMatrix_restrict e j f i i).symm)

/-- An actual intertwining sheaf isomorphism preserves the trace. -/
theorem localSectionTrace_iso
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    (a : End (M.over U)) (b : End (N.over U))
    (hab : a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    localSectionTrace e a V = localSectionTrace (e ≪≫ h) b V :=
  congrArg Matrix.trace (localSectionEndomorphism_toMatrix_iso e h a b hab V)

/-- Every finite target chart computes the trace transported by a sheaf isomorphism. -/
theorem localSectionTrace_iso_any_chart
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ N.over U)
    (a : End (M.over U)) (b : End (N.over U))
    (hab : a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    localSectionTrace e a V = localSectionTrace e' b V := by
  rw [localSectionTrace_iso e h a b hab V]
  exact localSectionTrace_trivialization_independent _ _ b V

end Langlands.Scheme.Modules
