import Langlands.Global.RankinSelberg.CuspidalTransposePairingReduction
import Langlands.Automorphic.CuspidalInvariantPairingCriterion

/-! # The cuspidal transpose reduction needs only a nonzero invariant form -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

open NumberField Global Automorphic

local instance nonzeroTransposeRationalGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance nonzeroTransposeContinuousGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance nonzeroTransposeSmoothGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance nonzeroTransposeFormsGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance nonzeroTransposeStableGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance nonzeroTransposeOperatorSpaceGroup
    {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace Automorphic.OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {S T : OperatorRealization F n}

private theorem inverse_covariance {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) {A : V → V} {A' : W → W}
    (h : ∀ x, e (A x) = A' (e x)) (x : W) :
    e.symm (A' x) = A (e.symm x) := by
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using
    (congrArg e.symm (h (e.symm x))).symm

/-- Pulling back the second variable along the actual transpose equivalence
transports just the invariance conditions, with no range hypothesis. -/
theorem IsTransposeIntertwining.isInvariantPairing_compl₂_symm
    {e : S.Space ≃ₗ[ℂ] T.Space} (he : S.IsTransposeIntertwining T e)
    {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ} (hB : S.IsTransposeInvariantPairing B) :
    S.IsInvariantPairing T (B.compl₂ e.symm.toLinearMap) := by
  rcases hB with ⟨hd, hk, hX⟩
  constructor
  · intro d y x
    change B (S.finiteRepresentation d y) (e.symm (T.finiteRepresentation d x)) =
      B y (e.symm x)
    exact (congrArg (B (S.finiteRepresentation d y))
      (inverse_covariance e (he.1 d) x)).trans (hd d y (e.symm x))
  constructor
  · intro k y x
    change B (S.compactRepresentation k y) (e.symm (T.compactRepresentation k x)) =
      B y (e.symm x)
    exact (congrArg (B (S.compactRepresentation k y))
      (inverse_covariance e (he.2.1 k) x)).trans (hk k y (e.symm x))
  · intro X y x
    change B (S.lieAction X y) (e.symm x) +
      B y (e.symm (T.lieAction X x)) = 0
    exact (congrArg (fun z => B (S.lieAction X y) (e.symm x) + B y z)
      (inverse_covariance e (he.2.2 X) x)).trans (hX X y (e.symm x))

end Automorphic.OperatorRealization

namespace Global.RankinSelbergGlobal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- A nonzero intrinsic invariant form suffices for contragredience of the
actual cuspidal transpose realization. -/
theorem cuspidalTranspose_isContragredientOf_of_nonzero
    {B : T.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ}
    (hB : T.realization.IsTransposeInvariantPairing B) (hB0 : B ≠ 0) :
    T.transpose.realization.IsContragredientOf T.realization := by
  let e := T.transposeEquiv
  have hC : T.realization.IsInvariantPairing T.transpose.realization
      (B.compl₂ e.symm.toLinearMap) :=
    (cuspidalTransposeEquiv_isTransposeIntertwining T).isInvariantPairing_compl₂_symm hB
  have hC0 : B.compl₂ e.symm.toLinearMap ≠ 0 := by
    intro h
    apply hB0
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    have hyx := congrArg (fun C : T.Space →ₗ[ℂ] T.transpose.Space →ₗ[ℂ] ℂ =>
      C y (e x)) h
    change B y (e.symm (e x)) = 0 at hyx
    simpa only [LinearEquiv.symm_apply_apply, map_zero, LinearMap.zero_apply] using hyx
  exact CuspidalOperatorRealization.isContragredientOf_of_nonzero_invariant hC hC0

/-- The remaining existence premise asks only for a nonzero invariant form
on each original cuspidal realization with its transpose-twisted actions. -/
def CuspidalNonzeroTransposePairingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    ∃ B : T.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ,
      T.realization.IsTransposeInvariantPairing B ∧ B ≠ 0

/-- Conditional reduction of the exact global target to nonzero invariant
transpose pairing existence, in the same free field universe. -/
def CuspidalNonzeroTransposePairingReductionStatement : Prop :=
  CuspidalNonzeroTransposePairingStatement.{u} →
    CuspidalTransposeInverseContragredientStatement.{u}

/-- The actual transpose realization supplies all dual cusp forms; the
nonzero invariant form supplies its contragredient identification. -/
theorem cuspidalNonzeroTransposePairingReduction :
    CuspidalNonzeroTransposePairingReductionStatement.{u} := by
  intro h F _ _ _ r T
  obtain ⟨B, hB, hB0⟩ := h F r T
  refine ⟨T.transpose, cuspidalTranspose_isContragredientOf_of_nonzero T hB hB0, ?_⟩
  intro x
  exact ⟨T.transposeEquiv x, cuspFunction_transposeEquiv T x⟩

end Global.RankinSelbergGlobal
end Langlands
