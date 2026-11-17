import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Automorphic.CuspidalConjugateRealization
import Langlands.Automorphic.OperatorHilbertCompletion

/-! # Recovering joint finite vectors in the actual Hilbert completion -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands

universe uG uK uV uH

section DenseJointRealization

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type uK} [Group K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Representation ℂ G V} {κ : Representation ℂ K V}

/-- Restrict the Hilbert inner product in its linear argument to the dense carrier. -/
def denseInnerFunctional (j : V →ₗ[ℂ] H) : H →ₗ⋆[ℂ] Module.Dual ℂ V where
  toFun x := (innerₛₗ ℂ x).comp j
  map_add' x y := LinearMap.ext fun v => inner_add_left x y (j v)
  map_smul' a x := LinearMap.ext fun v => inner_smul_left x (j v) a

@[simp]
theorem denseInnerFunctional_apply (j : V →ₗ[ℂ] H) (x : H) (v : V) :
    denseInnerFunctional j x v = Inner.inner ℂ x (j v) := rfl

/-- Unitary equivariance in the target gives dual covariance of the restricted
inner-product functional. -/
theorem denseInnerFunctional_dual
    {A : Type*} [Group A] (δ : Representation ℂ A V) (γ : Representation ℂ A H)
    (j : V →ₗ[ℂ] H)
    (hγ : ∀ a x y, Inner.inner ℂ (γ a x) (γ a y) = Inner.inner ℂ x y)
    (hj : ∀ a v, j (δ a v) = γ a (j v)) (a : A) (x : H) :
    δ.dual a (denseInnerFunctional j x) = denseInnerFunctional j (γ a x) := by
  apply LinearMap.ext
  intro v
  change Inner.inner ℂ x (j (δ a⁻¹ v)) = Inner.inner ℂ (γ a x) (j v)
  calc
    _ = Inner.inner ℂ (γ a x) (γ a (j (δ a⁻¹ v))) :=
      (hγ a x (j (δ a⁻¹ v))).symm
    _ = Inner.inner ℂ (γ a x) (j v) := by
      rw [← hj, Representation.self_inv_apply]

/-- Joint admissibility recovers exactly the vectors that are smooth for the
first action and finite for the second in a dense unitary realization. -/
theorem jointVectorRecovery_of_dense
    (b : InvariantPositiveForm ρ)
    (hb : ∀ k v w, b.inner (κ k v) (κ k w) = b.inner v w)
    (hcomm : ∀ d k v, ρ d (κ k v) = κ k (ρ d v))
    (hsmooth : IsSmooth ρ) (hfinite : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (hcofinal : ∀ L : OpenSubgroup G,
      ∃ L₀ : OpenSubgroup G, L₀ ≤ L ∧ IsCompact (L₀ : Set G))
    (hA : IsJointlyAdmissible ρ κ)
    (σ : Representation ℂ G H) (τ : Representation ℂ K H)
    (hσ : ∀ d x y, Inner.inner ℂ (σ d x) (σ d y) = Inner.inner ℂ x y)
    (hτ : ∀ k x y, Inner.inner ℂ (τ k x) (τ k y) = Inner.inner ℂ x y)
    (j : V →ₗ[ℂ] H) (hdense : DenseRange j)
    (hform : ∀ v w, Inner.inner ℂ (j v) (j w) = b.inner v w)
    (hjG : ∀ d v, j (ρ d v) = σ d (j v))
    (hjK : ∀ k v, j (κ k v) = τ k (j v)) (x : H) :
    (IsSmoothVector σ x ∧ FiniteVectors.IsFiniteVector τ x) ↔
      ∃ v : V, j v = x := by
  constructor
  · rintro ⟨hxG, hxK⟩
    let l := denseInnerFunctional j x
    have hlG : IsSmoothVector ρ.dual l := by
      obtain ⟨L, hL⟩ := hxG
      refine ⟨L, fun d => ?_⟩
      exact (denseInnerFunctional_dual ρ σ j hσ hjG d x).trans
        (congrArg (denseInnerFunctional j) (hL d))
    have hlK : FiniteVectors.IsFiniteVector κ.dual l :=
      hxK.antilinear κ.dual (denseInnerFunctional j)
        (fun k => ⟨k, denseInnerFunctional_dual κ τ j hτ hjK k x⟩)
    obtain ⟨v, hv⟩ := b.exists_inner_eq_of_contragredient
      hb hcomm hsmooth hfinite hcofinal hA hlG hlK
    exact ⟨v, hdense.eq_of_inner_left ℂ fun w => (hform v w).trans (hv w)⟩
  · rintro ⟨v, rfl⟩
    let jG : ρ.IntertwiningMap σ :=
      { toLinearMap := j
        isIntertwining' d := LinearMap.ext (hjG d) }
    let jK : κ.IntertwiningMap τ :=
      { toLinearMap := j
        isIntertwining' k := LinearMap.ext (hjK k) }
    exact ⟨isSmoothVector_map jG (hsmooth v), (hfinite v).map jK⟩

end DenseJointRealization
end Langlands

namespace Langlands.Automorphic.OperatorUnitaryFormCore

universe uG uK uV uX

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} {ρ : Representation ℂ G V} {κ : Representation ℂ K V}
  {D : X → Module.End ℂ V}

/-- The original carrier is exactly the smooth/finite part of its completion
for the finite and compact actions, respectively. -/
def JointVectorRecovery (b : OperatorUnitaryFormCore ρ κ D) : Prop :=
  ∀ x : b.finiteForm.HilbertCompletion,
    (Langlands.IsSmoothVector b.completedFiniteRepresentation x ∧
      Langlands.FiniteVectors.IsFiniteVector b.completedCompactRepresentation x) ↔
        ∃ v : V, b.finiteForm.toHilbert v = x

/-- Joint admissibility supplies recovery for the common Hilbert completion. -/
theorem jointVectorRecovery (b : OperatorUnitaryFormCore ρ κ D)
    (hcomm : ∀ d k v, ρ d (κ k v) = κ k (ρ d v))
    (hsmooth : Langlands.IsSmooth ρ)
    (hfinite : ∀ v, Langlands.FiniteVectors.IsFiniteVector κ v)
    (hcofinal : ∀ L : OpenSubgroup G,
      ∃ L₀ : OpenSubgroup G, L₀ ≤ L ∧ IsCompact (L₀ : Set G))
    (hA : Langlands.IsJointlyAdmissible ρ κ) : JointVectorRecovery b :=
  Langlands.jointVectorRecovery_of_dense b.finiteForm b.compact_invariant
    hcomm hsmooth hfinite hcofinal hA
    b.completedFiniteRepresentation b.completedCompactRepresentation
    b.finiteForm.completedRepresentation_inner b.compactInvariantForm.completedRepresentation_inner
    b.finiteForm.toHilbert b.finiteForm.denseRange_toHilbert b.finiteForm.inner_toHilbert
    (fun d v => (b.completedFiniteRepresentation_toHilbert d v).symm)
    (fun k v => (b.completedCompactRepresentation_toHilbert k v).symm)

end Langlands.Automorphic.OperatorUnitaryFormCore

namespace Langlands.Automorphic

open Langlands.Global
universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance recoveryRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance recoveryContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance recoverySmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance recoveryFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance recoveryStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance recoverySpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n}

/-- Recovery on an actual jointly admissible operator realization needs no
irreducibility premise or new archimedean globalization. -/
theorem jointVectorRecovery (b : S.UnitaryForm) (hA : S.IsJointlyAdmissible) :
    OperatorUnitaryFormCore.JointVectorRecovery b :=
  OperatorUnitaryFormCore.jointVectorRecovery b
    S.finiteRepresentation_compactRepresentation S.finiteRepresentation_isSmooth
    S.compactRepresentation_isFiniteVector OperatorRealization.exists_compact_openSubgroup_le hA

end OperatorRealization.UnitaryForm

/-- All finite-smooth, compact-finite vectors of the prescribed Hilbert completion
of a jointly admissible actual realization come from its original carrier. -/
def OperatorJointVectorRecoveryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : OperatorRealization F n),
    S.IsJointlyAdmissible → ∀ b : S.UnitaryForm,
      OperatorUnitaryFormCore.JointVectorRecovery b

/-- Joint-vector recovery for actual operator Hilbert completions. -/
theorem operatorJointVectorRecovery : OperatorJointVectorRecoveryStatement.{u} := by
  intro F _ _ n S hA b
  exact b.jointVectorRecovery hA

end Langlands.Automorphic
