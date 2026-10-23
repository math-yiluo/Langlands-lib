import Langlands.AbelianScheme.Tate.RationalTransport
import Langlands.Shimura.PEL.OrbitTransport

/-! # Path-independent fixed orbits of actual adelic Tate frames -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u v w z

namespace Langlands.Shimura.PEL.LinearFrame

variable {R V W W' G Γ : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W'] [Group G] [Group Γ]

/-- The right action on linear frames by a given source representation. -/
@[instance_reducible] def rightAction (ρ : G →* (V ≃ₗ[R] V)) :
    MulAction Gᵐᵒᵖ (V ≃ₗ[R] W) where
  smul g eta := (ρ g.unop).trans eta
  one_smul eta := by
    apply LinearEquiv.ext
    intro x
    change eta (ρ 1 x) = eta x
    rw [map_one]
    rfl
  mul_smul g h eta := by
    apply LinearEquiv.ext
    intro x
    change eta (ρ (h.unop * g.unop) x) = eta (ρ h.unop (ρ g.unop x))
    rw [map_mul]
    rfl

/-- The left action on frames by a given target representation. -/
@[instance_reducible] def leftAction (τ : Γ →* (W ≃ₗ[R] W)) :
    MulAction Γ (V ≃ₗ[R] W) where
  smul γ eta := eta.trans (τ γ)
  one_smul eta := by
    apply LinearEquiv.ext
    intro x
    change τ 1 (eta x) = eta x
    rw [map_one]
    rfl
  mul_smul γ δ eta := by
    apply LinearEquiv.ext
    intro x
    change τ (γ * δ) (eta x) = τ γ (τ δ (eta x))
    rw [map_mul]
    rfl

/-- Source precomposition commutes with target postcomposition. -/
theorem actionsComm (ρ : G →* (V ≃ₗ[R] V)) (τ : Γ →* (W ≃ₗ[R] W)) :
    letI := rightAction (W := W) ρ
    letI := leftAction (V := V) τ
    SMulCommClass Γ Gᵐᵒᵖ (V ≃ₗ[R] W) := by
  let := rightAction (W := W) ρ
  let := leftAction (V := V) τ
  exact ⟨fun _ _ _ => by ext x; rfl⟩

/-- Postcompose linear frames by a target linear equivalence. -/
def postcomp (e : W ≃ₗ[R] W') : (V ≃ₗ[R] W) ≃ (V ≃ₗ[R] W') where
  toFun eta := eta.trans e
  invFun eta := eta.trans e.symm
  left_inv eta := by ext x; exact e.symm_apply_apply (eta x)
  right_inv eta := by ext x; exact e.apply_symm_apply (eta x)

end Langlands.Shimura.PEL.LinearFrame

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Shimura.PEL

variable {S : Scheme.{u}} (A : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  (s : Spec (.of Ω) ⟶ S)

/-- Tensor-algebra-linear frames in the actual full rational Tate module.
No condition on a Weil pairing is imposed here. -/
abbrev AdelicFrame :=
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] RationalFull A (Over.mk s)

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))

/-- Right precomposition on the actual Tate-frame space. -/
@[instance_reducible] def adelicFrameRightAction : MulAction Gᵐᵒᵖ (AdelicFrame A h i V s) := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  exact LinearFrame.rightAction ρ

variable (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- Left postcomposition by actual geometric Tate monodromy. -/
@[instance_reducible] def adelicFrameMonodromyAction :
    MulAction (FundamentalGroup s hs) (AdelicFrame A h i V s) := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  exact LinearFrame.leftAction
    (finiteAdeleAlgebraMonodromyRepresentation s hs htor A (fun _ => True) hu h i)

/-- The actual geometric left action commutes with right precomposition. -/
theorem adelicFrameActionsComm :
    letI := adelicFrameRightAction A h i V s ρ
    letI := adelicFrameMonodromyAction A h i V s hs htor hu
    SMulCommClass (FundamentalGroup s hs) Gᵐᵒᵖ (AdelicFrame A h i V s) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  exact LinearFrame.actionsComm ρ
    (finiteAdeleAlgebraMonodromyRepresentation s hs htor A (fun _ => True) hu h i)

/-- Geometrically fixed right orbits of actual Tate frames. These are ambient
linear-frame orbits; the Weil-form restriction is a separate construction. -/
abbrev AdelicFrameOrbit (U : Subgroup G) :=
  letI := adelicFrameRightAction A h i V s ρ
  letI := adelicFrameMonodromyAction A h i V s hs htor hu
  letI := adelicFrameActionsComm A h i V s ρ hs htor hu
  InvariantOrbit (X := AdelicFrame A h i V s) (FundamentalGroup s hs) U

variable {s} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

/-- Transport actual adelic Tate frames by the constructed geometric path map. -/
def adelicFrameTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    AdelicFrame A h i V s ≃ AdelicFrame A h i V t := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  exact LinearFrame.postcomp (finiteAdeleAlgebraTransport htor A (fun _ => True) hu h i p)

@[simp] theorem adelicFrameTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : AdelicFrame A h i V s) (x : V) :
    adelicFrameTransport A h i V htor hu p eta x =
      rationalTransport htor A (fun _ => True) hu p (eta x) := rfl

@[simp] theorem adelicFrameTransport_refl (eta : AdelicFrame A h i V s) :
    adelicFrameTransport A h i V htor hu (Iso.refl (fiberFunctor s hs)) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_refl htor A (fun _ => True) hu (eta x)

theorem adelicFrameTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (eta : AdelicFrame A h i V s) :
    adelicFrameTransport A h i V htor hu (p ≪≫ q) eta =
      adelicFrameTransport A h i V htor hu q (adelicFrameTransport A h i V htor hu p eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_trans htor A (fun _ => True) hu p q (eta x)

theorem adelicFrameTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (adelicFrameTransport A h i V htor hu p).symm =
      adelicFrameTransport A h i V htor hu p.symm := by
  apply Equiv.ext
  intro eta
  apply LinearEquiv.ext
  intro x
  rfl

/-- Path transport on fixed orbits of actual tensor-linear Tate frames. -/
def adelicFrameOrbitTransport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    AdelicFrameOrbit A h i V s ρ hs htor hu U ≃
      AdelicFrameOrbit A h i V t ρ ht htor hu U := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  letI := adelicFrameRightAction A h i V s ρ
  letI := adelicFrameRightAction A h i V t ρ
  letI := adelicFrameMonodromyAction A h i V s hs htor hu
  letI := adelicFrameMonodromyAction A h i V t ht htor hu
  letI := adelicFrameActionsComm A h i V s ρ hs htor hu
  letI := adelicFrameActionsComm A h i V t ρ ht htor hu
  exact InvariantOrbit.equiv U (pathConjugation p) (adelicFrameTransport A h i V htor hu p)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact rationalTransport_monodromy htor A (fun _ => True) hu p γ (eta x))

/-- The fixed-orbit equivalence is independent of the chosen geometric path. -/
theorem adelicFrameOrbitTransport_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    adelicFrameOrbitTransport A h i V ρ htor hu U p =
      adelicFrameOrbitTransport A h i V ρ htor hu U q := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameRightAction A h i V t ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameMonodromyAction A h i V t ht htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  let := adelicFrameActionsComm A h i V t ρ ht htor hu
  symm
  apply InvariantOrbit.equiv_eq_of_left U (pathConjugation p) (pathConjugation q)
    (adelicFrameTransport A h i V htor hu p) (adelicFrameTransport A h i V htor hu q)
    _ _ _ _ (p.symm ≪≫ q)
  intro eta
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_change_path htor A (fun _ => True) hu p q (eta x)

@[simp] theorem adelicFrameOrbitTransport_refl (U : Subgroup G) :
    adelicFrameOrbitTransport A h i V ρ htor hu U (Iso.refl (fiberFunctor s hs)) =
      Equiv.refl (AdelicFrameOrbit A h i V s ρ hs htor hu U) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameTransport_refl A h i V htor hu (hs := hs) eta)

theorem adelicFrameOrbitTransport_trans (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    adelicFrameOrbitTransport A h i V ρ htor hu U (p ≪≫ q) =
      (adelicFrameOrbitTransport A h i V ρ htor hu U p).trans
        (adelicFrameOrbitTransport A h i V ρ htor hu U q) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  let := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  let := adelicFrameRightAction A h i V t ρ
  let := adelicFrameMonodromyAction A h i V t ht htor hu
  let := adelicFrameActionsComm A h i V t ρ ht htor hu
  let := finiteAdeleAlgebraModule A (Over.mk r) (fun _ => True) h i
  let := adelicFrameRightAction A h i V r ρ
  let := adelicFrameMonodromyAction A h i V r hr htor hu
  let := adelicFrameActionsComm A h i V r ρ hr htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U) (adelicFrameTransport_trans A h i V htor hu p q eta)

theorem adelicFrameOrbitTransport_symm (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (adelicFrameOrbitTransport A h i V ρ htor hu U p).symm =
      adelicFrameOrbitTransport A h i V ρ htor hu U p.symm := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  let := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  let := adelicFrameRightAction A h i V t ρ
  let := adelicFrameMonodromyAction A h i V t ht htor hu
  let := adelicFrameActionsComm A h i V t ρ ht htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (adelicFrameTransport_symm A h i V htor hu p))

/-- Right translation between levels, on actual fixed Tate-frame orbits. -/
def adelicFrameOrbitTranslate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    AdelicFrameOrbit A h i V s ρ hs htor hu U →
      AdelicFrameOrbit A h i V s ρ hs htor hu U' := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  exact InvariantOrbit.translate g hg

/-- Forgetting a finer subgroup level. -/
def adelicFrameOrbitForget {U U' : Subgroup G} (hU : U ≤ U') :
    AdelicFrameOrbit A h i V s ρ hs htor hu U →
      AdelicFrameOrbit A h i V s ρ hs htor hu U' :=
  adelicFrameOrbitTranslate A h i V ρ htor hu 1 (by intro u hu; simpa using hU hu)

theorem adelicFrameOrbitTransport_translate {U U' : Subgroup G}
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    adelicFrameOrbitTransport A h i V ρ htor hu U' p
        (adelicFrameOrbitTranslate A h i V ρ htor hu g hg x) =
      adelicFrameOrbitTranslate A h i V ρ htor hu g hg
        (adelicFrameOrbitTransport A h i V ρ htor hu U p x) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  let := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  let := adelicFrameRightAction A h i V t ρ
  let := adelicFrameMonodromyAction A h i V t ht htor hu
  let := adelicFrameActionsComm A h i V t ρ ht htor hu
  exact InvariantOrbit.map_translate (pathConjugation p)
    (adelicFrameTransport A h i V htor hu p)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact rationalTransport_monodromy htor A (fun _ => True) hu p γ (eta x)) g hg x

theorem adelicFrameOrbitTransport_forget {U U' : Subgroup G}
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (hU : U ≤ U')
    (x : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    adelicFrameOrbitTransport A h i V ρ htor hu U' p
        (adelicFrameOrbitForget A h i V ρ htor hu hU x) =
      adelicFrameOrbitForget A h i V ρ htor hu hU
        (adelicFrameOrbitTransport A h i V ρ htor hu U p x) :=
  adelicFrameOrbitTransport_translate A h i V ρ htor hu p 1 _ x

end Langlands.AbelianScheme.Tate
