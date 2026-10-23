import Langlands.AbelianScheme.Tate.AdelicFrameTransport

/-! # Path-independent fixed orbits of actual prime-to-modulus adelic Tate frames -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u v w z

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Shimura.PEL

variable {S : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  (s : Spec (.of Ω) ⟶ S)

/-- Tensor-algebra-linear frames in the actual prime-to-modulus rational Tate module.
No condition on a Weil pairing is imposed here. -/
abbrev PrimeToAdelicFrame :=
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] RationalAway A (Over.mk s) m

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))

/-- Right precomposition on the actual Tate-frame space. -/
@[instance_reducible] def primeToAdelicFrameRightAction : MulAction Gᵐᵒᵖ (PrimeToAdelicFrame A m hAway i V s) := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact LinearFrame.rightAction ρ

variable (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- Left postcomposition by actual geometric Tate monodromy. -/
@[instance_reducible] def primeToAdelicFrameMonodromyAction :
    MulAction (FundamentalGroup s hs) (PrimeToAdelicFrame A m hAway i V s) := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact LinearFrame.leftAction
    (primeToFiniteAdeleAlgebraMonodromyRepresentation s hs htor A m hu hAway i)

/-- The actual geometric left action commutes with right precomposition. -/
theorem primeToAdelicFrameActionsComm :
    letI := primeToAdelicFrameRightAction A m hAway i V s ρ
    letI := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
    SMulCommClass (FundamentalGroup s hs) Gᵐᵒᵖ (PrimeToAdelicFrame A m hAway i V s) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact LinearFrame.actionsComm ρ
    (primeToFiniteAdeleAlgebraMonodromyRepresentation s hs htor A m hu hAway i)

/-- Geometrically fixed right orbits of actual Tate frames. These are ambient
linear-frame orbits; the Weil-form restriction is a separate construction. -/
abbrev PrimeToAdelicFrameOrbit (U : Subgroup G) :=
  letI := primeToAdelicFrameRightAction A m hAway i V s ρ
  letI := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  letI := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  InvariantOrbit (X := PrimeToAdelicFrame A m hAway i V s) (FundamentalGroup s hs) U

variable {s} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

/-- Transport actual prime-to-modulus adelic Tate frames by the constructed geometric path map. -/
def primeToAdelicFrameTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    PrimeToAdelicFrame A m hAway i V s ≃ PrimeToAdelicFrame A m hAway i V t := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  exact LinearFrame.postcomp (primeToFiniteAdeleAlgebraTransport htor A m hu hAway i p)

@[simp] theorem primeToAdelicFrameTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : PrimeToAdelicFrame A m hAway i V s) (x : V) :
    primeToAdelicFrameTransport A m hAway i V htor hu p eta x =
      rationalTransport htor A (fun n => Nat.Coprime n m) hu p (eta x) := rfl

@[simp] theorem primeToAdelicFrameTransport_refl (eta : PrimeToAdelicFrame A m hAway i V s) :
    primeToAdelicFrameTransport A m hAway i V htor hu (Iso.refl (fiberFunctor s hs)) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_refl htor A (fun n => Nat.Coprime n m) hu (eta x)

theorem primeToAdelicFrameTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (eta : PrimeToAdelicFrame A m hAway i V s) :
    primeToAdelicFrameTransport A m hAway i V htor hu (p ≪≫ q) eta =
      primeToAdelicFrameTransport A m hAway i V htor hu q (primeToAdelicFrameTransport A m hAway i V htor hu p eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_trans htor A (fun n => Nat.Coprime n m) hu p q (eta x)

theorem primeToAdelicFrameTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (primeToAdelicFrameTransport A m hAway i V htor hu p).symm =
      primeToAdelicFrameTransport A m hAway i V htor hu p.symm := by
  apply Equiv.ext
  intro eta
  apply LinearEquiv.ext
  intro x
  rfl

/-- Path transport on fixed orbits of actual tensor-linear Tate frames. -/
def primeToAdelicFrameOrbitTransport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit A m hAway i V t ρ ht htor hu U := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  letI := primeToAdelicFrameRightAction A m hAway i V s ρ
  letI := primeToAdelicFrameRightAction A m hAway i V t ρ
  letI := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  letI := primeToAdelicFrameMonodromyAction A m hAway i V t ht htor hu
  letI := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  letI := primeToAdelicFrameActionsComm A m hAway i V t ρ ht htor hu
  exact InvariantOrbit.equiv U (pathConjugation p) (primeToAdelicFrameTransport A m hAway i V htor hu p)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact rationalTransport_monodromy htor A (fun n => Nat.Coprime n m) hu p γ (eta x))

/-- The fixed-orbit equivalence is independent of the chosen geometric path. -/
theorem primeToAdelicFrameOrbitTransport_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p =
      primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U q := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameRightAction A m hAway i V t ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameMonodromyAction A m hAway i V t ht htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V t ρ ht htor hu
  symm
  apply InvariantOrbit.equiv_eq_of_left U (pathConjugation p) (pathConjugation q)
    (primeToAdelicFrameTransport A m hAway i V htor hu p) (primeToAdelicFrameTransport A m hAway i V htor hu q)
    _ _ _ _ (p.symm ≪≫ q)
  intro eta
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_change_path htor A (fun n => Nat.Coprime n m) hu p q (eta x)

@[simp] theorem primeToAdelicFrameOrbitTransport_refl (U : Subgroup G) :
    primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U (Iso.refl (fiberFunctor s hs)) =
      Equiv.refl (PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameTransport_refl A m hAway i V htor hu (hs := hs) eta)

theorem primeToAdelicFrameOrbitTransport_trans (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U (p ≪≫ q) =
      (primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p).trans
        (primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U q) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V t ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V t ht htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V t ρ ht htor hu
  let := primeToFiniteAdeleAlgebraModule A (Over.mk r) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V r ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V r hr htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V r ρ hr htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U) (primeToAdelicFrameTransport_trans A m hAway i V htor hu p q eta)

theorem primeToAdelicFrameOrbitTransport_symm (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p).symm =
      primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p.symm := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V t ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V t ht htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V t ρ ht htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitTransport, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (primeToAdelicFrameTransport_symm A m hAway i V htor hu p))

/-- Right translation between levels, on actual fixed Tate-frame orbits. -/
def primeToAdelicFrameOrbitTranslate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U →
      PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U' := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  exact InvariantOrbit.translate g hg

/-- Forgetting a finer subgroup level. -/
def primeToAdelicFrameOrbitForget {U U' : Subgroup G} (hU : U ≤ U') :
    PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U →
      PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U' :=
  primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu 1 (by intro u hu; simpa using hU hu)

theorem primeToAdelicFrameOrbitTransport_translate {U U' : Subgroup G}
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U' p
        (primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg x) =
      primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg
        (primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p x) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  let := primeToAdelicFrameRightAction A m hAway i V t ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V t ht htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V t ρ ht htor hu
  exact InvariantOrbit.map_translate (pathConjugation p)
    (primeToAdelicFrameTransport A m hAway i V htor hu p)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact rationalTransport_monodromy htor A (fun n => Nat.Coprime n m) hu p γ (eta x)) g hg x

theorem primeToAdelicFrameOrbitTransport_forget {U U' : Subgroup G}
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (hU : U ≤ U')
    (x : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U' p
        (primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU x) =
      primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU
        (primeToAdelicFrameOrbitTransport A m hAway i V ρ htor hu U p x) :=
  primeToAdelicFrameOrbitTransport_translate A m hAway i V ρ htor hu p 1 _ x

end Langlands.AbelianScheme.Tate
