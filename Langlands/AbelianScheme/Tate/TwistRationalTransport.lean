import Langlands.AbelianScheme.Tate.TwistIntegralTransport
import Langlands.AbelianScheme.Tate.TwistRationalMonodromy

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (P : ℕ → Prop)
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Rational scalar extension of actual geometric transport on coherent roots. -/
def rationalTransportMap (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Rational Ω P →ₗ[ℚ] Divisibility.Rational Ω' P :=
  (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalTransportMap_tmul (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : ℚ) (x : Divisibility.Integral Ω P) :
    rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralTransport P (hμfin := hμfin) (hμet := hμet) γ x := rfl

@[simp] theorem rationalTransportMap_refl (x : Divisibility.Rational Ω P) :
    rationalTransportMap P (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp
  | add x y hx hy => simp_all

theorem rationalTransportMap_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Divisibility.Rational Ω P) :
    rationalTransportMap P (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      rationalTransportMap P (hμfin := hμfin) (hμet := hμet) δ
        (rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp [integralTransport_trans]
  | add x y hx hy => simp_all

/-- Rational root path transport, inverted by reversing the same geometric path. -/
def rationalTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Rational Ω P ≃ₗ[ℚ] Divisibility.Rational Ω' P :=
  { rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ with
    invFun := rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ.symm
    left_inv := fun x => by
      change rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ.symm
        (rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ x) = x
      rw [← rationalTransportMap_trans]
      simp
    right_inv := fun x => by
      change rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ
        (rationalTransportMap P (hμfin := hμfin) (hμet := hμet) γ.symm x) = x
      rw [← rationalTransportMap_trans]
      simp }

@[simp] theorem rationalTransport_tmul (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : ℚ) (x : Divisibility.Integral Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) γ (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralTransport P (hμfin := hμfin) (hμet := hμet) γ x := rfl

@[simp] theorem rationalTransport_refl (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x :=
  rationalTransportMap_refl P (hμfin := hμfin) (hμet := hμet) x

theorem rationalTransport_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      rationalTransport P (hμfin := hμfin) (hμet := hμet) δ
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) :=
  rationalTransportMap_trans P (hμfin := hμfin) (hμet := hμet) γ δ x

theorem rationalTransport_symm (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ).symm =
      rationalTransport P (hμfin := hμfin) (hμet := hμet) γ.symm := rfl

/-- For loops this is exactly the published rational geometric root action. -/
theorem rationalTransport_aut (g : FundamentalGroup s hs) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) g =
      rationalMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g := by
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp [integralTransport_aut]
  | add x y hx hy => simp_all

/-- Integral-to-rational passage commutes with the same actual path. -/
theorem toRational_transport (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Integral Ω P) :
    Divisibility.toRational Ω' P
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) =
      rationalTransport P (hμfin := hμfin) (hμet := hμet) γ
        (Divisibility.toRational Ω P x) := rfl

/-- Endpoint monodromy is intertwined by the geometric path conjugation. -/
theorem rationalTransport_monodromy (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) γ
        (rationalMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g x) =
      rationalMonodromy t ht P (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalMonodromy_tmul, rationalTransport_tmul]
    rw [integralTransport_monodromy]
  | add x y hx hy => simp_all

/-- Changing the path introduces the target-point loop monodromy. -/
theorem rationalTransport_change_path (γ δ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) δ x =
      rationalMonodromy t ht P (hμfin := hμfin) (hμet := hμet) (γ.symm ≪≫ δ)
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) := by
  rw [← rationalTransport_aut, ← rationalTransport_trans]
  simp

/-- Transport preserves the existing rationalized full residue action. -/
theorem rationalTransport_scalarAction (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) γ
        (Divisibility.rationalScalarAction Ω P a x) =
      Divisibility.rationalScalarAction Ω' P a
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) :=
  TateScalarExtension.map_action
    (integralTransportLinearEquiv P (hμfin := hμfin) (hμet := hμet) γ).toLinearMap a x

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The explicitly compared finite-adelic scalar action is preserved. -/
theorem rationalTransport_finiteAdeleAction (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.FiniteAdeles ℚ) (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hμfin) (hμet := hμet) γ
        (Divisibility.finiteAdeleAction Ω P h a x) =
      Divisibility.finiteAdeleAction Ω' P h a
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) :=
  rationalTransport_scalarAction P (hμfin := hμfin) (hμet := hμet) γ _ x

/-- The same transport over the existing, explicitly compared adelic modules. -/
def finiteAdeleTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := Divisibility.finiteAdeleModule Ω P h
    let := Divisibility.finiteAdeleModule Ω' P h
    Divisibility.Rational Ω P ≃ₗ[Global.FiniteAdeles ℚ] Divisibility.Rational Ω' P := by
  let := Divisibility.finiteAdeleModule Ω P h
  let := Divisibility.finiteAdeleModule Ω' P h
  exact { (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ).toEquiv with
    map_add' := (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ).map_add
    map_smul' := rationalTransport_finiteAdeleAction P
      (hμfin := hμfin) (hμet := hμet) h γ }

@[simp] theorem finiteAdeleTransport_apply (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Ω P) :
    finiteAdeleTransport P (hμfin := hμfin) (hμet := hμet) h γ x =
      rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x := rfl

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- Full rational root transport retains all positive orders. -/
abbrev rationalFullTransport
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.RationalFull Ω ≃ₗ[ℚ] Divisibility.RationalFull Ω' :=
  rationalTransport (fun _ => True) (hμfin := hfullfin) (hμet := hfullet) γ

variable (m : ℕ)
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

/-- Away rational root transport requires finite étaleness only at retained orders. -/
abbrev rationalAwayTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.RationalAway Ω m ≃ₗ[ℚ] Divisibility.RationalAway Ω' m :=
  rationalTransport (fun n => Nat.Coprime n m) (hμfin := hμfin) (hμet := hμet) γ

omit hμfin hμet in
/-- Restriction from all orders to the retained orders commutes with transport. -/
theorem rationalRestrictAway_transport
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.RationalFull Ω) :
    Divisibility.rationalRestrictAway Ω' m (rationalFullTransport hfullfin hfullet γ x) =
      rationalAwayTransport m
        (hμfin := fun n => hfullfin ⟨n.val, n.property.1, trivial⟩)
        (hμet := fun n => hfullet ⟨n.val, n.property.1, trivial⟩) γ
          (Divisibility.rationalRestrictAway Ω m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- Away transport preserves the existing rationalized away residue scalars. -/
theorem rationalAwayTransport_scalarAction (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : Divisibility.RationalAway Ω m) :
    rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ
        (Divisibility.rationalAwayScalarAction Ω m a x) =
      Divisibility.rationalAwayScalarAction Ω' m a
        (rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ x) :=
  TateScalarExtension.map_action
    (awayTransportLinearEquiv m (hμfin := hμfin) (hμet := hμet) γ).toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

theorem rationalAwayTransport_primeToFiniteAdeleAction
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.PrimeToFiniteAdeles m) (x : Divisibility.RationalAway Ω m) :
    rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ
        (Divisibility.primeToFiniteAdeleAction Ω hAway a x) =
      Divisibility.primeToFiniteAdeleAction Ω' hAway a
        (rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ x) :=
  rationalAwayTransport_scalarAction m (hμfin := hμfin) (hμet := hμet) γ _ x

/-- Away transport is linear over the existing compared away adelic modules. -/
def primeToFiniteAdeleTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    let := Divisibility.primeToFiniteAdeleModule Ω hAway
    let := Divisibility.primeToFiniteAdeleModule Ω' hAway
    Divisibility.RationalAway Ω m ≃ₗ[Global.PrimeToFiniteAdeles m]
      Divisibility.RationalAway Ω' m := by
  let := Divisibility.primeToFiniteAdeleModule Ω hAway
  let := Divisibility.primeToFiniteAdeleModule Ω' hAway
  exact { (rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ).toEquiv with
    map_add' := (rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ).map_add
    map_smul' := rationalAwayTransport_primeToFiniteAdeleAction m
      (hμfin := hμfin) (hμet := hμet) hAway γ }

@[simp] theorem primeToFiniteAdeleTransport_apply
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.RationalAway Ω m) :
    primeToFiniteAdeleTransport m (hμfin := hμfin) (hμet := hμet) hAway γ x =
      rationalAwayTransport m (hμfin := hμfin) (hμet := hμet) γ x := rfl

end Langlands.TateTwist.Geometry
