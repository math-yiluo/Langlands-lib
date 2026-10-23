import Langlands.AbelianScheme.Tate.TwistFiniteTransport
import Langlands.AbelianScheme.Tate.TwistIntegralMonodromy

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

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

/-- Transport a coherent root family by evaluating the path at every selected order. -/
def integralTransportHom (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Integral Ω P →+ Divisibility.Integral Ω' P :=
  Divisibility.lift Ω' P
    (fun n => (levelTransport n.val γ).toAddMonoidHom.comp
      (Divisibility.evaluation Ω P n)) (by
    intro n m h x
    change transition Ω' h (levelTransport m.val γ (x.val m)) = _
    rw [← levelTransport_transition h γ, x.property n m h]
    rfl)

@[simp] theorem evaluation_integralTransportHom
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (n : Index P)
    (x : Divisibility.Integral Ω P) :
    Divisibility.evaluation Ω' P n
        (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ x) =
      levelTransport n.val γ (Divisibility.evaluation Ω P n x) := rfl

@[simp] theorem integralTransportHom_refl (x : Divisibility.Integral Ω P) :
    integralTransportHom P (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x := by
  apply Subtype.ext
  funext n
  exact levelTransport_refl n.val (x.val n)

theorem integralTransportHom_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Divisibility.Integral Ω P) :
    integralTransportHom P (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      integralTransportHom P (hμfin := hμfin) (hμet := hμet) δ
        (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ x) := by
  apply Subtype.ext
  funext n
  change Divisibility.evaluation Ω'' P n
      (integralTransportHom P (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x) =
    Divisibility.evaluation Ω'' P n
      (integralTransportHom P (hμfin := hμfin) (hμet := hμet) δ
        (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ x))
  rw [evaluation_integralTransportHom, evaluation_integralTransportHom,
    evaluation_integralTransportHom, levelTransport_trans]

/-- Integral root path transport, inverted by reversing the same geometric path. -/
def integralTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Integral Ω P ≃+ Divisibility.Integral Ω' P :=
  { integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ with
    invFun := integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ.symm
    left_inv := fun x => by
      change integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ.symm
        (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ x) = x
      rw [← integralTransportHom_trans]
      simp
    right_inv := fun x => by
      change integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ
        (integralTransportHom P (hμfin := hμfin) (hμet := hμet) γ.symm x) = x
      rw [← integralTransportHom_trans]
      simp }

@[simp] theorem evaluation_integralTransport
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (n : Index P)
    (x : Divisibility.Integral Ω P) :
    Divisibility.evaluation Ω' P n
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) =
      levelTransport n.val γ (Divisibility.evaluation Ω P n x) := rfl

@[simp] theorem integralTransport_refl (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x :=
  integralTransportHom_refl P (hμfin := hμfin) (hμet := hμet) x

theorem integralTransport_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      integralTransport P (hμfin := hμfin) (hμet := hμet) δ
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) :=
  integralTransportHom_trans P (hμfin := hμfin) (hμet := hμet) γ δ x

theorem integralTransport_symm (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (integralTransport P (hμfin := hμfin) (hμet := hμet) γ).symm =
      integralTransport P (hμfin := hμfin) (hμet := hμet) γ.symm := rfl

/-- A loop gives exactly the previously constructed integral geometric root action. -/
theorem integralTransport_aut (g : FundamentalGroup s hs) :
    integralTransport P (hμfin := hμfin) (hμet := hμet) g =
      integralMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g := by
  apply AddEquiv.ext
  intro x
  apply Subtype.ext
  funext n
  exact congrArg (fun e : Level Ω n.val ≃+ Level Ω n.val => e (x.val n))
    (levelTransport_aut n.val g)

/-- Coordinatewise continuity uses the existing product-subspace topology. -/
theorem continuous_integralTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (integralTransport P (hμfin := hμfin) (hμet := hμet) γ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_levelTransport n.val γ).comp (Divisibility.continuous_evaluation Ω P n)

/-- The existing full residue scalars commute with transport. -/
theorem integralTransport_full_smul (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.ProfiniteIntegerRing) (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hμfin) (hμet := hμet) γ (a • x) =
      a • integralTransport P (hμfin := hμfin) (hμet := hμet) γ x := by
  apply Subtype.ext
  funext n
  exact (levelTransportLinear n.val γ).map_smul
    (GroupScheme.Tate.fullReduction P n a) (x.val n)

/-- Selected integral root transport is linear over the full profinite integers. -/
def integralTransportLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Integral Ω P ≃ₗ[Global.ProfiniteIntegerRing] Divisibility.Integral Ω' P :=
  { integralTransport P (hμfin := hμfin) (hμet := hμet) γ with
    map_smul' := integralTransport_full_smul P (hμfin := hμfin) (hμet := hμet) γ }

/-- The same transport is continuous in both directions. -/
def integralTransportContinuousLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Integral Ω P ≃L[Global.ProfiniteIntegerRing] Divisibility.Integral Ω' P :=
  { integralTransportLinearEquiv P (hμfin := hμfin) (hμet := hμet) γ with
    continuous_toFun := continuous_integralTransport P (hμfin := hμfin) (hμet := hμet) γ
    continuous_invFun := continuous_integralTransport P (hμfin := hμfin) (hμet := hμet) γ.symm }

/-- Monodromy at the endpoints is intertwined by the geometric conjugation map. -/
theorem integralTransport_monodromy (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hμfin) (hμet := hμet) γ
        (integralMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g x) =
      integralMonodromy t ht P (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) := by
  apply Subtype.ext
  funext n
  change Divisibility.evaluation Ω' P n
      (integralTransport P (hμfin := hμfin) (hμet := hμet) γ
        (integralMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g x)) =
    Divisibility.evaluation Ω' P n
      (integralMonodromy t ht P (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x))
  rw [evaluation_integralTransport, evaluation_integralMonodromy,
    evaluation_integralMonodromy, evaluation_integralTransport, levelTransport_monodromy]

/-- Changing the path introduces exactly the target-point loop monodromy. -/
theorem integralTransport_change_path (γ δ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hμfin) (hμet := hμet) δ x =
      integralMonodromy t ht P (hμfin := hμfin) (hμet := hμet) (γ.symm ≪≫ δ)
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) := by
  rw [← integralTransport_aut, ← integralTransport_trans]
  simp

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

/-- Full root transport uses all positive orders. -/
abbrev fullTransport
    (hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Full Ω ≃+ Divisibility.Full Ω' :=
  integralTransport (fun _ => True) (hμfin := hμfin) (hμet := hμet) γ

variable (m : ℕ)
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

/-- Away root transport uses only the retained orders. -/
abbrev awayTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Away Ω m ≃+ Divisibility.Away Ω' m :=
  integralTransport (fun n => Nat.Coprime n m) (hμfin := hμfin) (hμet := hμet) γ

theorem awayTransport_smul (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.PrimeToProfiniteIntegerRing m) (x : Divisibility.Away Ω m) :
    awayTransport m (hμfin := hμfin) (hμet := hμet) γ (a • x) =
      a • awayTransport m (hμfin := hμfin) (hμet := hμet) γ x := by
  apply Subtype.ext
  funext n
  exact (levelTransportLinear n.val γ).map_smul
    (GroupScheme.Tate.awayReduction m n a) (x.val n)

/-- Away root transport is linear over its own residue scalar ring. -/
def awayTransportLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Away Ω m ≃ₗ[Global.PrimeToProfiniteIntegerRing m] Divisibility.Away Ω' m :=
  { awayTransport m (hμfin := hμfin) (hμet := hμet) γ with
    map_smul' := awayTransport_smul m (hμfin := hμfin) (hμet := hμet) γ }

/-- Away root transport is continuous for the existing limit topology. -/
def awayTransportContinuousLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Away Ω m ≃L[Global.PrimeToProfiniteIntegerRing m] Divisibility.Away Ω' m :=
  { awayTransportLinearEquiv m (hμfin := hμfin) (hμet := hμet) γ with
    continuous_toFun := continuous_integralTransport _ (hμfin := hμfin) (hμet := hμet) γ
    continuous_invFun := continuous_integralTransport _ (hμfin := hμfin) (hμet := hμet) γ.symm }

omit hμfin hμet in
/-- Restriction from all orders to the retained orders commutes with the same path. -/
theorem restrictAway_transport
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Full Ω) :
    Divisibility.restrictAway Ω' m (fullTransport hfullfin hfullet γ x) =
      awayTransport m
        (hμfin := fun n => hfullfin ⟨n.val, n.property.1, trivial⟩)
        (hμet := fun n => hfullet ⟨n.val, n.property.1, trivial⟩) γ
          (Divisibility.restrictAway Ω m x) := rfl

end Langlands.TateTwist.Geometry
