import Langlands.AbelianScheme.Tate.FiniteTransport
import Langlands.AbelianScheme.Tate.IntegralMonodromy

/-! # Transport on actual integral Tate limits along a geometric path -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- Apply actual finite path transport to each selected torsion coordinate. -/
def integralTransportHom (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) P →+ Integral A (Over.mk t) P :=
  lift A (Over.mk t) P
    (fun n => (levelTransport htor A n.val n.property.1 (hu n) p).toAddMonoidHom.comp
      (evaluation A (Over.mk s) P n)) (by
    intro n m h x
    change transition A (Over.mk t) h
      (levelTransport htor A m.val m.property.1 (hu m) p (x.val m)) = _
    rw [← levelTransport_transition htor A n.val n.property.1 (hu n)
      m.val m.property.1 (hu m) h, x.property n m h]
    rfl)

@[simp] theorem evaluation_integralTransportHom
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (n : Index P)
    (x : Integral A (Over.mk s) P) :
    evaluation A (Over.mk t) P n (integralTransportHom htor A P hu p x) =
      levelTransport htor A n.val n.property.1 (hu n) p
        (evaluation A (Over.mk s) P n x) := rfl

@[simp] theorem integralTransportHom_refl (x : Integral A (Over.mk s) P) :
    integralTransportHom htor A P hu (Iso.refl (fiberFunctor s hs)) x = x := by
  apply Subtype.ext
  funext n
  exact levelTransport_refl htor A n.val n.property.1 (hu n) (x.val n)

theorem integralTransportHom_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral A (Over.mk s) P) :
    integralTransportHom htor A P hu (p ≪≫ q) x =
      integralTransportHom htor A P hu q (integralTransportHom htor A P hu p x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_trans htor A n.val n.property.1 (hu n) p q (x.val n)

/-- Integral path transport, with inverse given by the reverse path. -/
def integralTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) P ≃+ Integral A (Over.mk t) P :=
  { integralTransportHom htor A P hu p with
    invFun := integralTransportHom htor A P hu p.symm
    left_inv := fun x => by
      change integralTransportHom htor A P hu p.symm
        (integralTransportHom htor A P hu p x) = x
      rw [← integralTransportHom_trans]
      simp
    right_inv := fun x => by
      change integralTransportHom htor A P hu p
        (integralTransportHom htor A P hu p.symm x) = x
      rw [← integralTransportHom_trans]
      simp }

@[simp] theorem evaluation_integralTransport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (n : Index P)
    (x : Integral A (Over.mk s) P) :
    evaluation A (Over.mk t) P n (integralTransport htor A P hu p x) =
      levelTransport htor A n.val n.property.1 (hu n) p
        (evaluation A (Over.mk s) P n x) := rfl

@[simp] theorem integralTransport_refl (x : Integral A (Over.mk s) P) :
    integralTransport htor A P hu (Iso.refl (fiberFunctor s hs)) x = x :=
  integralTransportHom_refl htor A P hu x

theorem integralTransport_trans (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral A (Over.mk s) P) :
    integralTransport htor A P hu (p ≪≫ q) x =
      integralTransport htor A P hu q (integralTransport htor A P hu p x) :=
  integralTransportHom_trans htor A P hu p q x

theorem integralTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (integralTransport htor A P hu p).symm = integralTransport htor A P hu p.symm := rfl

/-- Loop transport is the existing geometric monodromy. -/
theorem integralTransport_aut (g : FundamentalGroup s hs) :
    integralTransport htor A P hu g = integralMonodromy s hs htor A P hu g := rfl

/-- Coordinatewise continuity for the existing product-subspace topologies. -/
theorem continuous_integralTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (integralTransport htor A P hu p) := by
  apply (GroupScheme.Tate.continuous_iff_evaluation A.toGrp (Over.mk t) P
    (integralTransport htor A P hu p)).mpr
  intro n
  exact (continuous_levelTransport htor A n.val n.property.1 (hu n) p).comp
    (continuous_evaluation A (Over.mk s) P n)

/-- Transport bundled with continuity in both directions. -/
def integralTransportHomeomorph (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) P ≃ₜ+ Integral A (Over.mk t) P where
  __ := integralTransport htor A P hu p
  continuous_toFun := continuous_integralTransport htor A P hu p
  continuous_invFun := continuous_integralTransport htor A P hu p.symm

/-- Path transport preserves the existing full profinite-integer action. -/
theorem integralTransport_full_smul (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : Global.ProfiniteIntegerRing) (x : Integral A (Over.mk s) P) :
    integralTransport htor A P hu p (a • x) = a • integralTransport htor A P hu p x := by
  apply Subtype.ext
  funext n
  exact levelTransport_zmod_smul htor A n.val n.property.1 (hu n) p
    (GroupScheme.Tate.fullReduction P n a) (x.val n)

/-- Transport as a linear equivalence for the actual profinite-integer action. -/
def integralTransportLinearEquiv (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) P ≃ₗ[Global.ProfiniteIntegerRing] Integral A (Over.mk t) P :=
  { integralTransport htor A P hu p with
    map_smul' := integralTransport_full_smul htor A P hu p }

/-- Equivariance for the actual monodromy actions at the two points. -/
theorem integralTransport_monodromy (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Integral A (Over.mk s) P) :
    integralTransport htor A P hu p (integralMonodromy s hs htor A P hu g x) =
      integralMonodromy t ht htor A P hu (pathConjugation p g)
        (integralTransport htor A P hu p x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_monodromy htor A n.val n.property.1 (hu n) p g (x.val n)

/-- The exact dependence on the path is target-point geometric monodromy. -/
theorem integralTransport_change_path (p q : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) P) :
    integralTransport htor A P hu q x =
      integralMonodromy t ht htor A P hu (p.symm ≪≫ q)
        (integralTransport htor A P hu p x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_change_path htor A n.val n.property.1 (hu n) p q (x.val n)

variable {A} {B : AbelianScheme S}

/-- Naturality in an actual abelian-scheme homomorphism. -/
theorem integralTransport_map (f : A ⟶ B)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Integral A (Over.mk s) P) :
    integralTransport htor B P hu p (map (Over.mk s) P f x) =
      map (Over.mk t) P f (integralTransport htor A P hu p x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_map htor A n.val n.property.1 (hu n) f p (x.val n)

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- Full integral transport requires invertibility of every positive order. -/
abbrev fullTransport (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Full A (Over.mk s) ≃+ Full A (Over.mk t) :=
  integralTransport htor A (fun _ => True) hu p

/-- Away integral transport requires invertibility of the retained orders only. -/
abbrev awayTransport (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Away A (Over.mk s) m ≃+ Away A (Over.mk t) m :=
  integralTransport htor A (fun n => Nat.Coprime n m) hu p

/-- Away transport also respects the actual away residue scalar action. -/
theorem awayTransport_smul (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (a : Global.PrimeToProfiniteIntegerRing m)
    (x : Away A (Over.mk s) m) :
    awayTransport htor A m hu p (a • x) = a • awayTransport htor A m hu p x := by
  apply Subtype.ext
  funext n
  exact levelTransport_zmod_smul htor A n.val n.property.1 (hu n) p
    (GroupScheme.Tate.awayReduction m n a) (x.val n)

/-- Away transport as a linear equivalence over the actual away residue ring. -/
def awayTransportLinearEquiv (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Away A (Over.mk s) m ≃ₗ[Global.PrimeToProfiniteIntegerRing m] Away A (Over.mk t) m :=
  { awayTransport htor A m hu p with
    map_smul' := awayTransport_smul htor A m hu p }

/-- The full-to-away restriction commutes with transport along the same path. -/
theorem restrictAway_transport (m : ℕ)
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Full A (Over.mk s)) :
    restrictAway A (Over.mk t) m (fullTransport htor A hu p x) =
      awayTransport htor A m (fun n => hu ⟨n.val, n.property.1, trivial⟩) p
        (restrictAway A (Over.mk s) m x) := rfl

end Langlands.AbelianScheme.Tate
