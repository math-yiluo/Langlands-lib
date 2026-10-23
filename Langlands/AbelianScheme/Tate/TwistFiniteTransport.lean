import Langlands.AbelianScheme.Tate.TwistFiniteMonodromy
import Langlands.AbelianScheme.Tate.FiniteTransport

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme
open Langlands.GroupScheme.Gm.TateComparison

universe u

private theorem transportKernel_isFinite (S : Scheme.{u}) (n : ℕ)
    [IsFinite (mu S n).X.hom] :
    IsFinite (kernel (multiplication (Gm S).toGrp n)).X.hom :=
  inferInstanceAs (IsFinite (mu S n).X.hom)

private theorem transportKernel_etale (S : Scheme.{u}) (n : ℕ)
    [Etale (mu S n).X.hom] :
    Etale (kernel (multiplication (Gm S).toGrp n)).X.hom :=
  inferInstanceAs (Etale (mu S n).X.hom)

attribute [local instance] transportKernel_isFinite transportKernel_etale

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (n : ℕ) [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]

/-- Evaluate the actual path on the roots-of-unity cover through the affine comparison. -/
def levelTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level Ω n ≃+ Level Ω' n :=
  ((affineLevelEquiv s n).symm.trans
    (Tate.finiteLevelTransport (Gm S).toGrp n γ)).trans (affineLevelEquiv t n)

@[simp] theorem affineLevelEquiv_transport (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Tate.Level (Gm S).toGrp (Over.mk s) n) :
    levelTransport n γ (affineLevelEquiv s n x) =
      affineLevelEquiv t n (Tate.finiteLevelTransport (Gm S).toGrp n γ x) := by
  simp [levelTransport]

/-- Transport on actual root-kernel points is precisely path evaluation. -/
theorem levelTransport_kernel (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Additive (Over.mk s ⟶ (mu S n).X)) :
    levelTransport n γ (mu.levelEquiv n s x) =
      mu.levelEquiv n t (Additive.ofMul (pathAct γ (mu S n).X x.toMul)) := by
  rw [← affineLevelEquiv_kernel, affineLevelEquiv_transport,
    Tate.finiteLevelTransport_kernel, affineLevelEquiv_kernel]
  rfl

@[simp] theorem levelTransport_refl (x : Level Ω n) :
    levelTransport n (Iso.refl (fiberFunctor s hs)) x = x := by
  simp [levelTransport]

theorem levelTransport_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Level Ω n) :
    levelTransport n (γ ≪≫ δ) x = levelTransport n δ (levelTransport n γ x) := by
  simp only [levelTransport, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rw [Tate.finiteLevelTransport_trans]

theorem levelTransport_symm (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (levelTransport n γ).symm = levelTransport n γ.symm := rfl

/-- A loop recovers the published geometric monodromy exactly. -/
theorem levelTransport_aut (g : FundamentalGroup s hs) :
    levelTransport n g = levelMonodromy s hs n g := rfl

/-- Path evaluation is linear for the existing residue actions. -/
def levelTransportLinear (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level Ω n ≃ₗ[ZMod n] Level Ω' n :=
  { levelTransport n γ with
    map_smul' := fun a x => ZMod.map_smul (levelTransport n γ).toAddMonoidHom a x }

theorem continuous_levelTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (levelTransport n γ) := continuous_of_discreteTopology

/-- The finite root transport uses the already published discrete level topologies. -/
def levelTransportContinuousLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level Ω n ≃L[ZMod n] Level Ω' n :=
  { levelTransportLinear n γ with
    continuous_toFun := continuous_levelTransport n γ
    continuous_invFun := continuous_levelTransport n γ.symm }

/-- The same geometric path transports the monodromy group by conjugation. -/
theorem levelTransport_monodromy (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Level Ω n) :
    levelTransport n γ (levelMonodromy s hs n g x) =
      levelMonodromy t ht n (pathConjugation γ g) (levelTransport n γ x) := by
  simp only [levelTransport, levelMonodromy, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  rw [Tate.finiteLevelTransport_monodromy]

/-- Changing the path introduces exactly the corresponding loop at the target point. -/
theorem levelTransport_change_path (γ δ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level Ω n) :
    levelTransport n δ x =
      levelMonodromy t ht n (γ.symm ≪≫ δ) (levelTransport n γ x) := by
  rw [← levelTransport_aut, ← levelTransport_trans]
  simp

variable {n}

/-- Root transport commutes with the existing quotient-power transition. -/
theorem levelTransport_transition {m : ℕ}
    [IsFinite (mu S m).X.hom] [Etale (mu S m).X.hom]
    (h : n ∣ m) (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Level Ω m) :
    levelTransport n γ (transition Ω h x) =
      transition Ω' h (levelTransport m γ x) := by
  obtain ⟨y, rfl⟩ := (affineLevelEquiv s m).surjective x
  rw [← affineLevelEquiv_transition s h y, affineLevelEquiv_transport,
    Tate.finiteLevelTransport_transition, affineLevelEquiv_transition,
    affineLevelEquiv_transport]

end Langlands.TateTwist.Geometry
