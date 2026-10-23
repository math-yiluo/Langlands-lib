import Langlands.AbelianScheme.Tate.AdelicFrameTransport
import Langlands.AbelianScheme.Tate.AdelicTransport

/-! # Rational-isogeny transport of actual adelic Tate-frame orbits -/

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

variable {S : Scheme.{u}} {A B C : AbelianScheme S}
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  (s : Spec (.of Ω) ⟶ S)

/-- Postcompose actual Tate frames with an intertwining rational isogeny. -/
def adelicFrameIsogeny (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    AdelicFrame A h iA V s ≃ AdelicFrame B h iB V s := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  letI := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  exact LinearFrame.postcomp (finiteAdeleAlgebraIso (Over.mk s) (fun _ => True) h iA iB e he)

@[simp] theorem adelicFrameIsogeny_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (eta : AdelicFrame A h iA V s) (x : V) :
    adelicFrameIsogeny h iA iB V s e he eta x =
      rationalHomMap (Over.mk s) (fun _ => True) e.hom (eta x) := rfl

@[simp] theorem adelicFrameIsogeny_refl (eta : AdelicFrame A h iA V s) :
    adelicFrameIsogeny h iA iA V s (Iso.refl _) (rationalIntertwines_identity iA) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity (Over.mk s) (fun _ => True)) (eta x)

theorem adelicFrameIsogeny_trans (iC : D →ₐ[ℚ] Rationalization.End C)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) (eta : AdelicFrame A h iA V s) :
    adelicFrameIsogeny h iA iC V s (e.trans f)
        (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) eta =
      adelicFrameIsogeny h iB iC V s f hf (adelicFrameIsogeny h iA iB V s e he eta) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp (Over.mk s) (fun _ => True) e.hom f.hom) (eta x)

theorem adelicFrameIsogeny_symm (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    (adelicFrameIsogeny h iA iB V s e he).symm =
      adelicFrameIsogeny h iB iA V s e.symm (rationalIntertwines_inverse iA iB e he) := by
  apply Equiv.ext
  intro eta
  apply LinearEquiv.ext
  intro x
  rfl

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- Rational-isogeny transport on fixed right orbits for the same geometric point. -/
def adelicFrameOrbitIsogeny (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    AdelicFrameOrbit A h iA V s ρ hs htor hu U ≃
      AdelicFrameOrbit B h iB V s ρ hs htor hu U := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  letI := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  letI := adelicFrameRightAction A h iA V s ρ
  letI := adelicFrameRightAction B h iB V s ρ
  letI := adelicFrameMonodromyAction A h iA V s hs htor hu
  letI := adelicFrameMonodromyAction B h iB V s hs htor hu
  letI := adelicFrameActionsComm A h iA V s ρ hs htor hu
  letI := adelicFrameActionsComm B h iB V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (adelicFrameIsogeny h iA iB V s e he)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact (rationalMonodromy_iso s hs htor (fun _ => True) hu e γ (eta x)).symm)

@[simp] theorem adelicFrameOrbitIsogeny_refl (U : Subgroup G) :
    adelicFrameOrbitIsogeny h iA iA V s ρ hs htor hu U
        (Iso.refl _) (rationalIntertwines_identity iA) =
      Equiv.refl (AdelicFrameOrbit A h iA V s ρ hs htor hu U) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V s ρ
  let := adelicFrameMonodromyAction A h iA V s hs htor hu
  let := adelicFrameActionsComm A h iA V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameIsogeny_refl h iA V s eta)

theorem adelicFrameOrbitIsogeny_trans (iC : D →ₐ[ℚ] Rationalization.End C) (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) :
    adelicFrameOrbitIsogeny h iA iC V s ρ hs htor hu U (e.trans f)
        (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) =
      (adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U e he).trans
        (adelicFrameOrbitIsogeny h iB iC V s ρ hs htor hu U f hf) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V s ρ
  let := adelicFrameMonodromyAction A h iA V s hs htor hu
  let := adelicFrameActionsComm A h iA V s ρ hs htor hu
  let := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  let := adelicFrameRightAction B h iB V s ρ
  let := adelicFrameMonodromyAction B h iB V s hs htor hu
  let := adelicFrameActionsComm B h iB V s ρ hs htor hu
  let := finiteAdeleAlgebraModule C (Over.mk s) (fun _ => True) h iC
  let := adelicFrameRightAction C h iC V s ρ
  let := adelicFrameMonodromyAction C h iC V s hs htor hu
  let := adelicFrameActionsComm C h iC V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameIsogeny_trans h iA iB V s iC e f he hf eta)

theorem adelicFrameOrbitIsogeny_symm (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    (adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U e he).symm =
      adelicFrameOrbitIsogeny h iB iA V s ρ hs htor hu U e.symm
        (rationalIntertwines_inverse iA iB e he) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V s ρ
  let := adelicFrameMonodromyAction A h iA V s hs htor hu
  let := adelicFrameActionsComm A h iA V s ρ hs htor hu
  let := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  let := adelicFrameRightAction B h iB V s ρ
  let := adelicFrameMonodromyAction B h iB V s hs htor hu
  let := adelicFrameActionsComm B h iB V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [adelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (adelicFrameIsogeny_symm h iA iB V s e he))

theorem adelicFrameOrbitIsogeny_translate {U U' : Subgroup G}
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : AdelicFrameOrbit A h iA V s ρ hs htor hu U) :
    adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U' e he
        (adelicFrameOrbitTranslate A h iA V ρ htor hu g hg x) =
      adelicFrameOrbitTranslate B h iB V ρ htor hu g hg
        (adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U e he x) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V s ρ
  let := adelicFrameMonodromyAction A h iA V s hs htor hu
  let := adelicFrameActionsComm A h iA V s ρ hs htor hu
  let := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  let := adelicFrameRightAction B h iB V s ρ
  let := adelicFrameMonodromyAction B h iB V s hs htor hu
  let := adelicFrameActionsComm B h iB V s ρ hs htor hu
  exact InvariantOrbit.map_translate (MulEquiv.refl (FundamentalGroup s hs))
    (adelicFrameIsogeny h iA iB V s e he)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact (rationalMonodromy_iso s hs htor (fun _ => True) hu e γ (eta x)).symm) g hg x

theorem adelicFrameOrbitIsogeny_forget {U U' : Subgroup G}
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (hU : U ≤ U')
    (x : AdelicFrameOrbit A h iA V s ρ hs htor hu U) :
    adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U' e he
        (adelicFrameOrbitForget A h iA V ρ htor hu hU x) =
      adelicFrameOrbitForget B h iB V ρ htor hu hU
        (adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U e he x) :=
  adelicFrameOrbitIsogeny_translate h iA iB V s ρ hs htor hu e he 1 _ x

variable {t : Spec (.of Ω') ⟶ S} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- Rational-isogeny transport commutes with geometric path transport on frames. -/
theorem adelicFrameIsogeny_transport (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : AdelicFrame A h iA V s) :
    adelicFrameTransport B h iB V htor hu p (adelicFrameIsogeny h iA iB V s e he eta) =
      adelicFrameIsogeny h iA iB V t e he (adelicFrameTransport A h iA V htor hu p eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_iso htor (fun _ => True) hu e p (eta x)

/-- The isogeny/path square on geometrically fixed right-orbit classes. -/
theorem adelicFrameOrbitIsogeny_transport (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : AdelicFrameOrbit A h iA V s ρ hs htor hu U) :
    adelicFrameOrbitTransport B h iB V ρ htor hu U p
        (adelicFrameOrbitIsogeny h iA iB V s ρ hs htor hu U e he x) =
      adelicFrameOrbitIsogeny h iA iB V t ρ ht htor hu U e he
        (adelicFrameOrbitTransport A h iA V ρ htor hu U p x) := by
  let := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V s ρ
  let := adelicFrameMonodromyAction A h iA V s hs htor hu
  let := adelicFrameActionsComm A h iA V s ρ hs htor hu
  let := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h iA
  let := adelicFrameRightAction A h iA V t ρ
  let := adelicFrameMonodromyAction A h iA V t ht htor hu
  let := adelicFrameActionsComm A h iA V t ρ ht htor hu
  let := finiteAdeleAlgebraModule B (Over.mk s) (fun _ => True) h iB
  let := adelicFrameRightAction B h iB V s ρ
  let := adelicFrameMonodromyAction B h iB V s hs htor hu
  let := adelicFrameActionsComm B h iB V s ρ hs htor hu
  let := finiteAdeleAlgebraModule B (Over.mk t) (fun _ => True) h iB
  let := adelicFrameRightAction B h iB V t ρ
  let := adelicFrameMonodromyAction B h iB V t ht htor hu
  let := adelicFrameActionsComm B h iB V t ρ ht htor hu
  apply Subtype.ext
  simp only [adelicFrameOrbitIsogeny, adelicFrameOrbitTransport, InvariantOrbit.equiv,
    Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (adelicFrameIsogeny_transport h iA iB V s hs htor hu e he p eta)

end Langlands.AbelianScheme.Tate
