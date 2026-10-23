import Langlands.AbelianScheme.Tate.PrimeToAdelicFrameTransport
import Langlands.AbelianScheme.Tate.AwayAdelicTransport

/-! # Rational-isogeny transport of actual prime-to-modulus adelic Tate-frame orbits -/

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
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  (s : Spec (.of Ω) ⟶ S)

/-- Postcompose actual Tate frames with an intertwining rational isogeny. -/
def primeToAdelicFrameIsogeny (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    PrimeToAdelicFrame A m hAway iA V s ≃ PrimeToAdelicFrame B m hAway iB V s := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  letI := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  exact LinearFrame.postcomp (primeToFiniteAdeleAlgebraIso (Over.mk s) hAway iA iB e he)

@[simp] theorem primeToAdelicFrameIsogeny_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (eta : PrimeToAdelicFrame A m hAway iA V s) (x : V) :
    primeToAdelicFrameIsogeny m hAway iA iB V s e he eta x =
      rationalHomMap (Over.mk s) (fun n => Nat.Coprime n m) e.hom (eta x) := rfl

@[simp] theorem primeToAdelicFrameIsogeny_refl (eta : PrimeToAdelicFrame A m hAway iA V s) :
    primeToAdelicFrameIsogeny m hAway iA iA V s (Iso.refl _) (rationalIntertwines_identity iA) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity (Over.mk s) (fun n => Nat.Coprime n m)) (eta x)

theorem primeToAdelicFrameIsogeny_trans (iC : D →ₐ[ℚ] Rationalization.End C)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) (eta : PrimeToAdelicFrame A m hAway iA V s) :
    primeToAdelicFrameIsogeny m hAway iA iC V s (e.trans f)
        (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) eta =
      primeToAdelicFrameIsogeny m hAway iB iC V s f hf (primeToAdelicFrameIsogeny m hAway iA iB V s e he eta) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp (Over.mk s) (fun n => Nat.Coprime n m) e.hom f.hom) (eta x)

theorem primeToAdelicFrameIsogeny_symm (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    (primeToAdelicFrameIsogeny m hAway iA iB V s e he).symm =
      primeToAdelicFrameIsogeny m hAway iB iA V s e.symm (rationalIntertwines_inverse iA iB e he) := by
  apply Equiv.ext
  intro eta
  apply LinearEquiv.ext
  intro x
  rfl

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- Rational-isogeny transport on fixed right orbits for the same geometric point. -/
def primeToAdelicFrameOrbitIsogeny (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    PrimeToAdelicFrameOrbit A m hAway iA V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit B m hAway iB V s ρ hs htor hu U := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  letI := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  letI := primeToAdelicFrameRightAction A m hAway iA V s ρ
  letI := primeToAdelicFrameRightAction B m hAway iB V s ρ
  letI := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  letI := primeToAdelicFrameMonodromyAction B m hAway iB V s hs htor hu
  letI := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  letI := primeToAdelicFrameActionsComm B m hAway iB V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (primeToAdelicFrameIsogeny m hAway iA iB V s e he)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact (rationalMonodromy_iso s hs htor (fun n => Nat.Coprime n m) hu e γ (eta x)).symm)

@[simp] theorem primeToAdelicFrameOrbitIsogeny_refl (U : Subgroup G) :
    primeToAdelicFrameOrbitIsogeny m hAway iA iA V s ρ hs htor hu U
        (Iso.refl _) (rationalIntertwines_identity iA) =
      Equiv.refl (PrimeToAdelicFrameOrbit A m hAway iA V s ρ hs htor hu U) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameIsogeny_refl m hAway iA V s eta)

theorem primeToAdelicFrameOrbitIsogeny_trans (iC : D →ₐ[ℚ] Rationalization.End C) (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d)) :
    primeToAdelicFrameOrbitIsogeny m hAway iA iC V s ρ hs htor hu U (e.trans f)
        (rationalIntertwines_comp iA iB iC e.hom f.hom he hf) =
      (primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U e he).trans
        (primeToAdelicFrameOrbitIsogeny m hAway iB iC V s ρ hs htor hu U f hf) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  let := primeToAdelicFrameRightAction B m hAway iB V s ρ
  let := primeToAdelicFrameMonodromyAction B m hAway iB V s hs htor hu
  let := primeToAdelicFrameActionsComm B m hAway iB V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule C (Over.mk s) hAway iC
  let := primeToAdelicFrameRightAction C m hAway iC V s ρ
  let := primeToAdelicFrameMonodromyAction C m hAway iC V s hs htor hu
  let := primeToAdelicFrameActionsComm C m hAway iC V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameIsogeny_trans m hAway iA iB V s iC e f he hf eta)

theorem primeToAdelicFrameOrbitIsogeny_symm (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) :
    (primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U e he).symm =
      primeToAdelicFrameOrbitIsogeny m hAway iB iA V s ρ hs htor hu U e.symm
        (rationalIntertwines_inverse iA iB e he) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  let := primeToAdelicFrameRightAction B m hAway iB V s ρ
  let := primeToAdelicFrameMonodromyAction B m hAway iB V s hs htor hu
  let := primeToAdelicFrameActionsComm B m hAway iB V s ρ hs htor hu
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (primeToAdelicFrameIsogeny_symm m hAway iA iB V s e he))

theorem primeToAdelicFrameOrbitIsogeny_translate {U U' : Subgroup G}
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (x : PrimeToAdelicFrameOrbit A m hAway iA V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U' e he
        (primeToAdelicFrameOrbitTranslate A m hAway iA V ρ htor hu g hg x) =
      primeToAdelicFrameOrbitTranslate B m hAway iB V ρ htor hu g hg
        (primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U e he x) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  let := primeToAdelicFrameRightAction B m hAway iB V s ρ
  let := primeToAdelicFrameMonodromyAction B m hAway iB V s hs htor hu
  let := primeToAdelicFrameActionsComm B m hAway iB V s ρ hs htor hu
  exact InvariantOrbit.map_translate (MulEquiv.refl (FundamentalGroup s hs))
    (primeToAdelicFrameIsogeny m hAway iA iB V s e he)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      exact (rationalMonodromy_iso s hs htor (fun n => Nat.Coprime n m) hu e γ (eta x)).symm) g hg x

theorem primeToAdelicFrameOrbitIsogeny_forget {U U' : Subgroup G}
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (hU : U ≤ U')
    (x : PrimeToAdelicFrameOrbit A m hAway iA V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U' e he
        (primeToAdelicFrameOrbitForget A m hAway iA V ρ htor hu hU x) =
      primeToAdelicFrameOrbitForget B m hAway iB V ρ htor hu hU
        (primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U e he x) :=
  primeToAdelicFrameOrbitIsogeny_translate m hAway iA iB V s ρ hs htor hu e he 1 _ x

variable {t : Spec (.of Ω') ⟶ S} {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- Rational-isogeny transport commutes with geometric path transport on frames. -/
theorem primeToAdelicFrameIsogeny_transport (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : PrimeToAdelicFrame A m hAway iA V s) :
    primeToAdelicFrameTransport B m hAway iB V htor hu p (primeToAdelicFrameIsogeny m hAway iA iB V s e he eta) =
      primeToAdelicFrameIsogeny m hAway iA iB V t e he (primeToAdelicFrameTransport A m hAway iA V htor hu p eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalTransport_iso htor (fun n => Nat.Coprime n m) hu e p (eta x)

/-- The isogeny/path square on geometrically fixed right-orbit classes. -/
theorem primeToAdelicFrameOrbitIsogeny_transport (U : Subgroup G)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : PrimeToAdelicFrameOrbit A m hAway iA V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitTransport B m hAway iB V ρ htor hu U p
        (primeToAdelicFrameOrbitIsogeny m hAway iA iB V s ρ hs htor hu U e he x) =
      primeToAdelicFrameOrbitIsogeny m hAway iA iB V t ρ ht htor hu U e he
        (primeToAdelicFrameOrbitTransport A m hAway iA V ρ htor hu U p x) := by
  let := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway iA
  let := primeToAdelicFrameRightAction A m hAway iA V t ρ
  let := primeToAdelicFrameMonodromyAction A m hAway iA V t ht htor hu
  let := primeToAdelicFrameActionsComm A m hAway iA V t ρ ht htor hu
  let := primeToFiniteAdeleAlgebraModule B (Over.mk s) hAway iB
  let := primeToAdelicFrameRightAction B m hAway iB V s ρ
  let := primeToAdelicFrameMonodromyAction B m hAway iB V s hs htor hu
  let := primeToAdelicFrameActionsComm B m hAway iB V s ρ hs htor hu
  let := primeToFiniteAdeleAlgebraModule B (Over.mk t) hAway iB
  let := primeToAdelicFrameRightAction B m hAway iB V t ρ
  let := primeToAdelicFrameMonodromyAction B m hAway iB V t ht htor hu
  let := primeToAdelicFrameActionsComm B m hAway iB V t ρ ht htor hu
  apply Subtype.ext
  simp only [primeToAdelicFrameOrbitIsogeny, primeToAdelicFrameOrbitTransport, InvariantOrbit.equiv,
    Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (primeToAdelicFrameIsogeny_transport m hAway iA iB V s hs htor hu e he p eta)

end Langlands.AbelianScheme.Tate
