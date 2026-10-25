import Langlands.AbelianScheme.Tate.AdelicFrameBaseChange
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeStatement

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Shimura.PEL.InvariantOrbit

variable {G X Y Γ Δ : Type*} [Group G] [Group Γ] [Group Δ]
  [MulAction Gᵐᵒᵖ X] [MulAction Gᵐᵒᵖ Y]
  [MulAction Γ X] [MulAction Δ Y]
  [SMulCommClass Γ Gᵐᵒᵖ X] [SMulCommClass Δ Gᵐᵒᵖ Y]

/-- Pull fixed orbits back across an equivariant equivalence and a group homomorphism.
The homomorphism need not be surjective. -/
def pullback (U : Subgroup G) (α : Γ →* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) :
    InvariantOrbit (X := Y) Δ U → InvariantOrbit (X := X) Γ U := fun q =>
  ⟨(RightOrbit.equiv U e he).symm q.1, fun γ => by
    apply (RightOrbit.equiv U e he).injective
    change RightOrbit.map U e he (γ • (RightOrbit.equiv U e he).symm q.1) =
      RightOrbit.map U e he ((RightOrbit.equiv U e he).symm q.1)
    rw [RightOrbit.map_smul U α e he hΓ]
    change α γ • ((RightOrbit.equiv U e he) ((RightOrbit.equiv U e he).symm q.1)) =
      (RightOrbit.equiv U e he) ((RightOrbit.equiv U e he).symm q.1)
    rw [Equiv.apply_symm_apply]
    exact q.2 (α γ)⟩

@[simp] theorem pullback_val (U : Subgroup G) (α : Γ →* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) (q : InvariantOrbit (X := Y) Δ U) :
    (pullback U α e he hΓ q).1 = (RightOrbit.equiv U e he).symm q.1 := rfl

theorem pullback_injective (U : Subgroup G) (α : Γ →* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) :
    Function.Injective (pullback U α e he hΓ) := by
  intro q r h
  apply Subtype.ext
  exact (RightOrbit.equiv U e he).symm.injective (congrArg Subtype.val h)

theorem pullback_translate {U U' : Subgroup G} (α : Γ →* Δ) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : InvariantOrbit (X := Y) Δ U) :
    pullback U' α e he hΓ (translate g hg q) =
      translate g hg (pullback U α e he hΓ q) := by
  apply Subtype.ext
  change (RightOrbit.equiv U' e he).symm (RightOrbit.translate g hg q.1) =
    RightOrbit.translate g hg ((RightOrbit.equiv U e he).symm q.1)
  apply (RightOrbit.equiv U' e he).injective
  rw [Equiv.apply_symm_apply]
  change RightOrbit.translate g hg q.1 =
    RightOrbit.map U' e he (RightOrbit.translate g hg ((RightOrbit.equiv U e he).symm q.1))
  rw [RightOrbit.map_translate]
  exact congrArg (RightOrbit.translate g hg)
    ((RightOrbit.equiv U e he).apply_symm_apply q.1).symm

end Langlands.Shimura.PEL.InvariantOrbit

universe u v w z
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Shimura.PEL

section Full
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S')
  {G : Type z} [Group G] (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
  (hbc : RationalMonodromyBaseChange.{u})

include hbc in
/-- The existing full frame comparison intertwines actual pointed monodromy. -/
theorem adelicFrameBaseChange_monodromy :
    letI := adelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
    letI := adelicFrameMonodromyAction A h i V (t ≫ b) hs htor hu
    ∀ γ eta, adelicFrameBaseChange b A h i V t (γ • eta) =
      fundamentalGroupMap b t (t ≫ b) rfl ht hs γ •
        adelicFrameBaseChange b A h i V t eta := by
  intro γ eta
  apply LinearEquiv.ext
  intro x
  exact hbc S S' b Ω inferInstance t ht hs htor A (fun _ => True) hu hu' γ (eta x)

/-- Pullback of fixed full Tate-frame orbits, with the named pointed-equivariance
proposition retained as an explicit mathematical dependency. -/
def adelicFrameOrbitPullback (U : Subgroup G) :
    AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U →
      AdelicFrameOrbit ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu' U := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ
  let := adelicFrameRightAction A h i V (t ≫ b) ρ
  let := adelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
  let := adelicFrameMonodromyAction A h i V (t ≫ b) hs htor hu
  let := adelicFrameActionsComm ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu'
  let := adelicFrameActionsComm A h i V (t ≫ b) ρ hs htor hu
  exact InvariantOrbit.pullback U (fundamentalGroupMap b t (t ≫ b) rfl ht hs)
    (adelicFrameBaseChange b A h i V t) (adelicFrameBaseChange_right b A h i V t ρ)
    (adelicFrameBaseChange_monodromy b A h i V t ht hs htor hu hu' hbc)

@[simp] theorem adelicFrameOrbitPullback_val (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    (adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U q).1 =
      (adelicFrameRightOrbitBaseChange b A h i V t ρ U).symm q.1 := rfl

/-- Pointed pullback is injective on the fixed orbit sets, without surjectivity
of the map on fundamental groups. -/
theorem adelicFrameOrbitPullback_injective (U : Subgroup G) :
    Function.Injective (adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U) := by
  intro q r hq
  apply Subtype.ext
  exact (adelicFrameRightOrbitBaseChange b A h i V t ρ U).symm.injective
    (congrArg Subtype.val hq)

/-- Pointed pullback commutes with the transporter-defined level map. -/
theorem adelicFrameOrbitPullback_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U'
        (adelicFrameOrbitTranslate A h i V ρ htor hu g hg q) =
      adelicFrameOrbitTranslate ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' g hg
        (adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U q) := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ
  let := adelicFrameRightAction A h i V (t ≫ b) ρ
  let := adelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
  let := adelicFrameMonodromyAction A h i V (t ≫ b) hs htor hu
  let := adelicFrameActionsComm ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu'
  let := adelicFrameActionsComm A h i V (t ≫ b) ρ hs htor hu
  exact InvariantOrbit.pullback_translate (fundamentalGroupMap b t (t ≫ b) rfl ht hs)
    (adelicFrameBaseChange b A h i V t) (adelicFrameBaseChange_right b A h i V t ρ)
    (adelicFrameBaseChange_monodromy b A h i V t ht hs htor hu hu' hbc) g hg q

/-- Forgetting a finer level commutes with pointed pullback. -/
theorem adelicFrameOrbitPullback_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U'
        (adelicFrameOrbitForget A h i V ρ htor hu hU q) =
      adelicFrameOrbitForget ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' hU
        (adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' hbc U q) :=
  adelicFrameOrbitPullback_translate b A h i V t ρ ht hs htor hu hu' hbc 1 _ q

end Full
section Away
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S')
  {G : Type z} [Group G] (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
  (hbc : RationalMonodromyBaseChange.{u})

include hbc in
/-- The existing prime-to-modulus frame comparison intertwines actual pointed monodromy. -/
theorem primeToAdelicFrameBaseChange_monodromy :
    letI := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
    letI := primeToAdelicFrameMonodromyAction A m hAway i V (t ≫ b) hs htor hu
    ∀ γ eta, primeToAdelicFrameBaseChange b A m hAway i V t (γ • eta) =
      fundamentalGroupMap b t (t ≫ b) rfl ht hs γ •
        primeToAdelicFrameBaseChange b A m hAway i V t eta := by
  intro γ eta
  apply LinearEquiv.ext
  intro x
  exact hbc S S' b Ω inferInstance t ht hs htor A (fun n => Nat.Coprime n m) hu hu' γ (eta x)

/-- Pullback of fixed prime-to-modulus Tate-frame orbits, with the named pointed-equivariance
proposition retained as an explicit mathematical dependency. -/
def primeToAdelicFrameOrbitPullback (U : Subgroup G) :
    PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U →
      PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu' U := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ
  let := primeToAdelicFrameRightAction A m hAway i V (t ≫ b) ρ
  let := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
  let := primeToAdelicFrameMonodromyAction A m hAway i V (t ≫ b) hs htor hu
  let := primeToAdelicFrameActionsComm ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu'
  let := primeToAdelicFrameActionsComm A m hAway i V (t ≫ b) ρ hs htor hu
  exact InvariantOrbit.pullback U (fundamentalGroupMap b t (t ≫ b) rfl ht hs)
    (primeToAdelicFrameBaseChange b A m hAway i V t) (primeToAdelicFrameBaseChange_right b A m hAway i V t ρ)
    (primeToAdelicFrameBaseChange_monodromy b A m hAway i V t ht hs htor hu hu' hbc)

@[simp] theorem primeToAdelicFrameOrbitPullback_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    (primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U q).1 =
      (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V t ρ U).symm q.1 := rfl

/-- Pointed pullback is injective on the fixed orbit sets, without surjectivity
of the map on fundamental groups. -/
theorem primeToAdelicFrameOrbitPullback_injective (U : Subgroup G) :
    Function.Injective (primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U) := by
  intro q r hq
  apply Subtype.ext
  exact (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V t ρ U).symm.injective
    (congrArg Subtype.val hq)

/-- Pointed pullback commutes with the transporter-defined level map. -/
theorem primeToAdelicFrameOrbitPullback_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U'
        (primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg q) =
      primeToAdelicFrameOrbitTranslate ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' g hg
        (primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U q) := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ
  let := primeToAdelicFrameRightAction A m hAway i V (t ≫ b) ρ
  let := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ht htor hu'
  let := primeToAdelicFrameMonodromyAction A m hAway i V (t ≫ b) hs htor hu
  let := primeToAdelicFrameActionsComm ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu'
  let := primeToAdelicFrameActionsComm A m hAway i V (t ≫ b) ρ hs htor hu
  exact InvariantOrbit.pullback_translate (fundamentalGroupMap b t (t ≫ b) rfl ht hs)
    (primeToAdelicFrameBaseChange b A m hAway i V t) (primeToAdelicFrameBaseChange_right b A m hAway i V t ρ)
    (primeToAdelicFrameBaseChange_monodromy b A m hAway i V t ht hs htor hu hu' hbc) g hg q

/-- Forgetting a finer level commutes with pointed pullback. -/
theorem primeToAdelicFrameOrbitPullback_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U'
        (primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU q) =
      primeToAdelicFrameOrbitForget ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' hU
        (primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' hbc U q) :=
  primeToAdelicFrameOrbitPullback_translate b A m hAway i V t ρ ht hs htor hu hu' hbc 1 _ q

end Away
end Langlands.AbelianScheme.Tate
