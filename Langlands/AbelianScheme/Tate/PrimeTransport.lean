import Langlands.AbelianScheme.Tate.RationalTransport
import Langlands.AbelianScheme.Tate.PrimeMonodromy

/-! # Actual prime-adic Tate transport along geometric paths -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate.PrimeAdic
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (p : ℕ) [Fact p.Prime] (hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(S, ⊤)))

/-- Actual finite path transport with the existing p-adic residue action. -/
def levelTransportLinear (n : ℕ) (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level A (Over.mk s) p n →ₗ[ℤ_[p]] Level A (Over.mk t) p n where
  toAddHom := (levelTransport htor A (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (hu n) e).toAddMonoidHom
  map_smul' a x := levelTransport_zmod_smul htor A (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (hu n) e (PadicInt.toZModPow n a) x

/-- Apply the path to each actual prime-power torsion coordinate. -/
def transportMap (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) p →ₗ[ℤ_[p]] Integral A (Over.mk t) p :=
  lift A (Over.mk t) p
    (fun n => (levelTransportLinear htor A p hu n e).comp
      (evaluation A (Over.mk s) p n)) (by
    intro n x
    change Tate.transition A (Over.mk t) _
      (levelTransport htor A (p ^ (n + 1))
        (pow_pos (Fact.out : p.Prime).pos (n + 1)) (hu (n + 1)) e (x.val (n + 1))) = _
    rw [← levelTransport_transition htor A (p ^ n)
      (pow_pos (Fact.out : p.Prime).pos n) (hu n) (p ^ (n + 1))
      (pow_pos (Fact.out : p.Prime).pos (n + 1)) (hu (n + 1))
      (pow_dvd_pow p (Nat.le_succ n)), x.property n]
    rfl)

@[simp] theorem evaluation_transportMap (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (n : ℕ) (x : Integral A (Over.mk s) p) :
    evaluation A (Over.mk t) p n (transportMap htor A p hu e x) =
      levelTransport htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
        (hu n) e (evaluation A (Over.mk s) p n x) := rfl

@[simp] theorem transportMap_refl (x : Integral A (Over.mk s) p) :
    transportMap htor A p hu (Iso.refl (fiberFunctor s hs)) x = x := by
  apply Subtype.ext
  funext n
  exact levelTransport_refl htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) (x.val n)

theorem transportMap_trans (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (f : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral A (Over.mk s) p) :
    transportMap htor A p hu (e ≪≫ f) x =
      transportMap htor A p hu f (transportMap htor A p hu e x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_trans htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) e f (x.val n)

/-- The actual prime-adic path equivalence, with inverse given by the reverse path. -/
def transport (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) p ≃ₗ[ℤ_[p]] Integral A (Over.mk t) p :=
  { transportMap htor A p hu e with
    invFun := transportMap htor A p hu e.symm
    left_inv := fun x => by
      change transportMap htor A p hu e.symm (transportMap htor A p hu e x) = x
      rw [← transportMap_trans]
      simp
    right_inv := fun x => by
      change transportMap htor A p hu e (transportMap htor A p hu e.symm x) = x
      rw [← transportMap_trans]
      simp }

@[simp] theorem transport_apply (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) p) :
    transport htor A p hu e x = transportMap htor A p hu e x := rfl

@[simp] theorem transport_refl (x : Integral A (Over.mk s) p) :
    transport htor A p hu (Iso.refl (fiberFunctor s hs)) x = x :=
  transportMap_refl htor A p hu x

theorem transport_trans (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (f : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral A (Over.mk s) p) :
    transport htor A p hu (e ≪≫ f) x =
      transport htor A p hu f (transport htor A p hu e x) :=
  transportMap_trans htor A p hu e f x

theorem transport_symm (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (transport htor A p hu e).symm = transport htor A p hu e.symm := rfl

/-- Loop transport is the previously constructed actual prime-adic monodromy. -/
theorem transport_aut (g : FundamentalGroup s hs) :
    transport htor A p hu g = monodromy s hs htor A p hu g := rfl

/-- Continuity for the existing product-subspace topology. -/
theorem continuous_transport (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (transport htor A p hu e) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_levelTransport htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) e).comp (continuous_evaluation A (Over.mk s) p n)

/-- Prime-adic transport is a continuous linear equivalence. -/
def transportContinuousLinearEquiv (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral A (Over.mk s) p ≃L[ℤ_[p]] Integral A (Over.mk t) p where
  __ := transport htor A p hu e
  continuous_toFun := continuous_transport htor A p hu e
  continuous_invFun := continuous_transport htor A p hu e.symm

/-- Equivariance under the actual conjugation of geometric fundamental groups. -/
theorem transport_monodromy (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Integral A (Over.mk s) p) :
    transport htor A p hu e (monodromy s hs htor A p hu g x) =
      monodromy t ht htor A p hu (pathConjugation e g) (transport htor A p hu e x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_monodromy htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) e g (x.val n)

/-- The dependence on the path is precisely target-point monodromy. -/
theorem transport_change_path (e f : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) p) :
    transport htor A p hu f x =
      monodromy t ht htor A p hu (e.symm ≪≫ f) (transport htor A p hu e x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_change_path htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) e f (x.val n)

variable {A} {B : AbelianScheme S}

/-- Naturality with respect to an actual abelian-scheme homomorphism. -/
theorem transport_map (f : A ⟶ B) (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) p) :
    transport htor B p hu e (map (Over.mk s) p f x) =
      map (Over.mk t) p f (transport htor A p hu e x) := by
  apply Subtype.ext
  funext n
  exact levelTransport_map htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    (hu n) f e (x.val n)

variable (A)

/-- Scalar extension of the actual prime-adic path map to the p-adic field. -/
def rationalTransportMap (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational A (Over.mk s) p →ₗ[ℚ_[p]] Rational A (Over.mk t) p :=
  (transportMap htor A p hu e).baseChange ℚ_[p]

@[simp] theorem rationalTransportMap_tmul (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ_[p]) (x : Integral A (Over.mk s) p) :
    rationalTransportMap htor A p hu e (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] transport htor A p hu e x := rfl

@[simp] theorem rationalTransportMap_refl (x : Rational A (Over.mk s) p) :
    rationalTransportMap htor A p hu (Iso.refl (fiberFunctor s hs)) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp_all

theorem rationalTransportMap_trans (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (f : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational A (Over.mk s) p) :
    rationalTransportMap htor A p hu (e ≪≫ f) x =
      rationalTransportMap htor A p hu f (rationalTransportMap htor A p hu e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp [transportMap_trans]
  | add x y hx hy => simp_all

/-- Rational prime-adic transport, with inverse given by the reverse path. -/
def rationalTransport (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational A (Over.mk s) p ≃ₗ[ℚ_[p]] Rational A (Over.mk t) p :=
  { rationalTransportMap htor A p hu e with
    invFun := rationalTransportMap htor A p hu e.symm
    left_inv := fun x => by
      change rationalTransportMap htor A p hu e.symm
        (rationalTransportMap htor A p hu e x) = x
      rw [← rationalTransportMap_trans]
      simp
    right_inv := fun x => by
      change rationalTransportMap htor A p hu e
        (rationalTransportMap htor A p hu e.symm x) = x
      rw [← rationalTransportMap_trans]
      simp }

@[simp] theorem rationalTransport_apply (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu e x = rationalTransportMap htor A p hu e x := rfl

@[simp] theorem rationalTransport_tmul (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (a : ℚ_[p]) (x : Integral A (Over.mk s) p) :
    rationalTransport htor A p hu e (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] transport htor A p hu e x := rfl

@[simp] theorem rationalTransport_refl (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu (Iso.refl (fiberFunctor s hs)) x = x :=
  rationalTransportMap_refl htor A p hu x

theorem rationalTransport_trans (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (f : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu (e ≪≫ f) x =
      rationalTransport htor A p hu f (rationalTransport htor A p hu e x) :=
  rationalTransportMap_trans htor A p hu e f x

theorem rationalTransport_symm (e : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (rationalTransport htor A p hu e).symm = rationalTransport htor A p hu e.symm := rfl

/-- Loop transport is precisely the existing rational prime-adic monodromy. -/
theorem rationalTransport_aut (g : FundamentalGroup s hs) :
    rationalTransport htor A p hu g = rationalMonodromy s hs htor A p hu g := rfl

/-- The existing integral-to-rational prime map commutes with transport. -/
theorem toRational_transport (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral A (Over.mk s) p) :
    toRational A (Over.mk t) p (transport htor A p hu e x) =
      rationalTransport htor A p hu e (toRational A (Over.mk s) p x) := rfl

/-- Rational prime-adic transport intertwines actual geometric monodromy. -/
theorem rationalTransport_monodromy (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu e (rationalMonodromy s hs htor A p hu g x) =
      rationalMonodromy t ht htor A p hu (pathConjugation e g)
        (rationalTransport htor A p hu e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change a ⊗ₜ[ℤ_[p]] transport htor A p hu e
      (monodromy s hs htor A p hu g x) =
      a ⊗ₜ[ℤ_[p]] monodromy t ht htor A p hu (pathConjugation e g)
        (transport htor A p hu e x)
    rw [transport_monodromy]
  | add x y hx hy => simp_all

/-- The rational change-of-path law is target-point monodromy. -/
theorem rationalTransport_change_path (e f : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) p) :
    rationalTransport htor A p hu f x =
      rationalMonodromy t ht htor A p hu (e.symm ≪≫ f)
        (rationalTransport htor A p hu e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change a ⊗ₜ[ℤ_[p]] transport htor A p hu f x =
      a ⊗ₜ[ℤ_[p]] monodromy t ht htor A p hu (e.symm ≪≫ f)
        (transport htor A p hu e x)
    rw [transport_change_path]
  | add x y hx hy => simp_all

variable {A}

/-- Scalar extension preserves naturality for actual abelian-scheme homomorphisms. -/
theorem rationalTransport_map (f : A ⟶ B) (e : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk s) p) :
    rationalTransport htor B p hu e (rationalMap (Over.mk s) p f x) =
      rationalMap (Over.mk t) p f (rationalTransport htor A p hu e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [rationalMap_tmul, rationalTransport_apply, rationalTransportMap_tmul]
    rw [transport_map]
  | add x y hx hy => simp_all

end Langlands.AbelianScheme.Tate.PrimeAdic

namespace Langlands.AbelianScheme.Tate.PrimeComparison
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Langlands.TateTwist.Divisibility (primePowerIndex)

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (p : ℕ) [Fact p.Prime]

/-- Reading selected prime-power coordinates commutes with the actual path map. -/
theorem toPrime_transport (hP : ∀ n : ℕ, P (p ^ n))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Integral A (Over.mk s) P) :
    GroupScheme.Tate.PrimeComparison.toPrime A.toGrp (Over.mk t) P p hP
        (integralTransport htor A P hu e x) =
      PrimeAdic.transport htor A p (fun n => hu (primePowerIndex P p hP n)) e
        (GroupScheme.Tate.PrimeComparison.toPrime A.toGrp (Over.mk s) P p hP x) := rfl

/-- The same square for the existing continuous semilinear coordinate map. -/
theorem toPrimeContinuousSemilinear_transport (hP : ∀ n : ℕ, P (p ^ n))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Integral A (Over.mk s) P) :
    toPrimeContinuousSemilinear A (Over.mk t) P p hP
        (integralTransport htor A P hu e x) =
      PrimeAdic.transport htor A p (fun n => hu (primePowerIndex P p hP n)) e
        (toPrimeContinuousSemilinear A (Over.mk s) P p hP x) := rfl

/-- Rational prime extraction intertwines the two scalar extensions of path transport. -/
theorem rationalToPrime_transport (hP : ∀ n : ℕ, P (p ^ n))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalToPrime A (Over.mk t) P p hP (rationalTransport htor A P hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex P p hP n)) e
        (rationalToPrime A (Over.mk s) P p hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [Tate.rationalTransport_apply, Tate.rationalTransportMap_tmul,
      rationalToPrime, GroupScheme.Tate.PrimeComparison.rationalToPrime_tmul,
      PrimeAdic.rationalTransport_apply, PrimeAdic.rationalTransportMap_tmul,
      toPrime_transport]
  | add x y hx hy => simp_all

/-- The existing rational semilinear map has the same transport compatibility. -/
theorem rationalToPrimeSemilinear_transport (hP : ∀ n : ℕ, P (p ^ n))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational A (Over.mk s) P) :
    rationalToPrimeSemilinear A (Over.mk t) P p hP
        (rationalTransport htor A P hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex P p hP n)) e
        (rationalToPrimeSemilinear A (Over.mk s) P p hP x) :=
  rationalToPrime_transport htor A P hu p hP e x

end Langlands.AbelianScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Langlands.TateTwist.Divisibility (primePowerIndex)

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (p : ℕ) [Fact p.Prime]

/-- Full prime extraction commutes with transport on both existing scalar structures. -/
theorem fullToPrimeContinuousSemilinear_transport
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Full A (Over.mk s)) :
    fullToPrimeContinuousSemilinear A (Over.mk t) p (fullTransport htor A hu e x) =
      PrimeAdic.transport htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) e
        (fullToPrimeContinuousSemilinear A (Over.mk s) p x) := rfl

/-- Away prime extraction commutes with transport at each retained prime. -/
theorem awayToPrimeContinuousSemilinear_transport (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Away A (Over.mk s) m) :
    awayToPrimeContinuousSemilinear A (Over.mk t) p m hp
        (awayTransport htor A m hu e x) =
      PrimeAdic.transport htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) e
        (awayToPrimeContinuousSemilinear A (Over.mk s) p m hp x) := rfl

/-- Full rational prime extraction commutes with the actual prime-adic path map. -/
theorem rationalFullToPrime_transport
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalFull A (Over.mk s)) :
    rationalFullToPrime A (Over.mk t) p (rationalFullTransport htor A hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) e
        (rationalFullToPrime A (Over.mk s) p x) :=
  rationalToPrime_transport htor A (fun _ => True) hu p (fun _ => trivial) e x

/-- Away rational prime extraction commutes with transport at each retained prime. -/
theorem rationalAwayToPrime_transport (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalAway A (Over.mk s) m) :
    rationalAwayToPrime A (Over.mk t) p m hp
        (rationalAwayTransport htor A m hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) e
        (rationalAwayToPrime A (Over.mk s) p m hp x) :=
  rationalToPrime_transport htor A (fun k => Nat.Coprime k m) hu p
    (fun k => hp.pow_left k) e x

/-- The full rational semilinear extraction is compatible with the same path maps. -/
theorem rationalFullToPrimeSemilinear_transport
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalFull A (Over.mk s)) :
    rationalFullToPrimeSemilinear A (Over.mk t) p
        (rationalFullTransport htor A hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) e
        (rationalFullToPrimeSemilinear A (Over.mk s) p x) :=
  rationalFullToPrime_transport htor A p hu e x

/-- The away rational semilinear extraction is compatible with the same path maps. -/
theorem rationalAwayToPrimeSemilinear_transport (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (e : fiberFunctor s hs ≅ fiberFunctor t ht) (x : RationalAway A (Over.mk s) m) :
    rationalAwayToPrimeSemilinear A (Over.mk t) p m hp
        (rationalAwayTransport htor A m hu e x) =
      PrimeAdic.rationalTransport htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) e
        (rationalAwayToPrimeSemilinear A (Over.mk s) p m hp x) :=
  rationalAwayToPrime_transport htor A p m hp hu e x

end Langlands.AbelianScheme.Tate.PrimeComparison
