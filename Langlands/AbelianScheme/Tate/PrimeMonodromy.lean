import Langlands.AbelianScheme.Tate.RationalMonodromy
import Langlands.AbelianScheme.Tate.RationalPrimeScalars

/-! # Actual geometric monodromy on prime-adic Tate modules -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate.PrimeAdic

universe u
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (p : ℕ) [Fact p.Prime] (hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(S, ⊤)))

omit [Fact p.Prime] in
/-- Inverting the prime supplies every required prime-power invertibility proof. -/
theorem primePower_isUnit (hp : IsUnit (p : Γ(S, ⊤))) (n : ℕ) :
    IsUnit ((p ^ n : ℕ) : Γ(S, ⊤)) := by
  simpa only [Nat.cast_pow] using hp.pow n

/-- Finite geometric monodromy with the existing p-adic residue scalar structure. -/
def levelMonodromyLinear (n : ℕ) (g : FundamentalGroup s hfin) :
    Level A (Over.mk s) p n →ₗ[ℤ_[p]] Level A (Over.mk s) p n where
  toAddHom := (levelMonodromy s hfin htor A (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (hu n) g).toAddMonoidHom
  map_smul' a x := levelMonodromy_zmod_smul s hfin htor A (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (hu n) g (PadicInt.toZModPow n a) x

/-- Coordinatewise evaluation of the actual geometric automorphism on prime-power torsion. -/
def monodromyMap (g : FundamentalGroup s hfin) :
    Integral A (Over.mk s) p →ₗ[ℤ_[p]] Integral A (Over.mk s) p :=
  lift A (Over.mk s) p
    (fun n => (levelMonodromyLinear s hfin htor A p hu n g).comp
      (evaluation A (Over.mk s) p n)) (by
    intro n x
    change Tate.transition A (Over.mk s) _
      (levelMonodromy s hfin htor A (p ^ (n + 1)) (pow_pos (Fact.out : p.Prime).pos (n + 1)) (hu (n + 1)) g (x.val (n + 1))) = _
    rw [← levelMonodromy_transition s hfin htor A (p ^ n)
      (pow_pos (Fact.out : p.Prime).pos n) (hu n) (p ^ (n + 1))
      (pow_pos (Fact.out : p.Prime).pos (n + 1)) (hu (n + 1))
      (pow_dvd_pow p (Nat.le_succ n)), x.property n]
    rfl)

@[simp] theorem evaluation_monodromyMap (g : FundamentalGroup s hfin)
    (n : ℕ) (x : Integral A (Over.mk s) p) :
    evaluation A (Over.mk s) p n (monodromyMap s hfin htor A p hu g x) =
      levelMonodromy s hfin htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
        (hu n) g (evaluation A (Over.mk s) p n x) := rfl

@[simp] theorem monodromyMap_one (x : Integral A (Over.mk s) p) :
    monodromyMap s hfin htor A p hu 1 x = x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_one s hfin htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) (hu n) (x.val n)

theorem monodromyMap_mul (g k : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) p) :
    monodromyMap s hfin htor A p hu (g * k) x =
      monodromyMap s hfin htor A p hu g (monodromyMap s hfin htor A p hu k x) := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_mul s hfin htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) (hu n) g k (x.val n)

/-- The actual prime-adic linear automorphism, with inverse obtained from the inverse loop. -/
def monodromy (g : FundamentalGroup s hfin) :
    Integral A (Over.mk s) p ≃ₗ[ℤ_[p]] Integral A (Over.mk s) p :=
  { monodromyMap s hfin htor A p hu g with
    invFun := monodromyMap s hfin htor A p hu g⁻¹
    left_inv := fun x => by
      change monodromyMap s hfin htor A p hu g⁻¹ (monodromyMap s hfin htor A p hu g x) = x
      rw [← monodromyMap_mul, inv_mul_cancel, monodromyMap_one]
    right_inv := fun x => by
      change monodromyMap s hfin htor A p hu g (monodromyMap s hfin htor A p hu g⁻¹ x) = x
      rw [← monodromyMap_mul, mul_inv_cancel, monodromyMap_one] }

@[simp] theorem monodromy_apply (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) p) :
    monodromy s hfin htor A p hu g x = monodromyMap s hfin htor A p hu g x := rfl

/-- The prime-adic linear automorphisms form the geometric representation. -/
def monodromyRepresentation :
    FundamentalGroup s hfin →*
      (Integral A (Over.mk s) p ≃ₗ[ℤ_[p]] Integral A (Over.mk s) p) where
  toFun := monodromy s hfin htor A p hu
  map_one' := LinearEquiv.ext (monodromyMap_one s hfin htor A p hu)
  map_mul' g k := LinearEquiv.ext (monodromyMap_mul s hfin htor A p hu g k)

/-- The same representation as a locally installable additive action. -/
@[instance_reducible] def monodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Integral A (Over.mk s) p) where
  smul := fun g x => monodromyMap s hfin htor A p hu g x
  one_smul := monodromyMap_one s hfin htor A p hu
  mul_smul := monodromyMap_mul s hfin htor A p hu
  smul_zero g := map_zero (monodromyMap s hfin htor A p hu g)
  smul_add g := _root_.map_add (monodromyMap s hfin htor A p hu g)

set_option maxHeartbeats 800000 in
/-- Joint continuity is tested at the actual finite prime-power coordinates. -/
theorem continuous_monodromy_coordinate (n : ℕ) :
    Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) p =>
      levelMonodromy s hfin htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
        (hu n) z.1 (evaluation A (Over.mk s) p n z.2)) := by
  have he : Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) p =>
      (z.1, evaluation A (Over.mk s) p n z.2)) :=
    continuous_fst.prodMk ((continuous_evaluation A (Over.mk s) p n).comp continuous_snd)
  exact Continuous.comp
    (f := fun z : FundamentalGroup s hfin × Integral A (Over.mk s) p =>
      (z.1, evaluation A (Over.mk s) p n z.2))
    (continuous_levelMonodromy s hfin htor A (p ^ n)
      (pow_pos (Fact.out : p.Prime).pos n) (hu n)) he

/-- Joint continuity for the existing product-subspace topology on the prime-adic limit. -/
theorem continuous_monodromy :
    Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) p =>
      monodromy s hfin htor A p hu z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_pi (continuous_monodromy_coordinate s hfin htor A p hu)

theorem monodromyAction_continuousSMul :
    let := monodromyAction s hfin htor A p hu
    ContinuousSMul (FundamentalGroup s hfin) (Integral A (Over.mk s) p) := by
  let := monodromyAction s hfin htor A p hu
  exact ⟨continuous_monodromy s hfin htor A p hu⟩

variable {A} {B : AbelianScheme S}

/-- Actual homomorphisms intertwine the prime-adic geometric actions. -/
theorem monodromy_map (f : A ⟶ B) (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) p) :
    monodromy s hfin htor B p hu g (map (Over.mk s) p f x) =
      map (Over.mk s) p f (monodromy s hfin htor A p hu g x) := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_map s hfin htor A (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) (hu n) f g (x.val n)

variable (A)

/-- Extension of the actual prime-adic representation to the existing p-adic rationalization. -/
def rationalMonodromyMap (g : FundamentalGroup s hfin) :
    Rational A (Over.mk s) p →ₗ[ℚ_[p]] Rational A (Over.mk s) p :=
  (monodromyMap s hfin htor A p hu g).baseChange ℚ_[p]

@[simp] theorem rationalMonodromyMap_tmul (g : FundamentalGroup s hfin)
    (a : ℚ_[p]) (x : Integral A (Over.mk s) p) :
    rationalMonodromyMap s hfin htor A p hu g (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] monodromy s hfin htor A p hu g x := rfl

@[simp] theorem rationalMonodromyMap_one (x : Rational A (Over.mk s) p) :
    rationalMonodromyMap s hfin htor A p hu 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp_all

theorem rationalMonodromyMap_mul (g k : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) p) :
    rationalMonodromyMap s hfin htor A p hu (g * k) x =
      rationalMonodromyMap s hfin htor A p hu g
        (rationalMonodromyMap s hfin htor A p hu k x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp [monodromyMap_mul]
  | add x y hx hy => simp_all

/-- Rational prime-adic monodromy is linear over the actual p-adic field. -/
def rationalMonodromy (g : FundamentalGroup s hfin) :
    Rational A (Over.mk s) p ≃ₗ[ℚ_[p]] Rational A (Over.mk s) p :=
  { rationalMonodromyMap s hfin htor A p hu g with
    invFun := rationalMonodromyMap s hfin htor A p hu g⁻¹
    left_inv := fun x => by
      change rationalMonodromyMap s hfin htor A p hu g⁻¹
        (rationalMonodromyMap s hfin htor A p hu g x) = x
      rw [← rationalMonodromyMap_mul, inv_mul_cancel, rationalMonodromyMap_one]
    right_inv := fun x => by
      change rationalMonodromyMap s hfin htor A p hu g
        (rationalMonodromyMap s hfin htor A p hu g⁻¹ x) = x
      rw [← rationalMonodromyMap_mul, mul_inv_cancel, rationalMonodromyMap_one] }

@[simp] theorem rationalMonodromy_apply (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) p) :
    rationalMonodromy s hfin htor A p hu g x = rationalMonodromyMap s hfin htor A p hu g x := rfl

/-- The p-adic rational representation has the same action order. -/
def rationalMonodromyRepresentation :
    FundamentalGroup s hfin →*
      (Rational A (Over.mk s) p ≃ₗ[ℚ_[p]] Rational A (Over.mk s) p) where
  toFun := rationalMonodromy s hfin htor A p hu
  map_one' := LinearEquiv.ext (rationalMonodromyMap_one s hfin htor A p hu)
  map_mul' g k := LinearEquiv.ext (rationalMonodromyMap_mul s hfin htor A p hu g k)

/-- The actual integral-to-rational prime map is equivariant. -/
theorem toRational_monodromy (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) p) :
    toRational A (Over.mk s) p (monodromy s hfin htor A p hu g x) =
      rationalMonodromy s hfin htor A p hu g (toRational A (Over.mk s) p x) := rfl

variable {A}

/-- Scalar extension preserves actual-homomorphism equivariance. -/
theorem rationalMonodromy_map (f : A ⟶ B) (g : FundamentalGroup s hfin)
    (x : Rational A (Over.mk s) p) :
    rationalMonodromy s hfin htor B p hu g (rationalMap (Over.mk s) p f x) =
      rationalMap (Over.mk s) p f (rationalMonodromy s hfin htor A p hu g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [rationalMap_tmul, rationalMonodromy_apply, rationalMonodromyMap_tmul]
    rw [monodromy_map]
  | add x y hx hy => simp_all

end Langlands.AbelianScheme.Tate.PrimeAdic

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Langlands.TateTwist.Divisibility (primePowerIndex)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (p : ℕ) [Fact p.Prime]

/-- Extracting selected prime-power coordinates commutes with actual geometric monodromy. -/
theorem toPrime_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Integral A (Over.mk s) P) :
    GroupScheme.Tate.PrimeComparison.toPrime A.toGrp (Over.mk s) P p hP
        (integralMonodromy s hfin htor A P hu g x) =
      PrimeAdic.monodromy s hfin htor A p
        (fun n => hu (primePowerIndex P p hP n)) g
        (GroupScheme.Tate.PrimeComparison.toPrime A.toGrp (Over.mk s) P p hP x) := rfl

/-- The existing continuous semilinear coordinate map is geometrically equivariant. -/
theorem toPrimeContinuousSemilinear_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Integral A (Over.mk s) P) :
    toPrimeContinuousSemilinear A (Over.mk s) P p hP
        (integralMonodromy s hfin htor A P hu g x) =
      PrimeAdic.monodromy s hfin htor A p
        (fun n => hu (primePowerIndex P p hP n)) g
        (toPrimeContinuousSemilinear A (Over.mk s) P p hP x) := rfl

/-- Rational prime extraction intertwines the two different scalar extensions. -/
theorem rationalToPrime_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalToPrime A (Over.mk s) P p hP (rationalMonodromy s hfin htor A P hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex P p hP n)) g
        (rationalToPrime A (Over.mk s) P p hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [Tate.rationalMonodromy_apply, Tate.rationalMonodromyMap_tmul,
      rationalToPrime, GroupScheme.Tate.PrimeComparison.rationalToPrime_tmul,
      PrimeAdic.rationalMonodromy_apply, PrimeAdic.rationalMonodromyMap_tmul,
      toPrime_monodromy]
  | add x y hx hy => simp_all

/-- Rational residue semilinearity and geometric equivariance hold for the same map. -/
theorem rationalToPrimeSemilinear_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Rational A (Over.mk s) P) :
    rationalToPrimeSemilinear A (Over.mk s) P p hP
        (rationalMonodromy s hfin htor A P hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex P p hP n)) g
        (rationalToPrimeSemilinear A (Over.mk s) P p hP x) :=
  rationalToPrime_monodromy s hfin htor A P hu p hP g x

end Langlands.AbelianScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Langlands.TateTwist.Divisibility (primePowerIndex)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (p : ℕ) [Fact p.Prime]

/-- Full prime coordinates preserve both their existing residue scalars and monodromy. -/
theorem fullToPrimeContinuousSemilinear_monodromy
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : Full A (Over.mk s)) :
    fullToPrimeContinuousSemilinear A (Over.mk s) p (fullMonodromy s hfin htor A hu g x) =
      PrimeAdic.monodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) g
        (fullToPrimeContinuousSemilinear A (Over.mk s) p x) := rfl

/-- Away prime coordinates retain exactly the primes coprime to the excluded modulus. -/
theorem awayToPrimeContinuousSemilinear_monodromy (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : Away A (Over.mk s) m) :
    awayToPrimeContinuousSemilinear A (Over.mk s) p m hp
        (awayMonodromy s hfin htor A m hu g x) =
      PrimeAdic.monodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) g
        (awayToPrimeContinuousSemilinear A (Over.mk s) p m hp x) := rfl

/-- Full rational prime extraction is equivariant for the actual p-adic rational action. -/
theorem rationalFullToPrime_monodromy
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : RationalFull A (Over.mk s)) :
    rationalFullToPrime A (Over.mk s) p (rationalFullMonodromy s hfin htor A hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) g
        (rationalFullToPrime A (Over.mk s) p x) :=
  rationalToPrime_monodromy s hfin htor A (fun _ => True) hu p (fun _ => trivial) g x

/-- Away rational prime extraction is equivariant at every retained prime. -/
theorem rationalAwayToPrime_monodromy (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : RationalAway A (Over.mk s) m) :
    rationalAwayToPrime A (Over.mk s) p m hp
        (rationalAwayMonodromy s hfin htor A m hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) g
        (rationalAwayToPrime A (Over.mk s) p m hp x) :=
  rationalToPrime_monodromy s hfin htor A (fun k => Nat.Coprime k m) hu p
    (fun k => hp.pow_left k) g x

/-- Full rational semilinear extraction uses the same equivariant map. -/
theorem rationalFullToPrimeSemilinear_monodromy
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : RationalFull A (Over.mk s)) :
    rationalFullToPrimeSemilinear A (Over.mk s) p
        (rationalFullMonodromy s hfin htor A hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun _ => True) p (fun _ => trivial) n)) g
        (rationalFullToPrimeSemilinear A (Over.mk s) p x) :=
  rationalFullToPrime_monodromy s hfin htor A p hu g x

/-- Away rational semilinear extraction uses the same equivariant map. -/
theorem rationalAwayToPrimeSemilinear_monodromy (m : ℕ) (hp : Nat.Coprime p m)
    (hu : ∀ n : Index (fun k => Nat.Coprime k m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : RationalAway A (Over.mk s) m) :
    rationalAwayToPrimeSemilinear A (Over.mk s) p m hp
        (rationalAwayMonodromy s hfin htor A m hu g x) =
      PrimeAdic.rationalMonodromy s hfin htor A p
        (fun n => hu (primePowerIndex (fun k => Nat.Coprime k m) p
          (fun k => hp.pow_left k) n)) g
        (rationalAwayToPrimeSemilinear A (Over.mk s) p m hp x) :=
  rationalAwayToPrime_monodromy s hfin htor A p m hp hu g x

end Langlands.AbelianScheme.Tate.PrimeComparison
