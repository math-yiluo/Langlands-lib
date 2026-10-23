import Langlands.AbelianScheme.Tate.TwistPrimeMonodromy
import Langlands.AbelianScheme.Tate.TwistRationalMonodromy
import Langlands.AbelianScheme.Tate.TwistRationalPrimeScalars

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom]
  [hμet : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom]

/-- Scalar extension of the actual geometric action on coherent prime-power roots. -/
def rationalPrimeMonodromyMap (g : FundamentalGroup s hfin) :
    Rational Ω p →ₗ[ℚ_[p]] Rational Ω p :=
  (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g).baseChange ℚ_[p]

@[simp] theorem rationalPrimeMonodromyMap_tmul (g : FundamentalGroup s hfin)
    (q : ℚ_[p]) (x : Integral Ω p) :
    rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g x := rfl

@[simp] theorem rationalPrimeMonodromyMap_one (x : Rational Ω p) :
    rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) 1 x = x := by
  have heq : primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) 1 =
      LinearMap.id := LinearMap.ext
    (primeMonodromyHom_one s hfin p (hμfin := hμfin) (hμet := hμet))
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω p => f.baseChange ℚ_[p]) heq
  rw [LinearMap.baseChange_id] at hbase
  exact LinearMap.congr_fun hbase x

theorem rationalPrimeMonodromyMap_mul (g h : FundamentalGroup s hfin)
    (x : Rational Ω p) :
    rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) (g * h) x =
      rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g
        (rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) h x) := by
  have heq : primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) (g * h) =
      (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g).comp
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) h) :=
    LinearMap.ext (primeMonodromyHom_mul s hfin p (hμfin := hμfin) (hμet := hμet) g h)
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω p => f.baseChange ℚ_[p]) heq
  rw [LinearMap.baseChange_comp] at hbase
  exact LinearMap.congr_fun hbase x

/-- The rational geometric automorphism retains the nontrivial twist action. -/
def rationalPrimeMonodromy (g : FundamentalGroup s hfin) :
    Rational Ω p ≃ₗ[ℚ_[p]] Rational Ω p :=
  { rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g with
    invFun := rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹
    left_inv := fun x => by
      change rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹
        (rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g x) = x
      rw [← rationalPrimeMonodromyMap_mul, inv_mul_cancel, rationalPrimeMonodromyMap_one]
    right_inv := fun x => by
      change rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g
        (rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹ x) = x
      rw [← rationalPrimeMonodromyMap_mul, mul_inv_cancel, rationalPrimeMonodromyMap_one] }

@[simp] theorem rationalPrimeMonodromy_tmul (g : FundamentalGroup s hfin)
    (q : ℚ_[p]) (x : Integral Ω p) :
    rationalPrimeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g x := rfl

/-- Integral-to-rational passage is equivariant for the actual root actions. -/
theorem primeToRational_monodromy (g : FundamentalGroup s hfin) (x : Integral Ω p) :
    TateTwist.toRational Ω p
        (primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g x) =
      rationalPrimeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g
        (TateTwist.toRational Ω p x) := rfl

def rationalPrimeRepresentation :
    FundamentalGroup s hfin →*
      (Rational Ω p ≃ₗ[ℚ_[p]] Rational Ω p) where
  toFun := rationalPrimeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet)
  map_one' := LinearEquiv.ext
    (rationalPrimeMonodromyMap_one s hfin p (hμfin := hμfin) (hμet := hμet))
  map_mul' g h := LinearEquiv.ext
    (rationalPrimeMonodromyMap_mul s hfin p (hμfin := hμfin) (hμet := hμet) g h)

@[instance_reducible] def rationalPrimeMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Rational Ω p) where
  smul := fun g x => rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g x
  one_smul := rationalPrimeMonodromyMap_one s hfin p (hμfin := hμfin) (hμet := hμet)
  mul_smul := rationalPrimeMonodromyMap_mul s hfin p (hμfin := hμfin) (hμet := hμet)
  smul_zero g := map_zero (rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g)
  smul_add g := map_add (rationalPrimeMonodromyMap s hfin p (hμfin := hμfin) (hμet := hμet) g)

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Rational extraction intertwines the actual selected and prime-adic root actions. -/
theorem rationalToPrime_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Divisibility.Rational Ω P) :
    Divisibility.rationalToPrime Ω P p hP
        (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      rationalPrimeMonodromy s hfin p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) g
          (Divisibility.rationalToPrime Ω P p hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    rw [rationalMonodromy_tmul, Divisibility.rationalToPrime_tmul,
      Divisibility.rationalToPrime_tmul]
    exact congrArg (fun y : Integral Ω p => (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] y)
      (toPrime_monodromy s hfin P p (hμfin := hμfin) (hμet := hμet) hP g x)
  | add x y hx hy => simp_all

/-- The existing semilinear projection has the same geometric equivariance. -/
theorem rationalToPrimeSemilinear_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Divisibility.Rational Ω P) :
    Divisibility.rationalToPrimeSemilinear Ω P p hP
        (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      rationalPrimeMonodromy s hfin p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) g
          (Divisibility.rationalToPrimeSemilinear Ω P p hP x) :=
  rationalToPrime_monodromy s hfin P p (hμfin := hμfin) (hμet := hμet) hP g x

omit hμfin hμet in
/-- Full rational extraction commutes with geometric monodromy. -/
theorem rationalFullToPrime_monodromy
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.RationalFull Ω) :
    Divisibility.rationalFullToPrime Ω p
        (rationalFullMonodromy s hfin hfullfin hfullet g x) =
      rationalPrimeMonodromy s hfin p
        (hμfin := fun n => hfullfin
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n))
        (hμet := fun n => hfullet
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n)) g
          (Divisibility.rationalFullToPrime Ω p x) :=
  rationalToPrime_monodromy s hfin (fun _ => True) p
    (hμfin := hfullfin) (hμet := hfullet) (fun _ => trivial) g x

omit hμfin hμet in
/-- Rational away extraction is equivariant at a retained prime. -/
theorem rationalAwayToPrime_monodromy (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.RationalAway Ω m) :
    Divisibility.rationalAwayToPrime Ω p m h
        (rationalAwayMonodromy s hfin m (hμfin := hawayfin) (hμet := hawayet) g x) =
      rationalPrimeMonodromy s hfin p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) g
          (Divisibility.rationalAwayToPrime Ω p m h x) :=
  rationalToPrime_monodromy s hfin (fun n => Nat.Coprime n m) p
    (hμfin := hawayfin) (hμet := hawayet) (fun n => h.pow_left n) g x

omit hμfin hμet in
/-- The away semilinear projection retains the same monodromy law. -/
theorem rationalAwayToPrimeSemilinear_monodromy (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.RationalAway Ω m) :
    Divisibility.rationalAwayToPrimeSemilinear Ω p m h
        (rationalAwayMonodromy s hfin m (hμfin := hawayfin) (hμet := hawayet) g x) =
      rationalPrimeMonodromy s hfin p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) g
          (Divisibility.rationalAwayToPrimeSemilinear Ω p m h x) :=
  rationalAwayToPrime_monodromy s hfin p m h hawayfin hawayet g x

end Langlands.TateTwist.Geometry
