import Langlands.AbelianScheme.Tate.TwistIntegralMonodromy
import Langlands.AbelianScheme.Tate.TwistAwayRationalScalars

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
  (P : ℕ → Prop)
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Scalar extension of the actual geometric action on coherent roots. -/
def rationalMonodromyMap (g : FundamentalGroup s hfin) :
    Divisibility.Rational Ω P →ₗ[ℚ] Divisibility.Rational Ω P :=
  (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalMonodromyMap_tmul (g : FundamentalGroup s hfin)
    (q : ℚ) (x : Divisibility.Integral Ω P) :
    rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x := rfl

@[simp] theorem rationalMonodromyMap_one (x : Divisibility.Rational Ω P) :
    rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralMonodromyHom s hfin P
      (hμfin := hμfin) (hμet := hμet) 1 x = q ⊗ₜ[ℤ] x
    rw [integralMonodromyHom_one]
  | add x y hx hy => simp_all

theorem rationalMonodromyMap_mul (g h : FundamentalGroup s hfin)
    (x : Divisibility.Rational Ω P) :
    rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) (g * h) x =
      rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g
        (rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalMonodromyMap_tmul]
    exact congrArg (fun y : Divisibility.Integral Ω P => q ⊗ₜ[ℤ] y)
      (integralMonodromyHom_mul s hfin P (hμfin := hμfin) (hμet := hμet) g h x)
  | add x y hx hy => simp_all

/-- The rational geometric automorphism retains the nontrivial twist action. -/
def rationalMonodromy (g : FundamentalGroup s hfin) :
    Divisibility.Rational Ω P ≃ₗ[ℚ] Divisibility.Rational Ω P :=
  { rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g with
    invFun := rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹
    left_inv := fun x => by
      change rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹
        (rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g x) = x
      rw [← rationalMonodromyMap_mul, inv_mul_cancel, rationalMonodromyMap_one]
    right_inv := fun x => by
      change rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g
        (rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹ x) = x
      rw [← rationalMonodromyMap_mul, mul_inv_cancel, rationalMonodromyMap_one] }

@[simp] theorem rationalMonodromy_tmul (g : FundamentalGroup s hfin)
    (q : ℚ) (x : Divisibility.Integral Ω P) :
    rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x := rfl

/-- Integral-to-rational passage is equivariant for the actual root actions. -/
theorem toRational_monodromy (g : FundamentalGroup s hfin) (x : Divisibility.Integral Ω P) :
    Divisibility.toRational Ω P
        (integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g
        (Divisibility.toRational Ω P x) := rfl

def rationalRepresentation :
    FundamentalGroup s hfin →*
      (Divisibility.Rational Ω P ≃ₗ[ℚ] Divisibility.Rational Ω P) where
  toFun := rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet)
  map_one' := LinearEquiv.ext
    (rationalMonodromyMap_one s hfin P (hμfin := hμfin) (hμet := hμet))
  map_mul' g h := LinearEquiv.ext
    (rationalMonodromyMap_mul s hfin P (hμfin := hμfin) (hμet := hμet) g h)

@[instance_reducible] def rationalMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Divisibility.Rational Ω P) where
  smul := fun g x => rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g x
  one_smul := rationalMonodromyMap_one s hfin P (hμfin := hμfin) (hμet := hμet)
  mul_smul := rationalMonodromyMap_mul s hfin P (hμfin := hμfin) (hμet := hμet)
  smul_zero g := map_zero (rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g)
  smul_add g := map_add (rationalMonodromyMap s hfin P (hμfin := hμfin) (hμet := hμet) g)

/-- Rational monodromy commutes with rationalized full residue scalars. -/
theorem rationalMonodromy_scalarAction (g : FundamentalGroup s hfin)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Divisibility.Rational Ω P) :
    rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g
        (Divisibility.rationalScalarAction Ω P a x) =
      Divisibility.rationalScalarAction Ω P a
        (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) :=
  TateScalarExtension.map_action
    (integralMonodromyLinearEquiv s hfin P
      (hμfin := hμfin) (hμet := hμet) g).toLinearMap a x

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The explicitly compared finite-adelic scalar action is preserved. -/
theorem rationalMonodromy_finiteAdeleAction (g : FundamentalGroup s hfin)
    (a : Global.FiniteAdeles ℚ) (x : Divisibility.Rational Ω P) :
    rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g
        (Divisibility.finiteAdeleAction Ω P h a x) =
      Divisibility.finiteAdeleAction Ω P h a
        (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) :=
  rationalMonodromy_scalarAction s hfin P (hμfin := hμfin) (hμet := hμet) g _ x

/-- Bundle the same root action over the existing finite-adelic module. -/
def finiteAdeleMonodromy (g : FundamentalGroup s hfin) :
    let := Divisibility.finiteAdeleModule Ω P h
    Divisibility.Rational Ω P ≃ₗ[Global.FiniteAdeles ℚ] Divisibility.Rational Ω P := by
  let := Divisibility.finiteAdeleModule Ω P h
  exact { (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g).toEquiv with
    map_add' := (rationalMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g).map_add
    map_smul' := rationalMonodromy_finiteAdeleAction s hfin P
      (hμfin := hμfin) (hμet := hμet) h g }

def finiteAdeleRepresentation :
    let := Divisibility.finiteAdeleModule Ω P h
    FundamentalGroup s hfin →*
      (Divisibility.Rational Ω P ≃ₗ[Global.FiniteAdeles ℚ] Divisibility.Rational Ω P) := by
  let := Divisibility.finiteAdeleModule Ω P h
  exact {
    toFun := finiteAdeleMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) h
    map_one' := LinearEquiv.ext
      (rationalMonodromyMap_one s hfin P (hμfin := hμfin) (hμet := hμet))
    map_mul' := fun g k => LinearEquiv.ext
      (rationalMonodromyMap_mul s hfin P (hμfin := hμfin) (hμet := hμet) g k) }

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

abbrev rationalFullMonodromy
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) :
    Divisibility.RationalFull Ω ≃ₗ[ℚ] Divisibility.RationalFull Ω :=
  rationalMonodromy s hfin (fun _ => True) (hμfin := hfullfin) (hμet := hfullet) g

variable (m : ℕ)
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

abbrev rationalAwayMonodromy (g : FundamentalGroup s hfin) :
    Divisibility.RationalAway Ω m ≃ₗ[ℚ] Divisibility.RationalAway Ω m :=
  rationalMonodromy s hfin (fun n => Nat.Coprime n m) (hμfin := hμfin) (hμet := hμet) g

omit hμfin hμet in
/-- Full-to-away rational restriction commutes with geometric monodromy. -/
theorem rationalRestrictAway_monodromy
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.RationalFull Ω) :
    Divisibility.rationalRestrictAway Ω m (rationalFullMonodromy s hfin hfullfin hfullet g x) =
      rationalAwayMonodromy s hfin m
        (hμfin := fun n => hfullfin ⟨n.val, n.property.1, trivial⟩)
        (hμet := fun n => hfullet ⟨n.val, n.property.1, trivial⟩) g
          (Divisibility.rationalRestrictAway Ω m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- Away monodromy preserves rationalized away residue scalars. -/
theorem rationalAwayMonodromy_scalarAction (g : FundamentalGroup s hfin)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : Divisibility.RationalAway Ω m) :
    rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g
        (Divisibility.rationalAwayScalarAction Ω m a x) =
      Divisibility.rationalAwayScalarAction Ω m a
        (rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g x) :=
  TateScalarExtension.map_action
    (awayMonodromyLinearEquiv s hfin m (hμfin := hμfin) (hμet := hμet) g).toLinearMap a x

variable {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Away monodromy preserves the existing, explicitly compared away adelic scalars. -/
theorem rationalAwayMonodromy_primeToFiniteAdeleAction (g : FundamentalGroup s hfin)
    (a : Global.PrimeToFiniteAdeles m) (x : Divisibility.RationalAway Ω m) :
    rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g
        (Divisibility.primeToFiniteAdeleAction Ω hAway a x) =
      Divisibility.primeToFiniteAdeleAction Ω hAway a
        (rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g x) :=
  rationalAwayMonodromy_scalarAction s hfin m (hμfin := hμfin) (hμet := hμet) g _ x

def primeToFiniteAdeleMonodromy (g : FundamentalGroup s hfin) :
    let := Divisibility.primeToFiniteAdeleModule Ω hAway
    Divisibility.RationalAway Ω m ≃ₗ[Global.PrimeToFiniteAdeles m]
      Divisibility.RationalAway Ω m := by
  let := Divisibility.primeToFiniteAdeleModule Ω hAway
  exact { (rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g).toEquiv with
    map_add' := (rationalAwayMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) g).map_add
    map_smul' := rationalAwayMonodromy_primeToFiniteAdeleAction s hfin m
      (hμfin := hμfin) (hμet := hμet) hAway g }

def primeToFiniteAdeleRepresentation :
    let := Divisibility.primeToFiniteAdeleModule Ω hAway
    FundamentalGroup s hfin →*
      (Divisibility.RationalAway Ω m ≃ₗ[Global.PrimeToFiniteAdeles m]
        Divisibility.RationalAway Ω m) := by
  let := Divisibility.primeToFiniteAdeleModule Ω hAway
  exact {
    toFun := primeToFiniteAdeleMonodromy s hfin m (hμfin := hμfin) (hμet := hμet) hAway
    map_one' := LinearEquiv.ext
      (rationalMonodromyMap_one s hfin _ (hμfin := hμfin) (hμet := hμet))
    map_mul' := fun g k => LinearEquiv.ext
      (rationalMonodromyMap_mul s hfin _ (hμfin := hμfin) (hμet := hμet) g k) }

end Langlands.TateTwist.Geometry
