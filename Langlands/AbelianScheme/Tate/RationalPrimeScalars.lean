import Langlands.AbelianScheme.Tate.RationalPrime
import Langlands.AbelianScheme.Tate.PrimeScalars
import Langlands.AbelianScheme.Tate.RationalScalars
import Langlands.Global.RationalProfiniteIntegerPadicProjection

/-! # Rational scalar compatibility of actual Tate prime coordinates -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Expose the existing rational residue action as a module for local installation. -/
@[instance_reducible] def rationalScalarModule (P : ℕ → Prop) :
    Module (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (Rational G T P) :=
  Module.compHom _ (rationalScalarAction G T P).toRingHom

theorem rationalScalarModule_smul (P : ℕ → Prop)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational G T P) :
    let := rationalScalarModule G T P
    a • x = rationalScalarAction G T P a x := rfl

theorem rationalScalarModule_scalarTower (P : ℕ → Prop) :
    let := rationalScalarModule G T P
    IsScalarTower ℚ (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (Rational G T P) := by
  let := rationalScalarModule G T P
  constructor
  intro q a x
  exact LinearMap.congr_fun ((rationalScalarAction G T P).toLinearMap.map_smul q a) x

/-- The existing away residue action as a module for local installation. -/
@[instance_reducible] def rationalAwayScalarModule (m : ℕ) :
    Module (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (RationalAway G T m) :=
  Module.compHom _ (rationalAwayScalarAction G T m).toRingHom

theorem rationalAwayScalarModule_smul (m : ℕ)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway G T m) :
    let := rationalAwayScalarModule G T m
    a • x = rationalAwayScalarAction G T m a x := rfl

theorem rationalAwayScalarModule_scalarTower (m : ℕ) :
    let := rationalAwayScalarModule G T m
    IsScalarTower ℚ (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m)
      (RationalAway G T m) := by
  let := rationalAwayScalarModule G T m
  constructor
  intro q a x
  exact LinearMap.congr_fun ((rationalAwayScalarAction G T m).toLinearMap.map_smul q a) x

end Langlands.GroupScheme.Tate

namespace Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Rational prime coordinates intertwine the canonical rational residue projections. -/
theorem rationalToPrime_scalarAction (hP : ∀ n : ℕ, P (p ^ n))
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational G T P) :
    rationalToPrime G T P p hP (rationalScalarAction G T P a x) =
      Global.ProfiniteIntegerRing.rationalToPadic p a •
        rationalToPrime G T P p hP x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp only [rationalScalarAction, TateScalarExtension.action_tmul,
        rationalToPrime_tmul, toPrime_smul,
        Global.ProfiniteIntegerRing.rationalToPadic_tmul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Rat.cast_mul]
      congr 1
      change (Global.ProfiniteIntegerRing.toPadic p a : ℚ_[p]) *
        ((q : ℚ_[p]) * (r : ℚ_[p])) =
        ((q : ℚ_[p]) * (Global.ProfiniteIntegerRing.toPadic p a : ℚ_[p])) *
          (r : ℚ_[p])
      ring
    | add x y hx hy => simp_all [smul_add]
  | add a b ha hb => simp_all [add_smul]

/-- The selected actual coordinate map, semilinear over rational residue scalars. -/
def rationalToPrimeSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    let := rationalScalarModule G T P
    Rational G T P →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      PrimeAdic.Rational G T p := by
  let := rationalScalarModule G T P
  exact { (rationalToPrime G T P p hP).toAddHom with
    map_smul' := rationalToPrime_scalarAction G T P p hP }

@[simp] theorem rationalToPrimeSemilinear_apply (hP : ∀ n : ℕ, P (p ^ n))
    (x : Rational G T P) :
    rationalToPrimeSemilinear G T P p hP x = rationalToPrime G T P p hP x := rfl

/-- Full rational coordinates preserve the canonical local scalar projection. -/
theorem rationalFullToPrime_scalarAction
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull G T) :
    rationalFullToPrime G T p (rationalScalarAction G T (fun _ => True) a x) =
      Global.ProfiniteIntegerRing.rationalToPadic p a • rationalFullToPrime G T p x :=
  rationalToPrime_scalarAction G T (fun _ => True) p (fun _ => trivial) a x

/-- The full actual rational coordinate map as a semilinear map. -/
def rationalFullToPrimeSemilinear :
    let := rationalScalarModule G T (fun _ => True)
    RationalFull G T →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      PrimeAdic.Rational G T p :=
  rationalToPrimeSemilinear G T (fun _ => True) p (fun _ => trivial)

@[simp] theorem rationalFullToPrimeSemilinear_apply (x : RationalFull G T) :
    rationalFullToPrimeSemilinear G T p x = rationalFullToPrime G T p x := rfl

/-- Away rational coordinates intertwine the canonical away scalar projection. -/
theorem rationalAwayToPrime_scalarAction (m : ℕ) (h : Nat.Coprime p m)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway G T m) :
    rationalAwayToPrime G T p m h (rationalAwayScalarAction G T m a x) =
      Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h a •
        rationalAwayToPrime G T p m h x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp only [rationalAwayScalarAction, TateScalarExtension.action_tmul,
        rationalAwayToPrime_tmul, awayToPrime_smul,
        Global.PrimeToProfiniteIntegerRing.rationalToPadic_tmul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Rat.cast_mul]
      congr 1
      change (Global.PrimeToProfiniteIntegerRing.toPadic p m h a : ℚ_[p]) *
        ((q : ℚ_[p]) * (r : ℚ_[p])) =
        ((q : ℚ_[p]) * (Global.PrimeToProfiniteIntegerRing.toPadic p m h a : ℚ_[p])) *
          (r : ℚ_[p])
      ring
    | add x y hx hy => simp_all [smul_add]
  | add a b ha hb => simp_all [add_smul]

/-- The away actual rational coordinate map as a semilinear map. -/
def rationalAwayToPrimeSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    let := rationalAwayScalarModule G T m
    RationalAway G T m →ₛₗ[
      (Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h).toRingHom]
      PrimeAdic.Rational G T p := by
  let := rationalAwayScalarModule G T m
  exact { (rationalAwayToPrime G T p m h).toAddHom with
    map_smul' := rationalAwayToPrime_scalarAction G T p m h }

@[simp] theorem rationalAwayToPrimeSemilinear_apply (m : ℕ) (h : Nat.Coprime p m)
    (x : RationalAway G T m) :
    rationalAwayToPrimeSemilinear G T p m h x = rationalAwayToPrime G T p m h x := rfl

/-- Restricting both the rational scalar and the Tate vector preserves the local action. -/
theorem rationalAwayToPrime_restrictAway_scalarAction (m : ℕ) (h : Nat.Coprime p m)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull G T) :
    rationalAwayToPrime G T p m h
      (rationalAwayScalarAction G T m (rationalScalarRestrictAway m a)
        (rationalRestrictAway G T m x)) =
      Global.ProfiniteIntegerRing.rationalToPadic p a • rationalFullToPrime G T p x := by
  rw [← rationalRestrictAway_scalarAction,
    ← LinearMap.comp_apply, rationalAwayToPrime_restrictAway, rationalFullToPrime_scalarAction]

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- The semilinear packaging retains naturality for actual group homomorphisms. -/
theorem rationalToPrimeSemilinear_map (hP : ∀ n : ℕ, P (p ^ n))
    (f : G ⟶ H) (x : Rational G T P) :
    rationalToPrimeSemilinear H T P p hP (rationalMap T P f x) =
      PrimeAdic.rationalMap T p f (rationalToPrimeSemilinear G T P p hP x) :=
  LinearMap.congr_fun (rationalToPrime_map T P p hP f) x

/-- Naturality at every prime retained by the away system. -/
theorem rationalAwayToPrimeSemilinear_map (m : ℕ) (h : Nat.Coprime p m)
    (f : G ⟶ H) (x : RationalAway G T m) :
    rationalAwayToPrimeSemilinear H T p m h (rationalMap T _ f x) =
      PrimeAdic.rationalMap T p f (rationalAwayToPrimeSemilinear G T p m h x) :=
  rationalToPrimeSemilinear_map T (fun n => Nat.Coprime n m) p
    (fun n => h.pow_left n) f x

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- Rational residue scalars on the actual abelian-scheme Tate carrier. -/
@[instance_reducible] def rationalScalarModule (P : ℕ → Prop) :
    Module (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (Rational A T P) :=
  GroupScheme.Tate.rationalScalarModule A.toGrp T P

/-- Away rational residue scalars on the actual abelian-scheme Tate carrier. -/
@[instance_reducible] def rationalAwayScalarModule (m : ℕ) :
    Module (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (RationalAway A T m) :=
  GroupScheme.Tate.rationalAwayScalarModule A.toGrp T m

namespace PrimeComparison

variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Selected rational prime extraction for an actual abelian scheme. -/
abbrev rationalToPrimeSemilinear (hP : ∀ n : ℕ, P (p ^ n)) :
    let := rationalScalarModule A T P
    Rational A T P →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalToPrimeSemilinear A.toGrp T P p hP

/-- Full rational prime extraction for an actual abelian scheme. -/
abbrev rationalFullToPrimeSemilinear :
    let := rationalScalarModule A T (fun _ => True)
    RationalFull A T →ₛₗ[(Global.ProfiniteIntegerRing.rationalToPadic p).toRingHom]
      PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalFullToPrimeSemilinear A.toGrp T p

/-- Away rational prime extraction for an actual abelian scheme. -/
abbrev rationalAwayToPrimeSemilinear (m : ℕ) (h : Nat.Coprime p m) :
    let := rationalAwayScalarModule A T m
    RationalAway A T m →ₛₗ[
      (Global.PrimeToProfiniteIntegerRing.rationalToPadic p m h).toRingHom]
      PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalAwayToPrimeSemilinear A.toGrp T p m h

variable {A} {B : AbelianScheme S}

/-- Selected semilinear coordinates commute with actual abelian-scheme homomorphisms. -/
theorem rationalToPrimeSemilinear_map (hP : ∀ n : ℕ, P (p ^ n))
    (f : A ⟶ B) (x : Rational A T P) :
    rationalToPrimeSemilinear B T P p hP (rationalMap T P f x) =
      PrimeAdic.rationalMap T p f (rationalToPrimeSemilinear A T P p hP x) :=
  GroupScheme.Tate.PrimeComparison.rationalToPrimeSemilinear_map T P p hP
    (AbelianScheme.groupHom f) x

end PrimeComparison
end Langlands.AbelianScheme.Tate
