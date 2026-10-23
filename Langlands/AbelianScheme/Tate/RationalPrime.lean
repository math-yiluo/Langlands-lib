import Langlands.AbelianScheme.Tate.Rational
import Langlands.AbelianScheme.Tate.PrimeComparison

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S) (p : ℕ) [Fact p.Prime]

instance rationalRatModule : Module ℚ (Rational G T p) :=
  inferInstanceAs (Module ℚ (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))

instance rationalPadicIntModule : Module ℤ_[p] (Rational G T p) :=
  inferInstanceAs (Module ℤ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))

instance rationalRatScalarTower : IsScalarTower ℚ ℚ_[p] (Rational G T p) :=
  inferInstanceAs (IsScalarTower ℚ ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))

instance rationalPadicIntScalarTower : IsScalarTower ℤ_[p] ℚ_[p] (Rational G T p) :=
  inferInstanceAs (IsScalarTower ℤ_[p] ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))

/-- The canonical map from the integral prime-adic Tate module to its rationalization. -/
def toRational : Integral G T p →ₗ[ℤ_[p]] Rational G T p :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (Integral G T p) 1

@[simp] theorem toRational_apply (x : Integral G T p) :
    toRational G T p x = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := rfl

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S) (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- The canonical rational map to a prime-adic rational Tate module. -/
def rationalToPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Rational G T P →ₗ[ℚ] PrimeAdic.Rational G T p :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun q := q • ((PrimeAdic.toRational G T p).restrictScalars ℤ).comp
      (toPrime G T P p hP).toIntLinearMap
    map_add' q r := add_smul q r _
    map_smul' q r := mul_smul q r _ }

@[simp] theorem rationalToPrime_tmul (hP : ∀ n : ℕ, P (p ^ n))
    (q : ℚ) (x : Integral G T P) :
    rationalToPrime G T P p hP (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime G T P p hP x := by
  change q • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime G T P p hP x) = _
  rw [TensorProduct.smul_tmul']
  simp

/-- The pure-tensor formula determines the rational extraction map. -/
theorem rationalToPrime_unique (hP : ∀ n : ℕ, P (p ^ n))
    (g : Rational G T P →ₗ[ℚ] PrimeAdic.Rational G T p)
    (hg : ∀ (q : ℚ) (x : Integral G T P),
      g (q ⊗ₜ[ℤ] x) = (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime G T P p hP x) :
    g = rationalToPrime G T P p hP := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  rw [hg, rationalToPrime_tmul]

@[simp] theorem rationalToPrime_toRational (hP : ∀ n : ℕ, P (p ^ n))
    (x : Integral G T P) :
    rationalToPrime G T P p hP (toRational G T P x) =
      PrimeAdic.toRational G T p (toPrime G T P p hP x) := by
  change rationalToPrime G T P p hP ((1 : ℚ) ⊗ₜ[ℤ] x) =
    (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] toPrime G T P p hP x
  rw [rationalToPrime_tmul, Rat.cast_one]

/-- Rational extraction from the full actual Tate module. -/
def rationalFullToPrime : RationalFull G T →ₗ[ℚ] PrimeAdic.Rational G T p :=
  rationalToPrime G T (fun _ => True) p (fun _ => trivial)

@[simp] theorem rationalFullToPrime_tmul (q : ℚ) (x : Full G T) :
    rationalFullToPrime G T p (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] fullToPrime G T p x :=
  rationalToPrime_tmul G T (fun _ => True) p (fun _ => trivial) q x

/-- Rational extraction at a prime retained by the away system. -/
def rationalAwayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    RationalAway G T m →ₗ[ℚ] PrimeAdic.Rational G T p :=
  rationalToPrime G T (fun n => Nat.Coprime n m) p (fun n => h.pow_left n)

@[simp] theorem rationalAwayToPrime_tmul (m : ℕ) (h : Nat.Coprime p m)
    (q : ℚ) (x : Away G T m) :
    rationalAwayToPrime G T p m h (q ⊗ₜ[ℤ] x) =
      (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] awayToPrime G T p m h x :=
  rationalToPrime_tmul G T (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) q x

theorem rationalAwayToPrime_restrictAway (m : ℕ) (h : Nat.Coprime p m) :
    (rationalAwayToPrime G T p m h).comp (rationalRestrictAway G T m) =
      rationalFullToPrime G T p := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp only [LinearMap.comp_apply, rationalRestrictAway_tmul,
    rationalAwayToPrime_tmul, rationalFullToPrime_tmul, awayToPrime_restrictAway]
  rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

theorem rationalToPrime_map (hP : ∀ n : ℕ, P (p ^ n)) (f : G ⟶ H) :
    (rationalToPrime H T P p hP).comp (rationalMap T P f) =
      ((PrimeAdic.rationalMap T p f).restrictScalars ℚ).comp
        (rationalToPrime G T P p hP) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  change rationalToPrime H T P p hP (rationalMap T P f (q ⊗ₜ[ℤ] x)) =
    PrimeAdic.rationalMap T p f (rationalToPrime G T P p hP (q ⊗ₜ[ℤ] x))
  simp only [rationalMap_tmul, rationalToPrime_tmul,
    PrimeAdic.rationalMap_tmul, toPrime_map]
  rfl

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeAdic

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (p : ℕ) [Fact p.Prime]

/-- Canonical rationalization of the actual integral prime-adic Tate module. -/
abbrev toRational : Integral A T p →ₗ[ℤ_[p]] Rational A T p :=
  GroupScheme.Tate.PrimeAdic.toRational A.toGrp T p

end Langlands.AbelianScheme.Tate.PrimeAdic

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)
variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Selected rational prime coordinate of the actual abelian-scheme Tate module. -/
abbrev rationalToPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Rational A T P →ₗ[ℚ] PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalToPrime A.toGrp T P p hP

/-- Full rational prime coordinate of the actual abelian-scheme Tate module. -/
abbrev rationalFullToPrime : RationalFull A T →ₗ[ℚ] PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p

/-- Away rational prime coordinate of the actual abelian-scheme Tate module. -/
abbrev rationalAwayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    RationalAway A T m →ₗ[ℚ] PrimeAdic.Rational A T p :=
  GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m h

variable {A} {B : AbelianScheme S}

/-- Rational prime coordinates commute with actual abelian-scheme homomorphisms. -/
theorem rationalToPrime_map (hP : ∀ n : ℕ, P (p ^ n)) (f : A ⟶ B) :
    (rationalToPrime B T P p hP).comp (rationalMap T P f) =
      ((PrimeAdic.rationalMap T p f).restrictScalars ℚ).comp
        (rationalToPrime A T P p hP) :=
  GroupScheme.Tate.PrimeComparison.rationalToPrime_map T P p hP
    (AbelianScheme.groupHom f)

end Langlands.AbelianScheme.Tate.PrimeComparison
