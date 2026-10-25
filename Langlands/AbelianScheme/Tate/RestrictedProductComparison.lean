import Langlands.AbelianScheme.Tate.RestrictedProductProof
import Langlands.AbelianScheme.Tate.RationalPrimeScalars
import Mathlib.Algebra.Module.TransferInstance

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] primeFact
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The proved full comparison, normalized by the actual rational prime coordinates. -/
def rationalRestrictedProductEquiv : RationalFull G T ≃+ RationalRestrictedProduct G T :=
  (rationalRestrictedProductComparison G T).choose

@[simp] theorem rationalRestrictedProductEquiv_apply (x : RationalFull G T) (p : Nat.Primes) :
    rationalRestrictedProductEquiv G T x p = rationalFullToPrime G T (p : ℕ) x :=
  (rationalRestrictedProductComparison G T).choose_spec x p

@[simp] theorem rationalRestrictedProductEquiv_symm_apply
    (x : RationalRestrictedProduct G T) (p : Nat.Primes) :
    rationalFullToPrime G T (p : ℕ) ((rationalRestrictedProductEquiv G T).symm x) = x p := by
  simpa only [AddEquiv.apply_symm_apply] using
    (rationalRestrictedProductEquiv_apply G T ((rationalRestrictedProductEquiv G T).symm x) p).symm

/-- Coordinate normalization determines the full comparison uniquely. -/
theorem rationalRestrictedProductEquiv_unique
    (e : RationalFull G T ≃+ RationalRestrictedProduct G T)
    (he : ∀ x p, e x p = rationalFullToPrime G T (p : ℕ) x) :
    e = rationalRestrictedProductEquiv G T := by
  ext x p
  exact (he x p).trans (rationalRestrictedProductEquiv_apply G T x p).symm

/-- The proved away comparison, for every natural excluded modulus. -/
def rationalAwayRestrictedProductEquiv (m : ℕ) :
    RationalAway G T m ≃+ RationalAwayRestrictedProduct G T m :=
  (rationalAwayRestrictedProductComparison G T m).choose

@[simp] theorem rationalAwayRestrictedProductEquiv_apply (m : ℕ)
    (x : RationalAway G T m) (p : AwayPrime m) :
    rationalAwayRestrictedProductEquiv G T m x p =
      rationalAwayToPrime G T (p.val : ℕ) m p.property x :=
  (rationalAwayRestrictedProductComparison G T m).choose_spec x p

@[simp] theorem rationalAwayRestrictedProductEquiv_symm_apply (m : ℕ)
    (x : RationalAwayRestrictedProduct G T m) (p : AwayPrime m) :
    rationalAwayToPrime G T (p.val : ℕ) m p.property
      ((rationalAwayRestrictedProductEquiv G T m).symm x) = x p := by
  simpa only [AddEquiv.apply_symm_apply] using
    (rationalAwayRestrictedProductEquiv_apply G T m
      ((rationalAwayRestrictedProductEquiv G T m).symm x) p).symm

theorem rationalAwayRestrictedProductEquiv_unique (m : ℕ)
    (e : RationalAway G T m ≃+ RationalAwayRestrictedProduct G T m)
    (he : ∀ x p, e x p = rationalAwayToPrime G T (p.val : ℕ) m p.property x) :
    e = rationalAwayRestrictedProductEquiv G T m := by
  ext x p
  exact (he x p).trans (rationalAwayRestrictedProductEquiv_apply G T m x p).symm

@[simp] theorem rationalRestrictedProductEquiv_toRational (x : Full G T) :
    rationalRestrictedProductEquiv G T (toRational G T (fun _ => True) x) =
      integralToRestrictedProduct G T x := by
  ext p
  rw [rationalRestrictedProductEquiv_apply, integralToRestrictedProduct_apply]
  exact rationalToPrime_toRational G T (fun _ => True) (p : ℕ) (fun _ => trivial) x

@[simp] theorem rationalAwayRestrictedProductEquiv_toRational (m : ℕ) (x : Away G T m) :
    rationalAwayRestrictedProductEquiv G T m (toRational G T (fun n => Nat.Coprime n m) x) =
      integralToAwayRestrictedProduct G T m x := by
  ext p
  rw [rationalAwayRestrictedProductEquiv_apply, integralToAwayRestrictedProduct_apply]
  exact rationalToPrime_toRational G T (fun n => Nat.Coprime n m) (p.val : ℕ)
    (fun n => p.property.pow_left n) x

/-- Full-to-away restriction commutes with the normalized rational comparisons. -/
theorem rationalRestrictedProductEquiv_restrictAway (m : ℕ) (x : RationalFull G T) :
    rationalAwayRestrictedProductEquiv G T m (rationalRestrictAway G T m x) =
      restrictedProductRestrict G T m (rationalRestrictedProductEquiv G T x) := by
  ext p
  simp only [rationalAwayRestrictedProductEquiv_apply, restrictedProductRestrict_apply,
    rationalRestrictedProductEquiv_apply]
  exact LinearMap.congr_fun (rationalAwayToPrime_restrictAway G T (p.val : ℕ) m p.property) x

theorem rationalRestrictedProductEquiv_symm_restrictAway (m : ℕ)
    (x : RationalRestrictedProduct G T) :
    (rationalAwayRestrictedProductEquiv G T m).symm (restrictedProductRestrict G T m x) =
      rationalRestrictAway G T m ((rationalRestrictedProductEquiv G T).symm x) := by
  apply (rationalAwayRestrictedProductEquiv G T m).injective
  simp only [AddEquiv.apply_symm_apply, rationalRestrictedProductEquiv_restrictAway]

/-- Rational scalar transport to the existing additive restricted-product carrier. -/
@[instance_reducible] def restrictedProductRatModule : Module ℚ (RationalRestrictedProduct G T) :=
  (rationalRestrictedProductEquiv G T).symm.module ℚ

@[instance_reducible] def awayRestrictedProductRatModule (m : ℕ) :
    Module ℚ (RationalAwayRestrictedProduct G T m) :=
  (rationalAwayRestrictedProductEquiv G T m).symm.module ℚ

attribute [local instance] restrictedProductRatModule awayRestrictedProductRatModule

/-- The transported rational action is exactly coordinatewise rational multiplication. -/
@[simp] theorem restrictedProductRatModule_smul_apply (q : ℚ)
    (x : RationalRestrictedProduct G T) (p : Nat.Primes) :
    (q • x) p = q • x p := by
  change rationalRestrictedProductEquiv G T
    (q • (rationalRestrictedProductEquiv G T).symm x) p = _
  rw [rationalRestrictedProductEquiv_apply, map_smul, rationalRestrictedProductEquiv_symm_apply]

@[simp] theorem awayRestrictedProductRatModule_smul_apply (m : ℕ) (q : ℚ)
    (x : RationalAwayRestrictedProduct G T m) (p : AwayPrime m) :
    (q • x) p = q • x p := by
  change rationalAwayRestrictedProductEquiv G T m
    (q • (rationalAwayRestrictedProductEquiv G T m).symm x) p = _
  rw [rationalAwayRestrictedProductEquiv_apply, map_smul,
    rationalAwayRestrictedProductEquiv_symm_apply]

/-- The full normalized comparison as a rational linear equivalence. -/
def rationalRestrictedProductLinearEquiv :
    RationalFull G T ≃ₗ[ℚ] RationalRestrictedProduct G T :=
  ((rationalRestrictedProductEquiv G T).symm.linearEquiv ℚ).symm

/-- The away normalized comparison as a rational linear equivalence. -/
def rationalAwayRestrictedProductLinearEquiv (m : ℕ) :
    RationalAway G T m ≃ₗ[ℚ] RationalAwayRestrictedProduct G T m :=
  ((rationalAwayRestrictedProductEquiv G T m).symm.linearEquiv ℚ).symm

@[simp] theorem rationalRestrictedProductLinearEquiv_apply (x : RationalFull G T) :
    rationalRestrictedProductLinearEquiv G T x = rationalRestrictedProductEquiv G T x := rfl

@[simp] theorem rationalAwayRestrictedProductLinearEquiv_apply (m : ℕ) (x : RationalAway G T m) :
    rationalAwayRestrictedProductLinearEquiv G T m x =
      rationalAwayRestrictedProductEquiv G T m x := rfl

/-- Scalar compatibility with the published rational residue projection. -/
theorem rationalRestrictedProductEquiv_scalarAction
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull G T) (p : Nat.Primes) :
    rationalRestrictedProductEquiv G T (rationalScalarAction G T (fun _ => True) a x) p =
      Global.ProfiniteIntegerRing.rationalToPadic (p : ℕ) a •
        rationalRestrictedProductEquiv G T x p := by
  simp only [rationalRestrictedProductEquiv_apply, rationalFullToPrime_scalarAction]

theorem rationalAwayRestrictedProductEquiv_scalarAction (m : ℕ)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway G T m)
    (p : AwayPrime m) :
    rationalAwayRestrictedProductEquiv G T m (rationalAwayScalarAction G T m a x) p =
      Global.PrimeToProfiniteIntegerRing.rationalToPadic (p.val : ℕ) m p.property a •
        rationalAwayRestrictedProductEquiv G T m x p := by
  simp only [rationalAwayRestrictedProductEquiv_apply, rationalAwayToPrime_scalarAction]

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Naturality for actual group-scheme homomorphisms. -/
theorem rationalRestrictedProductEquiv_map (f : G ⟶ H) (x : RationalFull G T) :
    rationalRestrictedProductEquiv H T (rationalMap T (fun _ => True) f x) =
      restrictedProductMap T f (rationalRestrictedProductEquiv G T x) := by
  ext p
  simp only [rationalRestrictedProductEquiv_apply, restrictedProductMap_apply]
  exact LinearMap.congr_fun (rationalToPrime_map T (fun _ => True) (p : ℕ)
    (fun _ => trivial) f) x

theorem rationalAwayRestrictedProductEquiv_map (m : ℕ) (f : G ⟶ H) (x : RationalAway G T m) :
    rationalAwayRestrictedProductEquiv H T m (rationalMap T (fun n => Nat.Coprime n m) f x) =
      awayRestrictedProductMap T m f (rationalAwayRestrictedProductEquiv G T m x) := by
  ext p
  simp only [rationalAwayRestrictedProductEquiv_apply, awayRestrictedProductMap_apply]
  exact LinearMap.congr_fun (rationalToPrime_map T (fun n => Nat.Coprime n m) (p.val : ℕ)
    (fun n => p.property.pow_left n) f) x

theorem rationalRestrictedProductEquiv_symm_map (f : G ⟶ H) (x : RationalRestrictedProduct G T) :
    (rationalRestrictedProductEquiv H T).symm (restrictedProductMap T f x) =
      rationalMap T (fun _ => True) f ((rationalRestrictedProductEquiv G T).symm x) := by
  apply (rationalRestrictedProductEquiv H T).injective
  simp only [AddEquiv.apply_symm_apply, rationalRestrictedProductEquiv_map]

theorem rationalAwayRestrictedProductEquiv_symm_map (m : ℕ) (f : G ⟶ H)
    (x : RationalAwayRestrictedProduct G T m) :
    (rationalAwayRestrictedProductEquiv H T m).symm (awayRestrictedProductMap T m f x) =
      rationalMap T (fun n => Nat.Coprime n m) f
        ((rationalAwayRestrictedProductEquiv G T m).symm x) := by
  apply (rationalAwayRestrictedProductEquiv H T m).injective
  simp only [AddEquiv.apply_symm_apply, rationalAwayRestrictedProductEquiv_map]

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison
universe u
open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] GroupScheme.Tate.PrimeComparison.primeFact
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- The normalized full comparison on actual abelian-scheme Tate modules. -/
abbrev rationalRestrictedProductEquiv :
    RationalFull A T ≃+ RationalRestrictedProduct A T :=
  GroupScheme.Tate.PrimeComparison.rationalRestrictedProductEquiv A.toGrp T

/-- The normalized away comparison on actual abelian-scheme Tate modules. -/
abbrev rationalAwayRestrictedProductEquiv (m : ℕ) :
    RationalAway A T m ≃+ RationalAwayRestrictedProduct A T m :=
  GroupScheme.Tate.PrimeComparison.rationalAwayRestrictedProductEquiv A.toGrp T m

@[instance_reducible] def restrictedProductRatModule :
    Module ℚ (RationalRestrictedProduct A T) :=
  GroupScheme.Tate.PrimeComparison.restrictedProductRatModule A.toGrp T

@[instance_reducible] def awayRestrictedProductRatModule (m : ℕ) :
    Module ℚ (RationalAwayRestrictedProduct A T m) :=
  GroupScheme.Tate.PrimeComparison.awayRestrictedProductRatModule A.toGrp T m

attribute [local instance] restrictedProductRatModule awayRestrictedProductRatModule

abbrev rationalRestrictedProductLinearEquiv :
    RationalFull A T ≃ₗ[ℚ] RationalRestrictedProduct A T :=
  GroupScheme.Tate.PrimeComparison.rationalRestrictedProductLinearEquiv A.toGrp T

abbrev rationalAwayRestrictedProductLinearEquiv (m : ℕ) :
    RationalAway A T m ≃ₗ[ℚ] RationalAwayRestrictedProduct A T m :=
  GroupScheme.Tate.PrimeComparison.rationalAwayRestrictedProductLinearEquiv A.toGrp T m

@[simp] theorem rationalRestrictedProductEquiv_apply (x : RationalFull A T) (p : Nat.Primes) :
    rationalRestrictedProductEquiv A T x p = rationalFullToPrime A T (p : ℕ) x :=
  GroupScheme.Tate.PrimeComparison.rationalRestrictedProductEquiv_apply A.toGrp T x p

@[simp] theorem rationalAwayRestrictedProductEquiv_apply (m : ℕ)
    (x : RationalAway A T m) (p : AwayPrime m) :
    rationalAwayRestrictedProductEquiv A T m x p =
      rationalAwayToPrime A T (p.val : ℕ) m p.property x :=
  GroupScheme.Tate.PrimeComparison.rationalAwayRestrictedProductEquiv_apply A.toGrp T m x p

theorem rationalRestrictedProductEquiv_restrictAway (m : ℕ) (x : RationalFull A T) :
    rationalAwayRestrictedProductEquiv A T m
      (GroupScheme.Tate.rationalRestrictAway A.toGrp T m x) =
      restrictedProductRestrict A T m (rationalRestrictedProductEquiv A T x) :=
  GroupScheme.Tate.PrimeComparison.rationalRestrictedProductEquiv_restrictAway A.toGrp T m x

variable {A} {B : AbelianScheme S}

theorem rationalRestrictedProductEquiv_map (f : A ⟶ B) (x : RationalFull A T) :
    rationalRestrictedProductEquiv B T (rationalMap T (fun _ => True) f x) =
      restrictedProductMap T f (rationalRestrictedProductEquiv A T x) :=
  GroupScheme.Tate.PrimeComparison.rationalRestrictedProductEquiv_map T
    (AbelianScheme.groupHom f) x

theorem rationalAwayRestrictedProductEquiv_map (m : ℕ) (f : A ⟶ B) (x : RationalAway A T m) :
    rationalAwayRestrictedProductEquiv B T m (rationalMap T (fun n => Nat.Coprime n m) f x) =
      awayRestrictedProductMap T m f (rationalAwayRestrictedProductEquiv A T m x) :=
  GroupScheme.Tate.PrimeComparison.rationalAwayRestrictedProductEquiv_map T m
    (AbelianScheme.groupHom f) x

end Langlands.AbelianScheme.Tate.PrimeComparison
