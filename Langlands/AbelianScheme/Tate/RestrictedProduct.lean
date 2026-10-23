import Langlands.AbelianScheme.Tate.RationalPrime
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (p : ℕ) [Fact p.Prime]

/-- The actual integral image inside the local rational Tate module. -/
def integralImage : Submodule ℤ_[p] (Rational G T p) :=
  LinearMap.range (toRational G T p)

@[simp] theorem mem_integralImage (y : Rational G T p) :
    y ∈ integralImage G T p ↔ ∃ x : Integral G T p, toRational G T p x = y := Iff.rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

theorem rationalMap_mem_integralImage (f : G ⟶ H) {y : Rational G T p}
    (hy : y ∈ integralImage G T p) :
    rationalMap T p f y ∈ integralImage H T p := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨map T p f x, ?_⟩
  simp only [toRational_apply, rationalMap_tmul]
  rfl

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] primeFact
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Local rational Tate modules, integral at all but finitely many primes. -/
abbrev RationalRestrictedProduct :=
  RestrictedProduct (fun p : Nat.Primes => PrimeAdic.Rational G T (p : ℕ))
    (fun p => (PrimeAdic.integralImage G T (p : ℕ)).toAddSubgroup) Filter.cofinite

/-- The same restricted product over primes coprime to an excluded modulus. -/
abbrev RationalAwayRestrictedProduct (m : ℕ) :=
  RestrictedProduct (fun p : AwayPrime m => PrimeAdic.Rational G T (p.val : ℕ))
    (fun p => (PrimeAdic.integralImage G T (p.val : ℕ)).toAddSubgroup) Filter.cofinite

/-- Integral full Tate coordinates give an everywhere-integral restricted family. -/
def integralToRestrictedProduct : Full G T →+ RationalRestrictedProduct G T where
  toFun x := ⟨fun p => PrimeAdic.toRational G T (p : ℕ) (fullToPrime G T (p : ℕ) x),
    Filter.Eventually.of_forall (fun p => ⟨fullToPrime G T (p : ℕ) x, rfl⟩)⟩
  map_zero' := by ext p; exact map_zero ((PrimeAdic.toRational G T (p : ℕ)).toAddMonoidHom.comp (fullToPrime G T (p : ℕ)))
  map_add' x y := by ext p; exact map_add ((PrimeAdic.toRational G T (p : ℕ)).toAddMonoidHom.comp (fullToPrime G T (p : ℕ))) x y

@[simp] theorem integralToRestrictedProduct_apply (x : Full G T) (p : Nat.Primes) :
    integralToRestrictedProduct G T x p =
      PrimeAdic.toRational G T (p : ℕ) (fullToPrime G T (p : ℕ) x) := rfl

/-- Integral away Tate coordinates give an everywhere-integral restricted family. -/
def integralToAwayRestrictedProduct (m : ℕ) :
    Away G T m →+ RationalAwayRestrictedProduct G T m where
  toFun x := ⟨fun p => PrimeAdic.toRational G T (p.val : ℕ)
      (awayToPrime G T (p.val : ℕ) m p.property x),
    Filter.Eventually.of_forall (fun p =>
      ⟨awayToPrime G T (p.val : ℕ) m p.property x, rfl⟩)⟩
  map_zero' := by ext p; exact map_zero ((PrimeAdic.toRational G T (p.val : ℕ)).toAddMonoidHom.comp (awayToPrime G T (p.val : ℕ) m p.property))
  map_add' x y := by ext p; exact map_add ((PrimeAdic.toRational G T (p.val : ℕ)).toAddMonoidHom.comp (awayToPrime G T (p.val : ℕ) m p.property)) x y

@[simp] theorem integralToAwayRestrictedProduct_apply (m : ℕ) (x : Away G T m)
    (p : AwayPrime m) :
    integralToAwayRestrictedProduct G T m x p = PrimeAdic.toRational G T (p.val : ℕ)
      (awayToPrime G T (p.val : ℕ) m p.property x) := rfl

/-- Restriction of a rational restricted family to the retained primes. -/
def restrictedProductRestrict (m : ℕ) :
    RationalRestrictedProduct G T →+ RationalAwayRestrictedProduct G T m where
  toFun x := ⟨fun p => x p.val, Subtype.val_injective.tendsto_cofinite.eventually x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem restrictedProductRestrict_apply (m : ℕ)
    (x : RationalRestrictedProduct G T) (p : AwayPrime m) :
    restrictedProductRestrict G T m x p = x p.val := rfl

theorem integralToRestrictedProduct_restrictAway (m : ℕ) (x : Full G T) :
    integralToAwayRestrictedProduct G T m (restrictAway G T m x) =
      restrictedProductRestrict G T m (integralToRestrictedProduct G T x) := rfl

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- Coordinatewise map induced by an actual group-scheme homomorphism. -/
def restrictedProductMap (f : G ⟶ H) :
    RationalRestrictedProduct G T →+ RationalRestrictedProduct H T where
  toFun x := ⟨fun p => PrimeAdic.rationalMap T (p : ℕ) f (x p),
    x.property.mono (fun p hp => PrimeAdic.rationalMap_mem_integralImage T (p : ℕ) f hp)⟩
  map_zero' := by ext p; exact map_zero (PrimeAdic.rationalMap T (p : ℕ) f)
  map_add' x y := by ext p; exact map_add (PrimeAdic.rationalMap T (p : ℕ) f) (x p) (y p)

/-- Coordinatewise induced map at the retained primes. -/
def awayRestrictedProductMap (m : ℕ) (f : G ⟶ H) :
    RationalAwayRestrictedProduct G T m →+ RationalAwayRestrictedProduct H T m where
  toFun x := ⟨fun p => PrimeAdic.rationalMap T (p.val : ℕ) f (x p),
    x.property.mono (fun p hp => PrimeAdic.rationalMap_mem_integralImage T (p.val : ℕ) f hp)⟩
  map_zero' := by ext p; exact map_zero (PrimeAdic.rationalMap T (p.val : ℕ) f)
  map_add' x y := by ext p; exact map_add (PrimeAdic.rationalMap T (p.val : ℕ) f) (x p) (y p)

@[simp] theorem restrictedProductMap_apply (f : G ⟶ H)
    (x : RationalRestrictedProduct G T) (p : Nat.Primes) :
    restrictedProductMap T f x p = PrimeAdic.rationalMap T (p : ℕ) f (x p) := rfl

@[simp] theorem awayRestrictedProductMap_apply (m : ℕ) (f : G ⟶ H)
    (x : RationalAwayRestrictedProduct G T m) (p : AwayPrime m) :
    awayRestrictedProductMap T m f x p = PrimeAdic.rationalMap T (p.val : ℕ) f (x p) := rfl

theorem restrictedProductMap_integral (f : G ⟶ H) (x : Full G T) :
    restrictedProductMap T f (integralToRestrictedProduct G T x) =
      integralToRestrictedProduct H T (map T (fun _ => True) f x) := by
  ext p
  simp only [restrictedProductMap_apply, integralToRestrictedProduct_apply,
    PrimeAdic.toRational_apply, PrimeAdic.rationalMap_tmul]
  rfl

theorem awayRestrictedProductMap_integral (m : ℕ) (f : G ⟶ H) (x : Away G T m) :
    awayRestrictedProductMap T m f (integralToAwayRestrictedProduct G T m x) =
      integralToAwayRestrictedProduct H T m (map T (fun n => Nat.Coprime n m) f x) := by
  ext p
  simp only [awayRestrictedProductMap_apply, integralToAwayRestrictedProduct_apply,
    PrimeAdic.toRational_apply, PrimeAdic.rationalMap_tmul]
  rfl

@[simp] theorem restrictedProductMap_id :
    restrictedProductMap T (𝟙 G) = AddMonoidHom.id (RationalRestrictedProduct G T) := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_id (G := G) T (p : ℕ)) (x p)

@[simp] theorem awayRestrictedProductMap_id (m : ℕ) :
    awayRestrictedProductMap T m (𝟙 G) =
      AddMonoidHom.id (RationalAwayRestrictedProduct G T m) := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_id (G := G) T (p.val : ℕ)) (x p)

theorem restrictedProductMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    restrictedProductMap T (f ≫ g) = (restrictedProductMap T g).comp (restrictedProductMap T f) := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_comp T (p : ℕ) f g) (x p)

theorem awayRestrictedProductMap_comp (m : ℕ) (f : G ⟶ H) (g : H ⟶ K) :
    awayRestrictedProductMap T m (f ≫ g) =
      (awayRestrictedProductMap T m g).comp (awayRestrictedProductMap T m f) := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_comp T (p.val : ℕ) f g) (x p)

theorem restrictedProductMap_mul (f g : G ⟶ H) :
    restrictedProductMap T (f * g) = restrictedProductMap T f + restrictedProductMap T g := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_mul T (p : ℕ) f g) (x p)

theorem awayRestrictedProductMap_mul (m : ℕ) (f g : G ⟶ H) :
    awayRestrictedProductMap T m (f * g) =
      awayRestrictedProductMap T m f + awayRestrictedProductMap T m g := by
  ext x p
  exact LinearMap.congr_fun (PrimeAdic.rationalMap_mul T (p.val : ℕ) f g) (x p)

theorem restrictedProductRestrict_map (m : ℕ) (f : G ⟶ H) (x : RationalRestrictedProduct G T) :
    restrictedProductRestrict H T m (restrictedProductMap T f x) =
      awayRestrictedProductMap T m f (restrictedProductRestrict G T m x) := rfl

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

abbrev RationalRestrictedProduct := GroupScheme.Tate.PrimeComparison.RationalRestrictedProduct A.toGrp T
abbrev RationalAwayRestrictedProduct (m : ℕ) :=
  GroupScheme.Tate.PrimeComparison.RationalAwayRestrictedProduct A.toGrp T m
abbrev integralToRestrictedProduct : Full A T →+ RationalRestrictedProduct A T :=
  GroupScheme.Tate.PrimeComparison.integralToRestrictedProduct A.toGrp T
abbrev integralToAwayRestrictedProduct (m : ℕ) :
    Away A T m →+ RationalAwayRestrictedProduct A T m :=
  GroupScheme.Tate.PrimeComparison.integralToAwayRestrictedProduct A.toGrp T m
abbrev restrictedProductRestrict (m : ℕ) :
    RationalRestrictedProduct A T →+ RationalAwayRestrictedProduct A T m :=
  GroupScheme.Tate.PrimeComparison.restrictedProductRestrict A.toGrp T m

variable {A} {B : AbelianScheme S}
abbrev restrictedProductMap (f : A ⟶ B) :
    RationalRestrictedProduct A T →+ RationalRestrictedProduct B T :=
  GroupScheme.Tate.PrimeComparison.restrictedProductMap T (AbelianScheme.groupHom f)
abbrev awayRestrictedProductMap (m : ℕ) (f : A ⟶ B) :
    RationalAwayRestrictedProduct A T m →+ RationalAwayRestrictedProduct B T m :=
  GroupScheme.Tate.PrimeComparison.awayRestrictedProductMap T m (AbelianScheme.groupHom f)

theorem restrictedProductMap_add (f g : A ⟶ B) :
    restrictedProductMap T (f + g) = restrictedProductMap T f + restrictedProductMap T g :=
  GroupScheme.Tate.PrimeComparison.restrictedProductMap_mul T
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

theorem awayRestrictedProductMap_add (m : ℕ) (f g : A ⟶ B) :
    awayRestrictedProductMap T m (f + g) =
      awayRestrictedProductMap T m f + awayRestrictedProductMap T m g :=
  GroupScheme.Tate.PrimeComparison.awayRestrictedProductMap_mul T m
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

end Langlands.AbelianScheme.Tate.PrimeComparison
