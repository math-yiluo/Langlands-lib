import Langlands.AbelianScheme.Tate.AbelianScheme
import Langlands.AbelianScheme.Tate.AbelianPrimeAdic
import Langlands.AbelianScheme.Tate.TwistPrimeComparison

/-! # Canonical prime-power coordinates of actual Tate limits -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison

open Langlands.TateTwist.Divisibility (primePowerIndex AwayPrime)

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- Read the prime-power coordinates of the actual selected torsion limit. -/
def toPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral G T P →+ PrimeAdic.Integral G T p where
  toFun x := ⟨fun n => x.val (primePowerIndex P p hP n), by
    intro n
    exact x.property (primePowerIndex P p hP n) (primePowerIndex P p hP (n + 1))
      (pow_dvd_pow p (Nat.le_succ n))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evaluation_toPrime (hP : ∀ n : ℕ, P (p ^ n))
    (n : ℕ) (x : Integral G T P) :
    PrimeAdic.evaluation G T p n (toPrime G T P p hP x) =
      evaluation G T P (primePowerIndex P p hP n) x := rfl

theorem continuous_toPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Continuous (toPrime G T P p hP) :=
  (continuous_pi (fun n => continuous_evaluation G T P
    (primePowerIndex P p hP n))).subtype_mk _

/-- The prime-adic component of the full actual Tate limit. -/
def fullToPrime : Full G T →+ PrimeAdic.Integral G T p :=
  toPrime G T (fun _ => True) p (fun _ => trivial)

/-- The prime-adic component retained by the away-from-`m` limit. -/
def awayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    Away G T m →+ PrimeAdic.Integral G T p :=
  toPrime G T (fun n => Nat.Coprime n m) p (fun n => h.pow_left n)

theorem continuous_fullToPrime : Continuous (fullToPrime G T p) :=
  continuous_toPrime G T _ p _

theorem continuous_awayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    Continuous (awayToPrime G T p m h) := continuous_toPrime G T _ p _

theorem awayToPrime_restrictAway (m : ℕ) (h : Nat.Coprime p m) (x : Full G T) :
    awayToPrime G T p m h (restrictAway G T m x) = fullToPrime G T p x := rfl

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

theorem toPrime_map (hP : ∀ n : ℕ, P (p ^ n)) (f : G ⟶ H) (x : Integral G T P) :
    toPrime H T P p hP (map T P f x) =
      PrimeAdic.map T p f (toPrime G T P p hP x) := rfl

variable (G)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

/-- The product of the existing actual prime-adic Tate modules. -/
abbrev PrimeProduct := ∀ p : Nat.Primes, PrimeAdic.Integral G T (p : ℕ)

/-- The corresponding product over retained primes. -/
abbrev AwayPrimeProduct (m : ℕ) :=
  ∀ p : AwayPrime m, PrimeAdic.Integral G T (p.val : ℕ)

/-- The canonical comparison map reads all prime-power coordinates. -/
def toPrimeProduct : Full G T →+ PrimeProduct G T where
  toFun x p := fullToPrime G T (p : ℕ) x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The away comparison map reads only retained prime-power coordinates. -/
def toAwayPrimeProduct (m : ℕ) : Away G T m →+ AwayPrimeProduct G T m where
  toFun x p := awayToPrime G T (p.val : ℕ) m p.property x
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_toPrimeProduct : Continuous (toPrimeProduct G T) :=
  continuous_pi (fun p => continuous_fullToPrime G T (p : ℕ))

theorem continuous_toAwayPrimeProduct (m : ℕ) : Continuous (toAwayPrimeProduct G T m) :=
  continuous_pi (fun p => continuous_awayToPrime G T (p.val : ℕ) m p.property)

/-- Restrict the product to the primes coprime to the excluded modulus. -/
def primeProductRestrict (m : ℕ) : PrimeProduct G T →+ AwayPrimeProduct G T m where
  toFun x p := x p.val
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_primeProductRestrict (m : ℕ) : Continuous (primeProductRestrict G T m) :=
  continuous_pi (fun p => continuous_apply p.val)

theorem toPrimeProduct_restrictAway (m : ℕ) (x : Full G T) :
    toAwayPrimeProduct G T m (restrictAway G T m x) =
      primeProductRestrict G T m (toPrimeProduct G T x) := rfl

variable {G}

/-- Product of the existing maps induced by an actual group-scheme homomorphism. -/
def primeProductMap (f : G ⟶ H) : PrimeProduct G T →+ PrimeProduct H T where
  toFun x p := PrimeAdic.map T (p : ℕ) f (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

/-- Product of the actual induced maps at retained primes. -/
def awayPrimeProductMap (m : ℕ) (f : G ⟶ H) :
    AwayPrimeProduct G T m →+ AwayPrimeProduct H T m where
  toFun x p := PrimeAdic.map T (p.val : ℕ) f (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

theorem toPrimeProduct_map (f : G ⟶ H) (x : Full G T) :
    toPrimeProduct H T (map T (fun _ => True) f x) =
      primeProductMap T f (toPrimeProduct G T x) := rfl

theorem toAwayPrimeProduct_map (m : ℕ) (f : G ⟶ H) (x : Away G T m) :
    toAwayPrimeProduct H T m (map T (fun n => Nat.Coprime n m) f x) =
      awayPrimeProductMap T m f (toAwayPrimeProduct G T m x) := rfl

theorem continuous_primeProductMap (f : G ⟶ H) : Continuous (primeProductMap T f) :=
  continuous_pi (fun p => (PrimeAdic.continuous_map T (p : ℕ) f).comp (continuous_apply p))

theorem continuous_awayPrimeProductMap (m : ℕ) (f : G ⟶ H) :
    Continuous (awayPrimeProductMap T m f) :=
  continuous_pi (fun p =>
    (PrimeAdic.continuous_map T (p.val : ℕ) f).comp (continuous_apply p))

@[simp] theorem primeProductMap_id :
    primeProductMap T (𝟙 G) = AddMonoidHom.id (PrimeProduct G T) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_id (G := G) T (p : ℕ)) (x p)

@[simp] theorem awayPrimeProductMap_id (m : ℕ) :
    awayPrimeProductMap T m (𝟙 G) = AddMonoidHom.id (AwayPrimeProduct G T m) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_id (G := G) T (p.val : ℕ)) (x p)

theorem primeProductMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    primeProductMap T (f ≫ g) = (primeProductMap T g).comp (primeProductMap T f) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_comp T (p : ℕ) f g) (x p)

theorem awayPrimeProductMap_comp (m : ℕ) (f : G ⟶ H) (g : H ⟶ K) :
    awayPrimeProductMap T m (f ≫ g) =
      (awayPrimeProductMap T m g).comp (awayPrimeProductMap T m f) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_comp T (p.val : ℕ) f g) (x p)

theorem primeProductMap_mul (f g : G ⟶ H) :
    primeProductMap T (f * g) = primeProductMap T f + primeProductMap T g := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_mul T (p : ℕ) f g) (x p)

theorem awayPrimeProductMap_mul (m : ℕ) (f g : G ⟶ H) :
    awayPrimeProductMap T m (f * g) =
      awayPrimeProductMap T m f + awayPrimeProductMap T m g := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (PrimeAdic.map_mul T (p.val : ℕ) f g) (x p)

theorem primeProductRestrict_map (m : ℕ) (f : G ⟶ H) (x : PrimeProduct G T) :
    primeProductRestrict H T m (primeProductMap T f x) =
      awayPrimeProductMap T m f (primeProductRestrict G T m x) := rfl

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- Product of actual prime-adic Tate modules of the bundled abelian scheme. -/
abbrev PrimeProduct := GroupScheme.Tate.PrimeComparison.PrimeProduct A.toGrp T

/-- Product over the primes retained by the away torsion system. -/
abbrev AwayPrimeProduct (m : ℕ) :=
  GroupScheme.Tate.PrimeComparison.AwayPrimeProduct A.toGrp T m

/-- Canonical full comparison on the actual abelian-scheme Tate carrier. -/
abbrev toPrimeProduct : Full A T →+ PrimeProduct A T :=
  GroupScheme.Tate.PrimeComparison.toPrimeProduct A.toGrp T

/-- Canonical away comparison on the actual abelian-scheme Tate carrier. -/
abbrev toAwayPrimeProduct (m : ℕ) : Away A T m →+ AwayPrimeProduct A T m :=
  GroupScheme.Tate.PrimeComparison.toAwayPrimeProduct A.toGrp T m

theorem continuous_toPrimeProduct : Continuous (toPrimeProduct A T) :=
  GroupScheme.Tate.PrimeComparison.continuous_toPrimeProduct A.toGrp T

theorem continuous_toAwayPrimeProduct (m : ℕ) : Continuous (toAwayPrimeProduct A T m) :=
  GroupScheme.Tate.PrimeComparison.continuous_toAwayPrimeProduct A.toGrp T m

variable {A} {B : AbelianScheme S}

/-- Product of the maps induced by the actual abelian-scheme homomorphism. -/
abbrev primeProductMap (f : A ⟶ B) : PrimeProduct A T →+ PrimeProduct B T :=
  GroupScheme.Tate.PrimeComparison.primeProductMap T (AbelianScheme.groupHom f)

/-- Product of the induced maps at the retained primes. -/
abbrev awayPrimeProductMap (m : ℕ) (f : A ⟶ B) :
    AwayPrimeProduct A T m →+ AwayPrimeProduct B T m :=
  GroupScheme.Tate.PrimeComparison.awayPrimeProductMap T m (AbelianScheme.groupHom f)

theorem toPrimeProduct_map (f : A ⟶ B) (x : Full A T) :
    toPrimeProduct B T (map T (fun _ => True) f x) =
      primeProductMap T f (toPrimeProduct A T x) := rfl

theorem toAwayPrimeProduct_map (m : ℕ) (f : A ⟶ B) (x : Away A T m) :
    toAwayPrimeProduct B T m (map T (fun n => Nat.Coprime n m) f x) =
      awayPrimeProductMap T m f (toAwayPrimeProduct A T m x) := rfl

theorem primeProductMap_add (f g : A ⟶ B) :
    primeProductMap T (f + g) = primeProductMap T f + primeProductMap T g :=
  GroupScheme.Tate.PrimeComparison.primeProductMap_mul T
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

theorem awayPrimeProductMap_add (m : ℕ) (f g : A ⟶ B) :
    awayPrimeProductMap T m (f + g) =
      awayPrimeProductMap T m f + awayPrimeProductMap T m g :=
  GroupScheme.Tate.PrimeComparison.awayPrimeProductMap_mul T m
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

end Langlands.AbelianScheme.Tate.PrimeComparison
