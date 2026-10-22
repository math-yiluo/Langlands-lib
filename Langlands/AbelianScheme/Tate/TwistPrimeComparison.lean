import Langlands.AbelianScheme.Tate.TwistDivisibility

noncomputable section

namespace Langlands.TateTwist.Divisibility
universe u v
variable (R : Type u) [CommRing R] (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]

/-- The selected positive index corresponding to a prime power. -/
def primePowerIndex (hP : ∀ n : ℕ, P (p ^ n)) (n : ℕ) : GroupScheme.Tate.Index P :=
  ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, hP n⟩

/-- Read the prime-power coordinates of an actual roots-of-unity limit. -/
def toPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Integral R P →+ TateTwist.Integral R p where
  toFun x := ⟨fun n => x.val (primePowerIndex P p hP n), by
    intro n
    exact x.property (primePowerIndex P p hP n) (primePowerIndex P p hP (n + 1))
      (pow_dvd_pow p (Nat.le_succ n))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma evaluation_toPrime (hP : ∀ n : ℕ, P (p ^ n))
    (n : ℕ) (x : Integral R P) :
    TateTwist.evaluation R p n (toPrime R P p hP x) =
      evaluation R P (primePowerIndex P p hP n) x := rfl

lemma continuous_toPrime (hP : ∀ n : ℕ, P (p ^ n)) :
    Continuous (toPrime R P p hP) :=
  (continuous_pi (fun n => continuous_evaluation R P (primePowerIndex P p hP n))).subtype_mk _

/-- Extract a prime-adic twist from the full root limit. -/
def fullToPrime : Full R →+ TateTwist.Integral R p :=
  toPrime R (fun _ => True) p (fun _ => trivial)

/-- Extract a prime-adic twist when the prime is coprime to the excluded modulus. -/
def awayToPrime (m : ℕ) (h : Nat.Coprime p m) : Away R m →+ TateTwist.Integral R p :=
  toPrime R (fun n => Nat.Coprime n m) p (fun n => h.pow_left n)

lemma continuous_fullToPrime : Continuous (fullToPrime R p) :=
  continuous_toPrime R _ p _

lemma continuous_awayToPrime (m : ℕ) (h : Nat.Coprime p m) :
    Continuous (awayToPrime R p m h) := continuous_toPrime R _ p _

lemma awayToPrime_restrictAway (m : ℕ) (h : Nat.Coprime p m) (x : Full R) :
    awayToPrime R p m h (restrictAway R m x) = fullToPrime R p x := rfl

variable {R} {S : Type v} [CommRing S]

lemma toPrime_map (hP : ∀ n : ℕ, P (p ^ n)) (f : R →+* S) (x : Integral R P) :
    toPrime S P p hP (map P f x) = TateTwist.map p f (toPrime R P p hP x) := rfl

variable (R)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

/-- The product of the actual integral twists over all primes. -/
abbrev PrimeProduct := ∀ p : Nat.Primes, TateTwist.Integral R (p : ℕ)

/-- Primes retained by the away-from-`m` divisibility system. -/
abbrev AwayPrime (m : ℕ) := {p : Nat.Primes // Nat.Coprime (p : ℕ) m}

/-- The product of the prime-adic twists at primes coprime to `m`. -/
abbrev AwayPrimeProduct (m : ℕ) :=
  ∀ p : AwayPrime m, TateTwist.Integral R (p.val : ℕ)

/-- The canonical map to the product of prime-power coordinate limits. -/
def toPrimeProduct : Full R →+ PrimeProduct R where
  toFun x p := fullToPrime R (p : ℕ) x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical away comparison map uses the same prime-power coordinates. -/
def toAwayPrimeProduct (m : ℕ) : Away R m →+ AwayPrimeProduct R m where
  toFun x p := awayToPrime R (p.val : ℕ) m p.property x
  map_zero' := rfl
  map_add' _ _ := rfl

lemma continuous_toPrimeProduct : Continuous (toPrimeProduct R) :=
  continuous_pi (fun p => continuous_fullToPrime R (p : ℕ))

lemma continuous_toAwayPrimeProduct (m : ℕ) : Continuous (toAwayPrimeProduct R m) :=
  continuous_pi (fun p => continuous_awayToPrime R (p.val : ℕ) m p.property)

/-- Forget the prime components not coprime to `m`. -/
def primeProductRestrict (m : ℕ) : PrimeProduct R →+ AwayPrimeProduct R m where
  toFun x p := x p.val
  map_zero' := rfl
  map_add' _ _ := rfl

lemma continuous_primeProductRestrict (m : ℕ) : Continuous (primeProductRestrict R m) :=
  continuous_pi (fun p => continuous_apply p.val)

lemma toPrimeProduct_restrictAway (m : ℕ) (x : Full R) :
    toAwayPrimeProduct R m (restrictAway R m x) =
      primeProductRestrict R m (toPrimeProduct R x) := rfl

variable {R}

/-- The product of the actual prime-adic maps induced by a ring homomorphism. -/
def primeProductMap (f : R →+* S) : PrimeProduct R →+ PrimeProduct S where
  toFun x p := TateTwist.map (p : ℕ) f (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

/-- The corresponding product map over the retained away primes. -/
def awayPrimeProductMap (m : ℕ) (f : R →+* S) :
    AwayPrimeProduct R m →+ AwayPrimeProduct S m where
  toFun x p := TateTwist.map (p.val : ℕ) f (x p)
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

lemma toPrimeProduct_map (f : R →+* S) (x : Full R) :
    toPrimeProduct S (map (fun _ => True) f x) =
      primeProductMap f (toPrimeProduct R x) := rfl

lemma toAwayPrimeProduct_map (m : ℕ) (f : R →+* S) (x : Away R m) :
    toAwayPrimeProduct S m (map (fun n => Nat.Coprime n m) f x) =
      awayPrimeProductMap m f (toAwayPrimeProduct R m x) := rfl

lemma continuous_primeProductMap (f : R →+* S) : Continuous (primeProductMap f) :=
  continuous_pi (fun p => (TateTwist.continuous_map (p : ℕ) f).comp (continuous_apply p))

lemma continuous_awayPrimeProductMap (m : ℕ) (f : R →+* S) :
    Continuous (awayPrimeProductMap m f) :=
  continuous_pi (fun p =>
    (TateTwist.continuous_map (p.val : ℕ) f).comp (continuous_apply p))

@[simp] lemma primeProductMap_id :
    primeProductMap (RingHom.id R) = AddMonoidHom.id (PrimeProduct R) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (TateTwist.map_id (R := R) (p : ℕ)) (x p)

@[simp] lemma awayPrimeProductMap_id (m : ℕ) :
    awayPrimeProductMap m (RingHom.id R) = AddMonoidHom.id (AwayPrimeProduct R m) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (TateTwist.map_id (R := R) (p.val : ℕ)) (x p)

variable {T : Type*} [CommRing T]

lemma primeProductMap_comp (f : R →+* S) (g : S →+* T) :
    primeProductMap (g.comp f) = (primeProductMap g).comp (primeProductMap f) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (TateTwist.map_comp (p : ℕ) f g) (x p)

lemma awayPrimeProductMap_comp (m : ℕ) (f : R →+* S) (g : S →+* T) :
    awayPrimeProductMap m (g.comp f) =
      (awayPrimeProductMap m g).comp (awayPrimeProductMap m f) := by
  apply AddMonoidHom.ext
  intro x
  funext p
  exact LinearMap.congr_fun (TateTwist.map_comp (p.val : ℕ) f g) (x p)

lemma primeProductRestrict_map (m : ℕ) (f : R →+* S) (x : PrimeProduct R) :
    primeProductRestrict S m (primeProductMap f x) =
      awayPrimeProductMap m f (primeProductRestrict R m x) := rfl

end Langlands.TateTwist.Divisibility
