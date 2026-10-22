import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

set_option maxHeartbeats 800000
noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist
universe u v w
variable (R : Type u) [CommRing R]

/-- Actual roots of unity, written additively for the module interface. -/
abbrev Level (n : ℕ) := Additive (rootsOfUnity n R)

def toUnit (n : ℕ) : Level R n →+ Additive Rˣ :=
  (rootsOfUnity n R).subtype.toAdditive

lemma toUnit_injective (n : ℕ) : Function.Injective (toUnit R n) :=
  fun _ _ h => Subtype.ext h

lemma level_nsmul_eq_zero (n : ℕ) (x : Level R n) : n • x = 0 := by
  apply toUnit_injective R n
  change (Additive.toMul x).val ^ n = 1
  exact (Additive.toMul x).property

instance levelZModModule (n : ℕ) : Module (ZMod n) (Level R n) :=
  AddCommGroup.zmodModule (level_nsmul_eq_zero R n)

lemma toUnit_zmod_smul (n : ℕ) [NeZero n] (a : ZMod n) (x : Level R n) :
    toUnit R n (a • x) = a.val • toUnit R n x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
  exact map_nsmul _ _ _

/-- The discrete topology on a torsion level. -/
instance (n : ℕ) : TopologicalSpace (Level R n) := ⊥
instance (n : ℕ) : DiscreteTopology (Level R n) := ⟨rfl⟩

/-- The transition for divisibility is the indicated power of an actual unit. -/
def transition {n m : ℕ} (h : n ∣ m) : Level R m →+ Level R n :=
  MonoidHom.toAdditive {
    toFun := fun x => ⟨x.val ^ (m / n), by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel h]
      exact x.property⟩
    map_one' := by apply Subtype.ext; exact one_pow _
    map_mul' := fun x y => by apply Subtype.ext; exact mul_pow _ _ _ }

@[simp]
lemma transition_self {n : ℕ} (hn : 0 < n) (x : Level R n) :
    transition R (dvd_refl n) x = x := by
  apply toUnit_injective R n
  change (Additive.toMul x).val ^ (n / n) = (Additive.toMul x).val
  rw [Nat.div_self hn, pow_one]

lemma transition_comp {n m k : ℕ} (hnm : n ∣ m) (hmk : m ∣ k) (x : Level R k) :
    transition R hnm (transition R hmk x) = transition R (dvd_trans hnm hmk) x := by
  apply toUnit_injective R n
  change ((Additive.toMul x).val ^ (k / m)) ^ (m / n) = _
  rw [← pow_mul, Nat.div_mul_div hmk hnm]
  rfl

lemma transition_zmod_smul {n m : ℕ} (h : n ∣ m) (a : ZMod m) (x : Level R m) :
    transition R h (a • x) = (ZMod.castHom h (ZMod n) a) • transition R h x := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast]

variable (p : ℕ) [Fact p.Prime]

instance levelModule (n : ℕ) : Module ℤ_[p] (Level R (p ^ n)) :=
  Module.compHom (Level R (p ^ n)) (PadicInt.toZModPow n)

lemma transition_smul {n m : ℕ} (h : n ≤ m) (a : ℤ_[p]) (x : Level R (p ^ m)) :
    transition R (pow_dvd_pow p h) (a • x) =
      a • transition R (pow_dvd_pow p h) x := by
  change transition R (pow_dvd_pow p h) (PadicInt.toZModPow m a • x) =
    PadicInt.toZModPow n a • transition R (pow_dvd_pow p h) x
  rw [transition_zmod_smul]
  congr 1
  exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow n m h) a

lemma toUnit_transition_succ (n : ℕ) (x : Level R (p ^ (n + 1))) :
    toUnit R (p ^ n) (transition R (pow_dvd_pow p (Nat.le_succ n)) x) =
      p • toUnit R (p ^ (n + 1)) x := by
  change (Additive.toMul x).val ^ (p ^ (n + 1) / p ^ n) = (Additive.toMul x).val ^ p
  have h : p ^ (n + 1) / p ^ n = p := by
    rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos (Fact.out : p.Prime).pos n)]
  rw [h]

/-- Coherent sequences of actual prime-power roots of unity. -/
def coherent : Submodule ℤ_[p] (∀ n : ℕ, Level R (p ^ n)) where
  carrier := {x | ∀ n, transition R (pow_dvd_pow p (Nat.le_succ n)) (x (n + 1)) = x n}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by
    intro x y hx hy n
    change transition R _ (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro a x hx n
    change transition R _ (a • x (n + 1)) = a • x n
    rw [transition_smul R p (Nat.le_succ n), hx n]

/-- The integral Tate twist, without a choice of compatible primitive roots. -/
def Integral : Type u := ↥(coherent R p)
instance : AddCommGroup (Integral R p) := inferInstanceAs (AddCommGroup (coherent R p))
instance : Module ℤ_[p] (Integral R p) := inferInstanceAs (Module ℤ_[p] (coherent R p))
instance : TopologicalSpace (Integral R p) := inferInstanceAs (TopologicalSpace (coherent R p))
instance : IsTopologicalAddGroup (Integral R p) :=
  inferInstanceAs (IsTopologicalAddGroup (coherent R p))

def evaluation (n : ℕ) : Integral R p →ₗ[ℤ_[p]] Level R (p ^ n) where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma evaluation_smul (n : ℕ) (a : ℤ_[p]) (x : Integral R p) :
    evaluation R p n (a • x) = PadicInt.toZModPow n a • evaluation R p n x := rfl

lemma continuous_evaluation (n : ℕ) : Continuous (evaluation R p n) :=
  (continuous_apply n).comp continuous_subtype_val

lemma evaluation_transition (n : ℕ) (x : Integral R p) :
    transition R (pow_dvd_pow p (Nat.le_succ n)) (evaluation R p (n + 1) x) =
      evaluation R p n x := x.property n

/-- Universal linear lift of compatible coordinates. -/
def lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level R (p ^ n))
    (hf : ∀ n a, transition R (pow_dvd_pow p (Nat.le_succ n)) (f (n + 1) a) = f n a) :
    A →ₗ[ℤ_[p]] Integral R p where
  toFun a := ⟨fun n => f n a, fun n => hf n a⟩
  map_add' a b := by apply Subtype.ext; funext n; exact map_add (f n) a b
  map_smul' a b := by apply Subtype.ext; funext n; exact map_smul (f n) a b

@[simp]
lemma evaluation_lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level R (p ^ n)) (hf) (n : ℕ) (a : A) :
    evaluation R p n (lift R p f hf a) = f n a := rfl

lemma lift_unique {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level R (p ^ n)) (hf)
    (g : A →ₗ[ℤ_[p]] Integral R p)
    (hg : ∀ n a, evaluation R p n (g a) = f n a) : g = lift R p f hf := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext n
  exact hg n a

lemma continuous_lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A] [TopologicalSpace A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level R (p ^ n)) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift R p f hf) :=
  (continuous_pi hc).subtype_mk _

/-- Rationalization of the actual inverse limit. -/
def Rational : Type _ := ℚ_[p] ⊗[ℤ_[p]] Integral R p
instance : AddCommGroup (Rational R p) := inferInstanceAs (AddCommGroup (ℚ_[p] ⊗[ℤ_[p]] Integral R p))
instance : Module ℚ_[p] (Rational R p) := inferInstanceAs (Module ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral R p))

variable {R} {S : Type v} {T : Type w} [CommRing S] [CommRing T]

/-- A ring map acts on actual roots of unity. -/
def levelMap (f : R →+* S) (n : ℕ) : Level R n →+ Level S n :=
  (restrictRootsOfUnity f n).toAdditive

lemma levelMap_transition (f : R →+* S) {n m : ℕ} (h : n ∣ m) (x : Level R m) :
    levelMap f n (transition R h x) = transition S h (levelMap f m x) := by
  apply toUnit_injective S n
  change Units.map f.toMonoidHom ((Additive.toMul x).val ^ (m / n)) =
    (Units.map f.toMonoidHom (Additive.toMul x).val) ^ (m / n)
  exact map_pow _ _ _

def levelMapLinear (f : R →+* S) (n : ℕ) :
    Level R (p ^ n) →ₗ[ℤ_[p]] Level S (p ^ n) where
  toAddHom := levelMap f (p ^ n)
  map_smul' a x := ZMod.map_smul (levelMap f (p ^ n)) (PadicInt.toZModPow n a) x

/-- The functorial map on the inverse limits. -/
def map (f : R →+* S) : Integral R p →ₗ[ℤ_[p]] Integral S p :=
  lift S p (fun n => (levelMapLinear p f n).comp (evaluation R p n)) (by
    intro n x
    change transition S _ (levelMap f (p ^ (n + 1)) (x.val (n + 1))) =
      levelMap f (p ^ n) (x.val n)
    rw [← levelMap_transition, x.property n])

@[simp]
lemma evaluation_map (f : R →+* S) (n : ℕ) (x : Integral R p) :
    evaluation S p n (map p f x) = levelMap f (p ^ n) (evaluation R p n x) := rfl

@[simp]
lemma map_id : map p (RingHom.id R) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toUnit_injective R (p ^ n)
  rfl

lemma map_comp (f : R →+* S) (g : S →+* T) :
    map p (g.comp f) = (map p g).comp (map p f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toUnit_injective T (p ^ n)
  rfl

lemma continuous_map (f : R →+* S) : Continuous (map p f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelMap f (p ^ n))).comp
    (continuous_evaluation R p n)

def rationalMap (f : R →+* S) : Rational R p →ₗ[ℚ_[p]] Rational S p :=
  (map p f).baseChange ℚ_[p]

@[simp]
lemma rationalMap_tmul (f : R →+* S) (a : ℚ_[p]) (x : Integral R p) :
    rationalMap p f (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] map p f x :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
lemma rationalMap_id : rationalMap p (RingHom.id R) = LinearMap.id := by
  simp [rationalMap]
  rfl

lemma rationalMap_comp (f : R →+* S) (g : S →+* T) :
    rationalMap p (g.comp f) = (rationalMap p g).comp (rationalMap p f) := by
  simp only [rationalMap, map_comp, LinearMap.baseChange_comp]
  rfl

/-- An actual ring isomorphism gives a linear isomorphism of twists. -/
def mapEquiv (f : R ≃+* S) : Integral R p ≃ₗ[ℤ_[p]] Integral S p where
  toLinearMap := map p f.toRingHom
  invFun := map p f.symm.toRingHom
  left_inv x := by
    change ((map p f.symm.toRingHom).comp (map p f.toRingHom)) x = x
    rw [← map_comp]
    rw [RingEquiv.symm_toRingHom_comp_toRingHom, map_id]; rfl
  right_inv x := by
    change ((map p f.toRingHom).comp (map p f.symm.toRingHom)) x = x
    rw [← map_comp]
    rw [RingEquiv.toRingHom_comp_symm_toRingHom, map_id]; rfl

variable (R)

/-- The natural automorphism action retains the action on every root of unity. -/
def automorphismAction : (R ≃+* R) →* (Integral R p ≃ₗ[ℤ_[p]] Integral R p) where
  toFun := mapEquiv p
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact map_id p
  map_mul' f g := by
    apply LinearEquiv.toLinearMap_injective
    exact map_comp p g.toRingHom f.toRingHom

def rationalAutomorphismAction : (R ≃+* R) →* (Rational R p ≃ₗ[ℚ_[p]] Rational R p) where
  toFun f := (automorphismAction R p f).baseChange ℤ_[p] ℚ_[p] _ _
  map_one' := by rw [map_one, LinearEquiv.baseChange_one]; rfl
  map_mul' f g := by rw [map_mul, LinearEquiv.baseChange_mul]; rfl

@[simp]
lemma rationalAutomorphismAction_tmul (f : R ≃+* R) (a : ℚ_[p]) (x : Integral R p) :
    rationalAutomorphismAction R p f (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] automorphismAction R p f x := rfl

lemma continuous_automorphismAction (f : R ≃+* R) :
    Continuous (automorphismAction R p f) := continuous_map p f.toRingHom

/-- The natural action agrees with the cyclotomic character when all the
required primitive roots exist. No basis of the twist is chosen. -/
lemma automorphismAction_eq_cyclotomic_smul [IsDomain R]
    [∀ n, HasEnoughRootsOfUnity R (p ^ n)] (f : R ≃+* R) (x : Integral R p) :
    automorphismAction R p f x = (cyclotomicCharacter R p f).val • x := by
  apply Subtype.ext
  funext n
  apply toUnit_injective R (p ^ n)
  change toUnit R (p ^ n) (levelMap f.toRingHom (p ^ n) (x.val n)) =
    toUnit R (p ^ n) ((PadicInt.toZModPow n (cyclotomicCharacter R p f).val) • x.val n)
  rw [toUnit_zmod_smul]
  change Units.map f.toMonoidHom (Additive.toMul (x.val n)).val =
    (Additive.toMul (x.val n)).val ^ ((cyclotomicCharacter R p f).val.toZModPow n).val
  apply Units.ext
  exact cyclotomicCharacter.spec p f _ ((mem_rootsOfUnity' _ _).mp (x.val n).property)

section Galois
variable (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual field automorphism action on the integral twist. -/
def galoisAction : Gal(L/K) →* (Integral L p ≃ₗ[ℤ_[p]] Integral L p) :=
  (automorphismAction L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)

/-- The actual field automorphism action after rationalization. -/
def rationalGaloisAction : Gal(L/K) →* (Rational L p ≃ₗ[ℚ_[p]] Rational L p) :=
  (rationalAutomorphismAction L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)

end Galois
end Langlands.TateTwist
