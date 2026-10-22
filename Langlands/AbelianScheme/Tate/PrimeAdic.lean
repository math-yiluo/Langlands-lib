import Langlands.AbelianScheme.Tate.Integral
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

lemma level_nsmul_eq_zero (n : ℕ) (x : Level G T n) : n • x = 0 := by
  apply toSection_injective G T n
  change (Additive.toMul x).val ^ n = 1
  exact (mem_levelGroup G T n _).mp (Additive.toMul x).property

instance levelZModModule (n : ℕ) : Module (ZMod n) (Level G T n) :=
  AddCommGroup.zmodModule (level_nsmul_eq_zero G T n)

lemma transition_zmod_smul {n m : ℕ} (h : n ∣ m) (a : ZMod m) (x : Level G T m) :
    transition G T h (a • x) = (ZMod.castHom h (ZMod n) a) • transition G T h x := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  simp only [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast]

namespace PrimeAdic
variable (p : ℕ) [Fact p.Prime]

instance levelModule (n : ℕ) : Module ℤ_[p] (Level G T (p ^ n)) :=
  Module.compHom (Level G T (p ^ n)) (PadicInt.toZModPow n)

lemma transition_smul {n m : ℕ} (h : n ≤ m) (a : ℤ_[p]) (x : Level G T (p ^ m)) :
    transition G T (pow_dvd_pow p h) (a • x) = a • transition G T (pow_dvd_pow p h) x := by
  change transition G T (pow_dvd_pow p h) (PadicInt.toZModPow m a • x) =
    PadicInt.toZModPow n a • transition G T (pow_dvd_pow p h) x
  rw [transition_zmod_smul]
  congr 1
  exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow n m h) a

/-- A successive transition is multiplication by the prime on underlying sections. -/
lemma toSection_transition_succ (n : ℕ) (x : Level G T (p ^ (n + 1))) :
    toSection G T (p ^ n) (transition G T (pow_dvd_pow p (Nat.le_succ n)) x) =
      p • toSection G T (p ^ (n + 1)) x := by
  change (Additive.toMul x).val ^ (p ^ (n + 1) / p ^ n) = (Additive.toMul x).val ^ p
  have h : p ^ (n + 1) / p ^ n = p := by
    rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos (Fact.out : p.Prime).pos n)]
  rw [h]

/-- Coherent sequences in the actual prime-power torsion groups. -/
def coherent : Submodule ℤ_[p] (∀ n : ℕ, Level G T (p ^ n)) where
  carrier := {x | ∀ n, transition G T (pow_dvd_pow p (Nat.le_succ n)) (x (n + 1)) = x n}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by
    intro x y hx hy n
    change transition G T _ (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro a x hx n
    change transition G T _ (a • x (n + 1)) = a • x n
    rw [transition_smul G T p (Nat.le_succ n), hx n]

/-- The prime-adic Tate module with its coordinatewise module structure. -/
def Integral : Type _ := ↥(coherent G T p)
instance : AddCommGroup (Integral G T p) := inferInstanceAs (AddCommGroup (coherent G T p))
instance : Module ℤ_[p] (Integral G T p) := inferInstanceAs (Module ℤ_[p] (coherent G T p))
instance : TopologicalSpace (Integral G T p) := inferInstanceAs (TopologicalSpace (coherent G T p))
instance : IsTopologicalAddGroup (Integral G T p) :=
  inferInstanceAs (IsTopologicalAddGroup (coherent G T p))

/-- Projection to actual prime-power torsion. -/
def evaluation (n : ℕ) : Integral G T p →ₗ[ℤ_[p]] Level G T (p ^ n) where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma evaluation_smul (n : ℕ) (a : ℤ_[p]) (x : Integral G T p) :
    evaluation G T p n (a • x) = PadicInt.toZModPow n a • evaluation G T p n x := rfl

lemma continuous_evaluation (n : ℕ) : Continuous (evaluation G T p n) :=
  (continuous_apply n).comp continuous_subtype_val

lemma evaluation_transition (n : ℕ) (x : Integral G T p) :
    transition G T (pow_dvd_pow p (Nat.le_succ n)) (evaluation G T p (n + 1) x) =
      evaluation G T p n x :=
  x.property n

/-- The universal linear map supplied by a compatible family of coordinates. -/
def lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level G T (p ^ n))
    (hf : ∀ n a, transition G T (pow_dvd_pow p (Nat.le_succ n)) (f (n + 1) a) = f n a) :
    A →ₗ[ℤ_[p]] Integral G T p where
  toFun a := ⟨fun n => f n a, fun n => hf n a⟩
  map_add' a b := by apply Subtype.ext; funext n; exact map_add (f n) a b
  map_smul' a b := by apply Subtype.ext; funext n; exact map_smul (f n) a b

@[simp]
lemma evaluation_lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level G T (p ^ n)) (hf) (n : ℕ) (a : A) :
    evaluation G T p n (lift G T p f hf a) = f n a := rfl

lemma lift_unique {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level G T (p ^ n)) (hf)
    (g : A →ₗ[ℤ_[p]] Integral G T p)
    (hg : ∀ n a, evaluation G T p n (g a) = f n a) : g = lift G T p f hf := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext n
  exact hg n a

lemma continuous_lift {A : Type*} [AddCommGroup A] [Module ℤ_[p] A] [TopologicalSpace A]
    (f : ∀ n : ℕ, A →ₗ[ℤ_[p]] Level G T (p ^ n)) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift G T p f hf) :=
  (continuous_pi hc).subtype_mk _

/-- Scalar extension to the actual field of p-adic numbers. -/
def Rational : Type _ := ℚ_[p] ⊗[ℤ_[p]] Integral G T p
instance : AddCommGroup (Rational G T p) := inferInstanceAs (AddCommGroup (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))
instance : Module ℚ_[p] (Rational G T p) := inferInstanceAs (Module ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Integral G T p))

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- The actual homomorphism on torsion points is linear for the residue scalar action. -/
def levelMapLinear (f : G ⟶ H) (n : ℕ) :
    Level G T (p ^ n) →ₗ[ℤ_[p]] Level H T (p ^ n) where
  toAddHom := levelMap T f (p ^ n)
  map_smul' a x := by
    change levelMap T f (p ^ n) (PadicInt.toZModPow n a • x) =
      PadicInt.toZModPow n a • levelMap T f (p ^ n) x
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (PadicInt.toZModPow n a)
    rw [← hb]
    simp only [Int.cast_smul_eq_zsmul, map_zsmul]

/-- The induced prime-adic linear map, defined coordinatewise. -/
def map (f : G ⟶ H) : Integral G T p →ₗ[ℤ_[p]] Integral H T p :=
  lift H T p (fun n => (levelMapLinear T p f n).comp (evaluation G T p n)) (by
    intro n x
    change transition H T _ (levelMap T f (p ^ (n + 1)) (x.val (n + 1))) =
      levelMap T f (p ^ n) (x.val n)
    rw [← levelMap_transition, x.property n])

@[simp]
lemma evaluation_map (f : G ⟶ H) (n : ℕ) (x : Integral G T p) :
    evaluation H T p n (map T p f x) =
      levelMap T f (p ^ n) (evaluation G T p n x) := rfl

@[simp]
lemma map_id : map T p (𝟙 G) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T (p ^ n)
  change (Additive.toMul (x.val n)).val ≫ 𝟙 G.X = _
  exact Category.comp_id _

lemma map_comp (f : G ⟶ H) (g : H ⟶ K) :
    map T p (f ≫ g) = (map T p g).comp (map T p f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective K T (p ^ n)
  change (Additive.toMul (x.val n)).val ≫ (f ≫ g).hom.hom = _
  exact (Category.assoc (Additive.toMul (x.val n)).val f.hom.hom g.hom.hom).symm

/-- Multiplication in the group-object Hom notation induces addition of linear maps. -/
lemma map_mul (f g : G ⟶ H) : map T p (f * g) = map T p f + map T p g := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective H T (p ^ n)
  change (Additive.toMul (x.val n)).val ≫ (f * g).hom.hom = _
  exact CategoryTheory.MonObj.comp_mul (Additive.toMul (x.val n)).val f.hom.hom g.hom.hom

lemma continuous_map (f : G ⟶ H) : Continuous (map T p f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelMap T f (p ^ n))).comp
    (continuous_evaluation G T p n)

/-- Scalar extension of the induced map to the p-adic rational Tate module. -/
def rationalMap (f : G ⟶ H) : Rational G T p →ₗ[ℚ_[p]] Rational H T p :=
  (map T p f).baseChange ℚ_[p]

@[simp]
lemma rationalMap_tmul (f : G ⟶ H) (a : ℚ_[p]) (x : Integral G T p) :
    rationalMap T p f (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] map T p f x :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
lemma rationalMap_id : rationalMap T p (𝟙 G) = LinearMap.id := by
  simp [rationalMap]
  rfl

lemma rationalMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    rationalMap T p (f ≫ g) = (rationalMap T p g).comp (rationalMap T p f) := by
  simp only [rationalMap, map_comp, LinearMap.baseChange_comp]
  rfl

lemma rationalMap_mul (f g : G ⟶ H) :
    rationalMap T p (f * g) = rationalMap T p f + rationalMap T p g := by
  simp only [rationalMap, map_mul, LinearMap.baseChange_add]
  rfl

variable (G)

/-- Integral prime-adic Tate module at an actual field-valued point. -/
abbrev IntegralAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Integral G (Over.mk s) p

/-- Rational prime-adic Tate module at an actual field-valued point. -/
abbrev RationalAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Rational G (Over.mk s) p

end PrimeAdic
end Langlands.GroupScheme.Tate
