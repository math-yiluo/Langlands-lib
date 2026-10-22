import Langlands.AbelianScheme.Tate.Twist
import Langlands.AbelianScheme.Tate.Scalars

noncomputable section

namespace Langlands.TateTwist.Divisibility
universe u v w
open Langlands.GroupScheme.Tate (Index)
variable (R : Type u) [CommRing R]

/-- Coherent families form a subgroup of the product of the roots-of-unity levels. -/
def coherent (P : ℕ → Prop) : AddSubgroup (∀ n : Index P, Level R n.val) where
  carrier := {x | ∀ (n m : Index P) (h : n.val ∣ m.val), transition R h (x m) = x n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro x y hx hy n m h
    change transition R h (x m + y m) = x n + y n
    rw [map_add, hx n m h, hy n m h]
  neg_mem' := by
    intro x hx n m h
    change transition R h (-x m) = -x n
    rw [map_neg, hx n m h]

/-- The inverse limit, with its coordinatewise group structure and product-subspace topology. -/
def Integral (P : ℕ → Prop) : Type _ := ↥(coherent R P)

instance (P : ℕ → Prop) : AddCommGroup (Integral R P) :=
  inferInstanceAs (AddCommGroup (coherent R P))
instance (P : ℕ → Prop) : TopologicalSpace (Integral R P) :=
  inferInstanceAs (TopologicalSpace (coherent R P))
instance (P : ℕ → Prop) : IsTopologicalAddGroup (Integral R P) :=
  inferInstanceAs (IsTopologicalAddGroup (coherent R P))

/-- The full integral Tate twist. -/
abbrev Full := Integral R (fun _ => True)
/-- The prime-to-`p` integral Tate twist; the definition works for any natural `p`. -/
abbrev Away (p : ℕ) := Integral R (fun n => Nat.Coprime n p)

/-- Projection to a roots-of-unity level. -/
def evaluation (P : ℕ → Prop) (n : Index P) : Integral R P →+ Level R n.val where
  toFun := fun x => x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma continuous_evaluation (P : ℕ → Prop) (n : Index P) :
    Continuous (evaluation R P n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Compatibility of the universal projections. -/
lemma evaluation_transition (P : ℕ → Prop) (n m : Index P) (h : n.val ∣ m.val)
    (x : Integral R P) :
    transition R h (evaluation R P m x) = evaluation R P n x :=
  x.property n m h

/-- A compatible family of homomorphisms gives a unique homomorphism into the limit. -/
def lift (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level R n.val)
    (hf : ∀ (n m : Index P) (h : n.val ∣ m.val) (a : A),
      transition R h (f m a) = f n a) : A →+ Integral R P where
  toFun a := ⟨fun n => f n a, fun n m h => hf n m h a⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero (f n)
  map_add' a b := by apply Subtype.ext; funext n; exact map_add (f n) a b

@[simp]
lemma evaluation_lift (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level R n.val) (hf) (n : Index P) (a : A) :
    evaluation R P n (lift R P f hf a) = f n a := rfl

lemma lift_unique (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level R n.val) (hf)
    (g : A →+ Integral R P)
    (hg : ∀ n a, evaluation R P n (g a) = f n a) : g = lift R P f hf := by
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  funext n
  exact hg n a

/-- The universal lift is continuous when its coordinates are continuous. -/
lemma continuous_lift (P : ℕ → Prop) {A : Type*} [AddGroup A] [TopologicalSpace A]
    (f : ∀ n : Index P, A →+ Level R n.val) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift R P f hf) :=
  (continuous_pi hc).subtype_mk _

/-- Restriction of a full coherent family to the levels prime to `p`. -/
def restrictAway (p : ℕ) : Full R →+ Away R p :=
  lift R (fun n => Nat.Coprime n p)
    (fun n => evaluation R (fun _ => True) ⟨n.val, n.property.1, trivial⟩)
    (fun n m h x => x.property ⟨n.val, n.property.1, trivial⟩
      ⟨m.val, m.property.1, trivial⟩ h)

lemma continuous_restrictAway (p : ℕ) : Continuous (restrictAway R p) :=
  continuous_lift R _ _ _ (fun _ => continuous_evaluation R _ _)

namespace ScalarAction
variable (P : ℕ → Prop) {A : Type*} [CommRing A]
variable (r : ∀ n : Index P, A →+* ZMod n.val)
variable (hr : ∀ n m (h : n.val ∣ m.val),
  (ZMod.castHom h (ZMod n.val)).comp (r m) = r n)

/-- Compatible residue scalars act on the existing coherent-family limit. -/
@[instance_reducible] def module : Module A (Integral R P) where
  smul a x := ⟨fun n => r n a • x.val n, by
    intro n m h
    rw [transition_zmod_smul, x.property n m h]
    exact congrArg (fun b => b • x.val n) (DFunLike.congr_fun (hr n m h) a)⟩
  one_smul x := by
    apply Subtype.ext; funext n
    change r n 1 • x.val n = x.val n
    rw [map_one, one_smul]
  mul_smul a b x := by
    apply Subtype.ext; funext n
    change r n (a * b) • x.val n = r n a • (r n b • x.val n)
    rw [_root_.map_mul, mul_smul]
  smul_zero a := by apply Subtype.ext; funext n; exact smul_zero _
  smul_add a x y := by apply Subtype.ext; funext n; exact smul_add _ _ _
  add_smul a b x := by
    apply Subtype.ext; funext n
    change r n (a + b) • x.val n = r n a • x.val n + r n b • x.val n
    rw [map_add, add_smul]
  zero_smul x := by
    apply Subtype.ext; funext n
    change r n 0 • x.val n = 0
    rw [map_zero, zero_smul]

variable {P r hr}

/-- Continuity is inherited from continuous residue maps and discrete roots-of-unity levels. -/
theorem continuous_smul [TopologicalSpace A] (hc : ∀ n, Continuous (r n)) :
    let := module R P r hr
    Continuous (fun z : A × Integral R P => z.1 • z.2) := by
  let := module R P r hr
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology
    (f := fun z : ZMod n.val × Level R n.val => z.1 • z.2)).comp
      (((hc n).comp continuous_fst).prodMk
        ((continuous_evaluation R P n).comp continuous_snd))

end ScalarAction

open Langlands.GroupScheme.Tate (fullReduction fullReduction_compatible
  awayReduction awayReduction_compatible)

/-- Every selected roots-of-unity limit is a module over the full profinite-integer ring. -/
instance fullModule (P : ℕ → Prop) : Module Global.ProfiniteIntegerRing (Integral R P) :=
  ScalarAction.module R P (fullReduction P) (fullReduction_compatible P)

@[simp] theorem evaluation_full_smul (P : ℕ → Prop) (n : Index P)
    (a : Global.ProfiniteIntegerRing) (x : Integral R P) :
    evaluation R P n (a • x) = fullReduction P n a • evaluation R P n x := rfl

instance fullContinuousSMul (P : ℕ → Prop) :
    ContinuousSMul Global.ProfiniteIntegerRing (Integral R P) :=
  ⟨ScalarAction.continuous_smul R (r := fullReduction P)
    (hr := fullReduction_compatible P) (fun _ => Global.ResidueLimit.continuous_reduction _)⟩

instance awayModule (p : ℕ) : Module (Global.PrimeToProfiniteIntegerRing p) (Away R p) :=
  ScalarAction.module R _ (awayReduction p) (awayReduction_compatible p)

@[simp] theorem evaluation_away_smul (p : ℕ) (n : Index (fun n => Nat.Coprime n p))
    (a : Global.PrimeToProfiniteIntegerRing p) (x : Away R p) :
    evaluation R _ n (a • x) = awayReduction p n a • evaluation R _ n x := rfl

instance awayContinuousSMul (p : ℕ) :
    ContinuousSMul (Global.PrimeToProfiniteIntegerRing p) (Away R p) :=
  ⟨ScalarAction.continuous_smul R (r := awayReduction p)
    (hr := awayReduction_compatible p) (fun _ => Global.ResidueLimit.continuous_reduction _)⟩

/-- Integer scalars have their usual additive meaning. -/
theorem full_intCast_smul (P : ℕ → Prop) (z : ℤ) (x : Integral R P) :
    (z : Global.ProfiniteIntegerRing) • x = z • x := by
  apply Subtype.ext
  funext n
  change fullReduction P n (z : Global.ProfiniteIntegerRing) • x.val n = z • x.val n
  rw [map_intCast, Int.cast_smul_eq_zsmul]

theorem away_intCast_smul (p : ℕ) (z : ℤ) (x : Away R p) :
    (z : Global.PrimeToProfiniteIntegerRing p) • x = z • x := by
  apply Subtype.ext
  funext n
  change awayReduction p n (z : Global.PrimeToProfiniteIntegerRing p) • x.val n = z • x.val n
  rw [map_intCast, Int.cast_smul_eq_zsmul]

/-- Restriction uses the corresponding restriction of the scalar ring. -/
theorem restrictAway_smul (p : ℕ) (a : Global.ProfiniteIntegerRing) (x : Full R) :
    restrictAway R p (a • x) = Global.PrimeToProfiniteIntegerRing.restrict p a •
      restrictAway R p x := rfl

/-- The full-ring action on an away limit agrees with its restricted scalar action. -/
theorem full_smul_eq_away_smul (p : ℕ) (a : Global.ProfiniteIntegerRing) (x : Away R p) :
    a • x = Global.PrimeToProfiniteIntegerRing.restrict p a • x := rfl


variable {R} {S : Type v} {T : Type w} [CommRing S] [CommRing T]

/-- A ring map acts on every coordinate of the roots-of-unity inverse limit. -/
def map (P : ℕ → Prop) (f : R →+* S) : Integral R P →+ Integral S P :=
  lift S P (fun n => (levelMap f n.val).comp (evaluation R P n)) (by
    intro n m h x
    change transition S h (levelMap f m.val (x.val m)) = levelMap f n.val (x.val n)
    rw [← levelMap_transition, x.property n m h])

@[simp] lemma evaluation_map (P : ℕ → Prop) (f : R →+* S) (n : Index P)
    (x : Integral R P) :
    evaluation S P n (map P f x) = levelMap f n.val (evaluation R P n x) := rfl

@[simp] lemma map_id (P : ℕ → Prop) :
    map P (RingHom.id R) = AddMonoidHom.id (Integral R P) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toUnit_injective R n.val
  rfl

lemma map_comp (P : ℕ → Prop) (f : R →+* S) (g : S →+* T) :
    map P (g.comp f) = (map P g).comp (map P f) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toUnit_injective T n.val
  rfl

lemma continuous_map (P : ℕ → Prop) (f : R →+* S) : Continuous (map P f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelMap f n.val)).comp
    (continuous_evaluation R P n)

/-- The map on twists is linear over the full profinite-integer ring. -/
def fullLinearMap (P : ℕ → Prop) (f : R →+* S) :
    Integral R P →ₗ[Global.ProfiniteIntegerRing] Integral S P where
  toAddHom := map P f
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (levelMap f n.val) (fullReduction P n a) (x.val n)

/-- The map on away twists is linear over the prime-to-p scalar ring. -/
def awayLinearMap (p : ℕ) (f : R →+* S) :
    Away R p →ₗ[Global.PrimeToProfiniteIntegerRing p] Away S p where
  toAddHom := map (fun n => Nat.Coprime n p) f
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (levelMap f n.val) (awayReduction p n a) (x.val n)

lemma restrictAway_map (p : ℕ) (f : R →+* S) (x : Full R) :
    restrictAway S p (map (fun _ => True) f x) =
      map (fun n => Nat.Coprime n p) f (restrictAway R p x) := rfl

end Langlands.TateTwist.Divisibility

namespace Langlands.TateTwist

/-- The full integral roots-of-unity Tate twist. -/
abbrev Full (R : Type*) [CommRing R] := Divisibility.Full R

/-- The prime-to-p integral roots-of-unity Tate twist. -/
abbrev Away (R : Type*) [CommRing R] (p : ℕ) := Divisibility.Away R p

end Langlands.TateTwist
