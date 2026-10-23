import Langlands.AbelianScheme.Torsion
import Langlands.AbelianScheme.Tate.Scalars
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
variable {T T' T'' : Over S}

/-- Restriction of actual torsion points in additive notation. -/
def levelRestrict (a : T' ⟶ T) (n : ℕ) : Level G T n →+ Level G T' n :=
  (torsionPointsRestrict G (n : ℤ) a).toAdditive

@[simp] theorem toSection_levelRestrict (a : T' ⟶ T) (n : ℕ) (x : Level G T n) :
    Additive.toMul (toSection G T' n (levelRestrict G a n x)) =
      a ≫ Additive.toMul (toSection G T n x) := rfl

/-- Restriction agrees with precomposition on actual torsion-kernel sections. -/
theorem levelRestrict_kernelLevelEquiv (a : T' ⟶ T) (n : ℕ)
    (x : Additive (T ⟶ (kernel (multiplication G n)).X)) :
    levelRestrict G a n (kernelLevelEquiv G T n x) =
      kernelLevelEquiv G T' n (Additive.ofMul (a ≫ Additive.toMul x)) := by
  apply toSection_injective G T' n
  exact (Category.assoc a (Additive.toMul x) (kernelι (multiplication G n)).hom.hom).symm

/-- Precomposition commutes with the quotient-power transition. -/
theorem levelRestrict_transition (a : T' ⟶ T) {n m : ℕ} (h : n ∣ m)
    (x : Level G T m) :
    levelRestrict G a n (transition G T h x) =
      transition G T' h (levelRestrict G a m x) := by
  apply toSection_injective G T' n
  exact CategoryTheory.MonObj.comp_pow (Additive.toMul x).val (m / n) a

/-- Contravariant restriction on the selected actual Tate limit. -/
def testRestrict (P : ℕ → Prop) (a : T' ⟶ T) : Integral G T P →+ Integral G T' P :=
  lift G T' P (fun n => (levelRestrict G a n.val).comp (evaluation G T P n)) (by
    intro n m h x
    change transition G T' h (levelRestrict G a m.val (x.val m)) =
      levelRestrict G a n.val (x.val n)
    rw [← levelRestrict_transition, x.property n m h])

@[simp] theorem evaluation_testRestrict (P : ℕ → Prop) (a : T' ⟶ T)
    (n : Index P) (x : Integral G T P) :
    evaluation G T' P n (testRestrict G P a x) =
      levelRestrict G a n.val (evaluation G T P n x) := rfl

@[simp] theorem testRestrict_id (P : ℕ → Prop) :
    testRestrict G P (𝟙 T) = AddMonoidHom.id (Integral G T P) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T n.val
  exact Category.id_comp (Additive.toMul (x.val n)).val

/-- The order is contravariant in the test scheme. -/
theorem testRestrict_comp (P : ℕ → Prop) (a : T' ⟶ T) (b : T'' ⟶ T') :
    testRestrict G P (b ≫ a) = (testRestrict G P b).comp (testRestrict G P a) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T'' n.val
  exact Category.assoc b a (Additive.toMul (x.val n)).val

theorem continuous_testRestrict (P : ℕ → Prop) (a : T' ⟶ T) :
    Continuous (testRestrict G P a) :=
  continuous_lift G T' P _ _ (fun n =>
    (continuous_of_discreteTopology (f := levelRestrict G a n.val)).comp
      (continuous_evaluation G T P n))

/-- Restriction is linear for the full residue action. -/
def fullTestRestrict (P : ℕ → Prop) (a : T' ⟶ T) :
    Integral G T P →L[Global.ProfiniteIntegerRing] Integral G T' P where
  toFun := testRestrict G P a
  map_add' := (testRestrict G P a).map_add
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (levelRestrict G a n.val) (fullReduction P n r) (x.val n)
  cont := continuous_testRestrict G P a

@[simp] theorem fullTestRestrict_apply (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Integral G T P) : fullTestRestrict G P a x = testRestrict G P a x := rfl

/-- Restriction is also linear for the away residue action. -/
def awayTestRestrict (m : ℕ) (a : T' ⟶ T) :
    Away G T m →L[Global.PrimeToProfiniteIntegerRing m] Away G T' m where
  toFun := testRestrict G (fun n => Nat.Coprime n m) a
  map_add' := (testRestrict G (fun n => Nat.Coprime n m) a).map_add
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact ZMod.map_smul (levelRestrict G a n.val) (awayReduction m n r) (x.val n)
  cont := continuous_testRestrict G (fun n => Nat.Coprime n m) a

@[simp] theorem awayTestRestrict_apply (m : ℕ) (a : T' ⟶ T) (x : Away G T m) :
    awayTestRestrict G m a x = testRestrict G (fun n => Nat.Coprime n m) a x := rfl

/-- Changing the test scheme commutes with restriction of the order indices. -/
theorem testRestrict_restrictAway (m : ℕ) (a : T' ⟶ T) (x : Full G T) :
    testRestrict G (fun n => Nat.Coprime n m) a (restrictAway G T m x) =
      restrictAway G T' m (testRestrict G (fun _ => True) a x) := rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Precomposition in the test scheme commutes with a group-scheme homomorphism. -/
theorem testRestrict_map (P : ℕ → Prop) (a : T' ⟶ T) (f : G ⟶ H)
    (x : Integral G T P) :
    testRestrict H P a (map T P f x) = map T' P f (testRestrict G P a x) := by
  apply Subtype.ext
  funext n
  apply toSection_injective H T' n.val
  exact (Category.assoc a (Additive.toMul (x.val n)).val f.hom.hom).symm

end Langlands.GroupScheme.Tate
