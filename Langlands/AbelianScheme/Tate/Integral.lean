import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.Multiplication
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Topology.Algebra.Group.Basic

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The subgroup cut out by the actual multiplication morphism on sections. -/
def levelGroup (n : ℕ) : Subgroup (T ⟶ G.X) :=
  ((yonedaGrp.map (multiplication G n)).app (.op T)).hom.ker

@[simp]
lemma mem_levelGroup (n : ℕ) (x : T ⟶ G.X) :
    x ∈ levelGroup G T n ↔ x ^ n = 1 := by
  change x ≫ (multiplication G (n : ℤ)).hom.hom = 1 ↔ _
  rw [points_multiplication]
  simp

/-- Additive notation for the points of the actual torsion kernel. -/
abbrev Level (n : ℕ) := Additive (levelGroup G T n)

instance (n : ℕ) : AddCommGroup (Level G T n) :=
  inferInstanceAs (AddCommGroup (Additive (levelGroup G T n)))

/-- The level carries the discrete topology; no finiteness is asserted. -/
instance (n : ℕ) : TopologicalSpace (Level G T n) := ⊥
instance (n : ℕ) : DiscreteTopology (Level G T n) := ⟨rfl⟩

/-- The kernel universal property identifies torsion-scheme points with the level. -/
def kernelLevelEquiv (n : ℕ) :
    Additive (T ⟶ (kernel (multiplication G n)).X) ≃+ Level G T n :=
  (kernelPointsEquiv (multiplication G n) T).toAdditive

/-- The underlying section of a torsion point, in additive notation. -/
def toSection (n : ℕ) : Level G T n →+ Additive (T ⟶ G.X) :=
  (levelGroup G T n).subtype.toAdditive

lemma toSection_injective (n : ℕ) : Function.Injective (toSection G T n) :=
  fun _ _ h => Subtype.ext h

/-- For `n ∣ m`, the transition is multiplication by `m / n`. -/
def transition {n m : ℕ} (h : n ∣ m) : Level G T m →+ Level G T n :=
  MonoidHom.toAdditive {
    toFun := fun x => ⟨x.val ^ (m / n), by
      rw [mem_levelGroup, ← pow_mul, Nat.div_mul_cancel h]
      exact (mem_levelGroup G T m x.val).mp x.property⟩
    map_one' := by apply Subtype.ext; exact one_pow _
    map_mul' := fun x y => by apply Subtype.ext; exact mul_pow _ _ _ }

@[simp]
lemma transition_self {n : ℕ} (hn : 0 < n) (x : Level G T n) :
    transition G T (dvd_refl n) x = x := by
  apply toSection_injective G T n
  change (Additive.toMul x).val ^ (n / n) = (Additive.toMul x).val
  rw [Nat.div_self hn, pow_one]

lemma transition_comp {n m k : ℕ} (hnm : n ∣ m) (hmk : m ∣ k)
    (x : Level G T k) :
    transition G T hnm (transition G T hmk x) =
      transition G T (dvd_trans hnm hmk) x := by
  apply toSection_injective G T n
  change ((Additive.toMul x).val ^ (k / m)) ^ (m / n) = _
  rw [← pow_mul, Nat.div_mul_div hmk hnm]
  rfl

/-- Positive levels selected by a predicate, ordered by divisibility in the compatibility law. -/
def Index (P : ℕ → Prop) := {n : ℕ // 0 < n ∧ P n}

/-- Coherent families form a subgroup of the product of the torsion levels. -/
def coherent (P : ℕ → Prop) : AddSubgroup (∀ n : Index P, Level G T n.val) where
  carrier := {x | ∀ (n m : Index P) (h : n.val ∣ m.val), transition G T h (x m) = x n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro x y hx hy n m h
    change transition G T h (x m + y m) = x n + y n
    rw [map_add, hx n m h, hy n m h]
  neg_mem' := by
    intro x hx n m h
    change transition G T h (-x m) = -x n
    rw [map_neg, hx n m h]

/-- The inverse limit, with its coordinatewise group structure and product-subspace topology. -/
def Integral (P : ℕ → Prop) : Type _ := ↥(coherent G T P)

instance (P : ℕ → Prop) : AddCommGroup (Integral G T P) :=
  inferInstanceAs (AddCommGroup (coherent G T P))
instance (P : ℕ → Prop) : TopologicalSpace (Integral G T P) :=
  inferInstanceAs (TopologicalSpace (coherent G T P))
instance (P : ℕ → Prop) : IsTopologicalAddGroup (Integral G T P) :=
  inferInstanceAs (IsTopologicalAddGroup (coherent G T P))

/-- The full integral Tate group. -/
abbrev Full := Integral G T (fun _ => True)
/-- The prime-to-`p` integral Tate group; the definition works for any natural `p`. -/
abbrev Away (p : ℕ) := Integral G T (fun n => Nat.Coprime n p)

/-- Projection to a torsion level. -/
def evaluation (P : ℕ → Prop) (n : Index P) : Integral G T P →+ Level G T n.val where
  toFun := fun x => x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma continuous_evaluation (P : ℕ → Prop) (n : Index P) :
    Continuous (evaluation G T P n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Compatibility of the universal projections. -/
lemma evaluation_transition (P : ℕ → Prop) (n m : Index P) (h : n.val ∣ m.val)
    (x : Integral G T P) :
    transition G T h (evaluation G T P m x) = evaluation G T P n x :=
  x.property n m h

/-- A compatible family of homomorphisms gives a unique homomorphism into the limit. -/
def lift (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level G T n.val)
    (hf : ∀ (n m : Index P) (h : n.val ∣ m.val) (a : A),
      transition G T h (f m a) = f n a) : A →+ Integral G T P where
  toFun a := ⟨fun n => f n a, fun n m h => hf n m h a⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero (f n)
  map_add' a b := by apply Subtype.ext; funext n; exact map_add (f n) a b

@[simp]
lemma evaluation_lift (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level G T n.val) (hf) (n : Index P) (a : A) :
    evaluation G T P n (lift G T P f hf a) = f n a := rfl

lemma lift_unique (P : ℕ → Prop) {A : Type*} [AddGroup A]
    (f : ∀ n : Index P, A →+ Level G T n.val) (hf)
    (g : A →+ Integral G T P)
    (hg : ∀ n a, evaluation G T P n (g a) = f n a) : g = lift G T P f hf := by
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  funext n
  exact hg n a

/-- The universal lift is continuous when its coordinates are continuous. -/
lemma continuous_lift (P : ℕ → Prop) {A : Type*} [AddGroup A] [TopologicalSpace A]
    (f : ∀ n : Index P, A →+ Level G T n.val) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift G T P f hf) :=
  (continuous_pi hc).subtype_mk _

/-- Restriction of a full coherent family to the levels prime to `p`. -/
def restrictAway (p : ℕ) : Full G T →+ Away G T p :=
  lift G T (fun n => Nat.Coprime n p)
    (fun n => evaluation G T (fun _ => True) ⟨n.val, n.property.1, trivial⟩)
    (fun n m h x => x.property ⟨n.val, n.property.1, trivial⟩
      ⟨m.val, m.property.1, trivial⟩ h)

lemma continuous_restrictAway (p : ℕ) : Continuous (restrictAway G T p) :=
  continuous_lift G T _ _ _ (fun _ => continuous_evaluation G T _ _)

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- A group-scheme homomorphism acts on the actual torsion point group. -/
def levelMap (f : G ⟶ H) (n : ℕ) : Level G T n →+ Level H T n :=
  MonoidHom.toAdditive {
    toFun := fun x => ⟨x.val ≫ f.hom.hom, by
      rw [mem_levelGroup, ← CategoryTheory.MonObj.pow_comp]
      rw [(mem_levelGroup G T n x.val).mp x.property]
      exact CategoryTheory.MonObj.one_comp _⟩
    map_one' := by apply Subtype.ext; exact CategoryTheory.MonObj.one_comp f.hom.hom
    map_mul' := fun x y => by apply Subtype.ext; exact CategoryTheory.MonObj.mul_comp x.val y.val f.hom.hom }

lemma levelMap_transition (f : G ⟶ H) {n m : ℕ} (h : n ∣ m) (x : Level G T m) :
    levelMap T f n (transition G T h x) = transition H T h (levelMap T f m x) := by
  apply toSection_injective H T n
  exact map_pow ((yonedaGrp.map f).app (.op T)).hom _ _

/-- The induced map of integral Tate groups acts coordinatewise. -/
def map (P : ℕ → Prop) (f : G ⟶ H) : Integral G T P →+ Integral H T P :=
  lift H T P (fun n => (levelMap T f n.val).comp (evaluation G T P n)) (by
    intro n m h x
    change transition H T h (levelMap T f m.val (x.val m)) = levelMap T f n.val (x.val n)
    rw [← levelMap_transition, x.property n m h])

@[simp]
lemma evaluation_map (P : ℕ → Prop) (f : G ⟶ H) (n : Index P) (x : Integral G T P) :
    evaluation H T P n (map T P f x) = levelMap T f n.val (evaluation G T P n x) := rfl

@[simp]
lemma map_id (P : ℕ → Prop) : map T P (𝟙 G) = AddMonoidHom.id (Integral G T P) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective G T n.val
  change (Additive.toMul (x.val n)).val ≫ 𝟙 G.X = _
  exact Category.comp_id _

lemma map_comp (P : ℕ → Prop) (f : G ⟶ H) (g : H ⟶ K) :
    map T P (f ≫ g) = (map T P g).comp (map T P f) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective K T n.val
  change (Additive.toMul (x.val n)).val ≫ (f ≫ g).hom.hom = _
  exact (Category.assoc (Additive.toMul (x.val n)).val f.hom.hom g.hom.hom).symm

/-- Pointwise multiplication of group-scheme morphisms is addition in Tate notation. -/
lemma map_mul (P : ℕ → Prop) (f g : G ⟶ H) :
    map T P (f * g) = map T P f + map T P g := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  funext n
  apply toSection_injective H T n.val
  change (Additive.toMul (x.val n)).val ≫ (f * g).hom.hom = _
  exact CategoryTheory.MonObj.comp_mul (Additive.toMul (x.val n)).val f.hom.hom g.hom.hom

lemma continuous_map (P : ℕ → Prop) (f : G ⟶ H) : Continuous (map T P f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelMap T f n.val)).comp
    (continuous_evaluation G T P n)

variable (G)

/-- Actual fibre points of the torsion scheme identify with the corresponding level.
This works over any base-change scheme, in particular a geometric point. -/
def fibreLevelEquiv {U : Scheme.{u}} (s : U ⟶ S) (n : ℕ) :
    (Over.mk (𝟙 U) ⟶ (Over.pullback s).obj (kernel (multiplication G n)).X) ≃
      Level G (Over.mk s) n := by
  let e : (Over.map s).obj (Over.mk (𝟙 U)) ≅ Over.mk s :=
    Over.isoMk (Iso.refl U) (by simp)
  exact ((Over.mapPullbackAdj s).homEquiv (Over.mk (𝟙 U))
    (kernel (multiplication G n)).X).symm |>.trans
      ((Iso.homCongr e (Iso.refl _)).trans
        (Additive.ofMul.trans (kernelLevelEquiv G (Over.mk s) n).toEquiv))

/-- The full integral Tate group at a field-valued point; take an algebraically
closed field for the geometric-point convention. -/
abbrev FullAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Full G (Over.mk s)

/-- The prime-to-`p` integral Tate group at a field-valued point. -/
abbrev AwayAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) (p : ℕ) :=
  Away G (Over.mk s) p

end Langlands.GroupScheme.Tate
