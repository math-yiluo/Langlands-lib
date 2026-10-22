import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Tate.Integral

/-! # Integral Tate groups of bundled abelian schemes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

/-- Actual torsion points of the underlying group scheme, in additive notation. -/
abbrev Level (n : ℕ) := GroupScheme.Tate.Level A.toGrp T n

/-- The integral coherent-family limit for selected positive levels. -/
abbrev Integral (P : ℕ → Prop) := GroupScheme.Tate.Integral A.toGrp T P

/-- The full integral Tate group of an abelian scheme on a test scheme. -/
abbrev Full := Integral A T (fun _ => True)

/-- The prime-to-`p` integral Tate group; the formula works for any natural `p`. -/
abbrev Away (p : ℕ) := Integral A T (fun n => Nat.Coprime n p)

/-- The actual multiplication-kernel points give precisely the torsion level. -/
abbrev kernelLevelEquiv (n : ℕ) :
    Additive (T ⟶ (GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X) ≃+
      Level A T n :=
  GroupScheme.Tate.kernelLevelEquiv A.toGrp T n

/-- Multiplication by `m / n` on actual torsion sections. -/
abbrev transition {n m : ℕ} (h : n ∣ m) : Level A T m →+ Level A T n :=
  GroupScheme.Tate.transition A.toGrp T h

@[simp]
theorem transition_self {n : ℕ} (hn : 0 < n) (x : Level A T n) :
    transition A T (dvd_refl n) x = x :=
  GroupScheme.Tate.transition_self A.toGrp T hn x

theorem transition_comp {n m k : ℕ} (hnm : n ∣ m) (hmk : m ∣ k)
    (x : Level A T k) :
    transition A T hnm (transition A T hmk x) =
      transition A T (dvd_trans hnm hmk) x :=
  GroupScheme.Tate.transition_comp A.toGrp T hnm hmk x

/-- Projection of a coherent family to its selected torsion level. -/
abbrev evaluation (P : ℕ → Prop) (n : GroupScheme.Tate.Index P) :
    Integral A T P →+ Level A T n.val :=
  GroupScheme.Tate.evaluation A.toGrp T P n

theorem continuous_evaluation (P : ℕ → Prop) (n : GroupScheme.Tate.Index P) :
    Continuous (evaluation A T P n) :=
  GroupScheme.Tate.continuous_evaluation A.toGrp T P n

theorem evaluation_transition (P : ℕ → Prop) (n m : GroupScheme.Tate.Index P)
    (h : n.val ∣ m.val) (x : Integral A T P) :
    transition A T h (evaluation A T P m x) = evaluation A T P n x :=
  GroupScheme.Tate.evaluation_transition A.toGrp T P n m h x

/-- The universal map from a compatible family of additive homomorphisms. -/
abbrev lift (P : ℕ → Prop) {B : Type*} [AddGroup B]
    (f : ∀ n : GroupScheme.Tate.Index P, B →+ Level A T n.val)
    (hf : ∀ (n m : GroupScheme.Tate.Index P) (h : n.val ∣ m.val) (b : B),
      transition A T h (f m b) = f n b) : B →+ Integral A T P :=
  GroupScheme.Tate.lift A.toGrp T P f hf

@[simp]
theorem evaluation_lift (P : ℕ → Prop) {B : Type*} [AddGroup B]
    (f : ∀ n : GroupScheme.Tate.Index P, B →+ Level A T n.val) (hf)
    (n : GroupScheme.Tate.Index P) (b : B) :
    evaluation A T P n (lift A T P f hf b) = f n b := rfl

theorem lift_unique (P : ℕ → Prop) {B : Type*} [AddGroup B]
    (f : ∀ n : GroupScheme.Tate.Index P, B →+ Level A T n.val) (hf)
    (g : B →+ Integral A T P)
    (hg : ∀ n b, evaluation A T P n (g b) = f n b) : g = lift A T P f hf :=
  GroupScheme.Tate.lift_unique A.toGrp T P f hf g hg

theorem continuous_lift (P : ℕ → Prop) {B : Type*} [AddGroup B] [TopologicalSpace B]
    (f : ∀ n : GroupScheme.Tate.Index P, B →+ Level A T n.val) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift A T P f hf) :=
  GroupScheme.Tate.continuous_lift A.toGrp T P f hf hc

/-- Restriction from all positive levels to the levels prime to `p`. -/
abbrev restrictAway (p : ℕ) : Full A T →+ Away A T p :=
  GroupScheme.Tate.restrictAway A.toGrp T p

theorem continuous_restrictAway (p : ℕ) : Continuous (restrictAway A T p) :=
  GroupScheme.Tate.continuous_restrictAway A.toGrp T p

variable {A} {B C : AbelianScheme S}

/-- An abelian-scheme homomorphism acts on torsion points by postcomposition. -/
abbrev levelMap (f : A ⟶ B) (n : ℕ) : Level A T n →+ Level B T n :=
  GroupScheme.Tate.levelMap T (AbelianScheme.groupHom f) n

theorem levelMap_transition (f : A ⟶ B) {n m : ℕ} (h : n ∣ m)
    (x : Level A T m) :
    levelMap T f n (transition A T h x) = transition B T h (levelMap T f m x) :=
  GroupScheme.Tate.levelMap_transition T (AbelianScheme.groupHom f) h x

/-- The continuous coordinatewise map induced by an abelian-scheme homomorphism. -/
abbrev map (P : ℕ → Prop) (f : A ⟶ B) : Integral A T P →+ Integral B T P :=
  GroupScheme.Tate.map T P (AbelianScheme.groupHom f)

@[simp]
theorem evaluation_map (P : ℕ → Prop) (f : A ⟶ B)
    (n : GroupScheme.Tate.Index P) (x : Integral A T P) :
    evaluation B T P n (map T P f x) = levelMap T f n.val (evaluation A T P n x) :=
  GroupScheme.Tate.evaluation_map T P (AbelianScheme.groupHom f) n x

@[simp]
theorem map_id (P : ℕ → Prop) :
    map T P (𝟙 A) = AddMonoidHom.id (Integral A T P) :=
  GroupScheme.Tate.map_id T P

theorem map_comp (P : ℕ → Prop) (f : A ⟶ B) (g : B ⟶ C) :
    map T P (f ≫ g) = (map T P g).comp (map T P f) :=
  GroupScheme.Tate.map_comp T P (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

/-- Addition of abelian-scheme homomorphisms induces addition of Tate maps. -/
theorem map_add (P : ℕ → Prop) (f g : A ⟶ B) :
    map T P (f + g) = map T P f + map T P g :=
  GroupScheme.Tate.map_mul T P (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

theorem continuous_map (P : ℕ → Prop) (f : A ⟶ B) : Continuous (map T P f) :=
  GroupScheme.Tate.continuous_map T P (AbelianScheme.groupHom f)

variable (A)

/-- Actual sections of the torsion fibre identify with the corresponding level. -/
abbrev fibreLevelEquiv {U : Scheme.{u}} (s : U ⟶ S) (n : ℕ) :
    (Over.mk (𝟙 U) ⟶
      (Over.pullback s).obj (GroupScheme.kernel (GroupScheme.multiplication A.toGrp n)).X) ≃
        Level A (Over.mk s) n :=
  GroupScheme.Tate.fibreLevelEquiv A.toGrp s n

/-- Full integral Tate group at a field-valued point; take an algebraically closed
field to obtain the geometric-point convention. -/
abbrev FullAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Full A (Over.mk s)

/-- Prime-to-`p` integral Tate group at a field-valued point. -/
abbrev AwayAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) (p : ℕ) :=
  Away A (Over.mk s) p

end Langlands.AbelianScheme.Tate
