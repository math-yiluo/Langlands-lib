import Langlands.Shimura.Levels
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Opposite

/-! # Invariant right orbits for commuting actions -/

universe u v w

namespace Langlands.Shimura.PEL

variable {G : Type u} {Γ : Type v} {X : Type w}
variable [Group G] [Group Γ] [MulAction Gᵐᵒᵖ X] [MulAction Γ X]
variable [SMulCommClass Γ Gᵐᵒᵖ X]

/-- Write an action of the opposite group as a right action. -/
def right (x : X) (g : G) : X := MulOpposite.op g • x

@[simp] theorem right_one (x : X) : right x (1 : G) = x := one_smul _ _

theorem right_mul (x : X) (g h : G) : right (right x g) h = right x (g * h) := by
  exact (mul_smul (MulOpposite.op h) (MulOpposite.op g) x).symm

theorem right_comm (γ : Γ) (x : X) (g : G) :
    γ • right x g = right (γ • x) g := smul_comm γ (MulOpposite.op g) x

/-- Equality up to the right action of an element of the level subgroup. -/
def rightOrbitSetoid (U : Subgroup G) : Setoid X where
  r x y := ∃ u : G, u ∈ U ∧ y = right x u
  iseqv := by
    constructor
    · intro x
      exact ⟨1, U.one_mem, (right_one x).symm⟩
    · rintro x y ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, U.inv_mem hu, by simp [right_mul]⟩
    · rintro x y z ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u * v, U.mul_mem hu hv, right_mul x u v⟩

/-- The right orbit set, before imposing monodromy invariance. -/
def RightOrbit (X : Type w) [MulAction Gᵐᵒᵖ X] (U : Subgroup G) : Type w :=
  Quotient (rightOrbitSetoid (X := X) U)

namespace RightOrbit

variable (U : Subgroup G)

/-- The orbit containing a representative. -/
def mk (x : X) : RightOrbit X U := Quotient.mk _ x

theorem mk_eq_mk (x y : X) : mk U x = mk U y ↔
    ∃ u : G, u ∈ U ∧ y = right x u := Quotient.eq

/-- Commutation with the right action lets the left action descend to orbits. -/
def left (γ : Γ) : RightOrbit X U → RightOrbit X U :=
  Quotient.map (fun x => γ • x) (by
    rintro x y ⟨u, hu, rfl⟩
    exact ⟨u, hu, right_comm γ x u⟩)

@[simp] theorem left_mk (γ : Γ) (x : X) : left U γ (mk U x) = mk U (γ • x) := rfl

instance : MulAction Γ (RightOrbit X U) where
  smul := left U
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h x => change mk U ((1 : Γ) • x) = mk U x; rw [one_smul]
  mul_smul γ δ q := by
    induction q using Quotient.inductionOn with
    | h x => change mk U ((γ * δ) • x) = mk U (γ • δ • x); rw [mul_smul]

@[simp] theorem smul_mk (γ : Γ) (x : X) : γ • mk U x = mk U (γ • x) := rfl

/-- An orbit is fixed when every left translate belongs to the same right orbit.
The representative itself need not be fixed. -/
theorem mk_mem_fixedPoints (x : X) :
    mk U x ∈ MulAction.fixedPoints Γ (RightOrbit X U) ↔
      ∀ γ : Γ, ∃ u : G, u ∈ U ∧ γ • x = right x u := by
  constructor
  · intro h γ
    exact (mk_eq_mk U x (γ • x)).mp (h γ).symm
  · intro h γ
    exact ((mk_eq_mk U x (γ • x)).mpr (h γ)).symm

variable {U} {V W : Subgroup G}

/-- Right translation descends under the transporter condition `g⁻¹ U g ≤ V`. -/
def translate (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) :
    RightOrbit X U → RightOrbit X V :=
  Quotient.map (fun x => right x g) (by
    rintro x y ⟨u, hu, rfl⟩
    refine ⟨g⁻¹ * u * g, hg u hu, ?_⟩
    simp [right_mul, mul_assoc])

@[simp] theorem translate_mk (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (x : X) :
    translate g hg (mk U x) = mk V (right x g) := rfl

theorem translate_smul (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (γ : Γ) (q : RightOrbit X U) :
    translate g hg (γ • q) = γ • translate g hg q := by
  induction q using Quotient.inductionOn with
  | h x => change mk V (right (γ • x) g) = mk V (γ • right x g); rw [right_comm]

@[simp] theorem translate_one (q : RightOrbit X U) :
    translate (V := U) 1 (by intro u hu; simpa using hu) q = q := by
  induction q using Quotient.inductionOn with
  | h x => change mk U (right x 1) = mk U x; rw [right_one]

theorem translate_comp (g h : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (hh : ∀ v ∈ V, h⁻¹ * v * h ∈ W)
    (q : RightOrbit X U) :
    translate h hh (translate g hg q) =
      translate (g * h) (by intro u hu; simpa [mul_assoc] using hh _ (hg u hu)) q := by
  induction q using Quotient.inductionOn with
  | h x => change mk W (right (right x g) h) = mk W (right x (g * h)); rw [right_mul]

end RightOrbit

/-- The subset of right level orbits fixed by the commuting left action. -/
def InvariantOrbit (Γ : Type v) [Group Γ] [MulAction Γ X]
    [SMulCommClass Γ Gᵐᵒᵖ X] (U : Subgroup G) : Type w :=
  MulAction.fixedPoints Γ (RightOrbit X U)

namespace InvariantOrbit

variable {U V W : Subgroup G}

/-- Transport of invariant orbits along an element satisfying the level condition. -/
def translate (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) :
    InvariantOrbit (X := X) Γ U → InvariantOrbit (X := X) Γ V := fun q =>
  ⟨RightOrbit.translate g hg q.1, fun γ => by
    rw [← RightOrbit.translate_smul, q.2 γ]⟩

@[simp] theorem translate_val (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (q : InvariantOrbit (X := X) Γ U) :
    (translate g hg q).1 = RightOrbit.translate g hg q.1 := rfl

@[simp] theorem translate_one (q : InvariantOrbit (X := X) Γ U) :
    translate (V := U) 1 (by intro u hu; simpa using hu) q = q :=
  Subtype.ext (RightOrbit.translate_one q.1)

theorem translate_comp (g h : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (hh : ∀ v ∈ V, h⁻¹ * v * h ∈ W)
    (q : InvariantOrbit (X := X) Γ U) :
    translate h hh (translate g hg q) =
      translate (g * h) (by intro u hu; simpa [mul_assoc] using hh _ (hg u hu)) q :=
  Subtype.ext (RightOrbit.translate_comp g h hg hh q.1)

/-- Forget a finer level; no choice of representative is involved. -/
def forget (hUV : U ≤ V) : InvariantOrbit (X := X) Γ U → InvariantOrbit (X := X) Γ V :=
  translate 1 (by intro u hu; simpa using hUV hu)

section Tower

open CategoryTheory

variable [TopologicalSpace G]

/-- The fixed-orbit functor on the already published compact-open transporter category. -/
def tower : CompactOpenLevel G ⥤ Type w where
  obj U := InvariantOrbit (X := X) Γ U.subgroup
  map f := TypeCat.ofHom (translate f.element f.respects)
  map_id U := by ext q; exact translate_one q
  map_comp f g := by ext q; exact (translate_comp f.element g.element f.respects g.respects q).symm

end Tower
end InvariantOrbit
end Langlands.Shimura.PEL
