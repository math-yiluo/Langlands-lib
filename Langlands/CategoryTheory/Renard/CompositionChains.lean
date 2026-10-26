import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Renard A.VI.3: simple objects, composition chains and simple subquotients

Source: Renard, *Représentations des groupes réductifs p-adiques*
(French edition dated 9 July 2026), Appendix A.VI.3, printed pages 263–264.
The type of isomorphism classes is defined over an arbitrary category; every
other construction lives in an arbitrary abelian category. Object and Hom
universes are independent, and the constructions use actual subobjects and
actual cokernels. No Jordan–Hölder theorem or extra categorical hypothesis is
assumed.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

/-! ### Isomorphism classes of objects -/

section ObjectClass

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The type of isomorphism classes of objects of `C`. It lies in the object
universe `u`, independently of the Hom universe `v`. -/
abbrev ObjectClass : Type u := Quotient (isIsomorphicSetoid C)

/-- The isomorphism class of an object. -/
def objectClass (X : C) : ObjectClass C := Quotient.mk (isIsomorphicSetoid C) X

/-- Two objects have the same class exactly when they are isomorphic. -/
theorem objectClass_eq_iff {X Y : C} : objectClass X = objectClass Y ↔ Nonempty (X ≅ Y) :=
  Quotient.eq

/-- Every class is the class of an object. -/
theorem objectClass_surjective : Function.Surjective (objectClass : C → ObjectClass C) :=
  Quotient.mk_surjective

end ObjectClass

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Simple objects and simple classes -/

/-- Renard's simple object: `X` is nonzero and every subobject of `X` is the
zero subobject or `X` itself. -/
def IsSimpleObject (X : C) : Prop :=
  ¬ IsZero X ∧ ∀ P : Subobject X, P = ⊥ ∨ P = ⊤

/-- The source simplicity condition is Mathlib's categorical `Simple`. -/
theorem isSimpleObject_iff_simple (X : C) : IsSimpleObject X ↔ Simple X := by
  rw [simple_iff_subobject_isSimpleOrder]
  constructor
  · rintro ⟨hX, h⟩
    exact { toNontrivial := Subobject.nontrivial_of_not_isZero hX, eq_bot_or_eq_top := h }
  · intro h
    refine ⟨fun hX => ?_, IsSimpleOrder.eq_bot_or_eq_top⟩
    have := Subobject.subsingleton_of_isZero hX
    exact IsSimpleOrder.bot_ne_top (Subsingleton.elim (⊥ : Subobject X) ⊤)

variable (C) in
/-- Renard's `Irr(A)`: the set of isomorphism classes of simple objects. -/
def simpleClasses : Set (ObjectClass C) :=
  {q | ∃ Y : C, Simple Y ∧ objectClass Y = q}

/-- An object's class lies in `simpleClasses C` exactly when the object is simple. -/
theorem objectClass_mem_simpleClasses_iff (X : C) :
    objectClass X ∈ simpleClasses C ↔ Simple X := by
  constructor
  · rintro ⟨Y, hY, hq⟩
    obtain ⟨e⟩ := objectClass_eq_iff.mp hq
    have := hY
    exact Simple.of_iso e.symm
  · intro h
    exact ⟨X, h, rfl⟩

/-! ### Composition chains -/

/-- A composition chain of `X` with `n` successive factors (Renard A.VI.3):
subobjects `0 = B 0 < B 1 < ⋯ < B n = X` of `X` whose successive factors, the
actual cokernels `B (i + 1) / B i` for `i < n`, are simple. -/
structure CompositionChain (X : C) (n : ℕ) where
  /-- The subobjects `B 0, …, B n` of `X`. -/
  subobject : Fin (n + 1) → Subobject X
  /-- The subobjects are strictly increasing, hence pairwise distinct. -/
  strictMono : StrictMono subobject
  /-- The first subobject is the zero subobject. -/
  subobject_zero : subobject 0 = ⊥
  /-- The last subobject is `X` itself. -/
  subobject_last : subobject (Fin.last n) = ⊤
  /-- Each successive factor, the cokernel of the actual inclusion
  `B i ⟶ B (i + 1)`, is simple. -/
  simple_factor : ∀ i : Fin n,
    Simple (cokernel (Subobject.ofLE (subobject i.castSucc) (subobject i.succ)
      (strictMono i.castSucc_lt_succ).le))

namespace CompositionChain

variable {X : C} {n : ℕ} (c : CompositionChain X n)

/-- The length of a composition chain: its number `n` of successive factors. -/
def length (_ : CompositionChain X n) : ℕ := n

theorem length_eq : c.length = n := rfl

theorem le_succ (i : Fin n) : c.subobject i.castSucc ≤ c.subobject i.succ :=
  (c.strictMono i.castSucc_lt_succ).le

/-- The actual inclusion `B i ⟶ B (i + 1)` of underlying objects. -/
def inclusion (i : Fin n) : (c.subobject i.castSucc : C) ⟶ (c.subobject i.succ : C) :=
  Subobject.ofLE _ _ (c.le_succ i)

instance (i : Fin n) : Mono (c.inclusion i) := by
  unfold inclusion
  infer_instance

/-- The inclusion is compatible with the arrows into `X`. -/
theorem inclusion_arrow (i : Fin n) :
    c.inclusion i ≫ (c.subobject i.succ).arrow = (c.subobject i.castSucc).arrow :=
  Subobject.ofLE_arrow _

/-- The `i`-th composition factor `B (i + 1) / B i`: the actual cokernel of the
inclusion. -/
def factor (i : Fin n) : C := cokernel (c.inclusion i)

/-- The quotient map `B (i + 1) ⟶ B (i + 1) / B i`. -/
def factorπ (i : Fin n) : (c.subobject i.succ : C) ⟶ c.factor i := cokernel.π _

instance factor_simple (i : Fin n) : Simple (c.factor i) := c.simple_factor i

/-- The isomorphism class of the `i`-th composition factor. -/
def factorClass (i : Fin n) : ObjectClass C := objectClass (c.factor i)

theorem factorClass_mem_simpleClasses (i : Fin n) : c.factorClass i ∈ simpleClasses C :=
  ⟨c.factor i, c.simple_factor i, rfl⟩

end CompositionChain

/-- `X` admits a composition chain with exactly `n` successive factors. -/
def HasCompositionChainOfLength (X : C) (n : ℕ) : Prop :=
  Nonempty (CompositionChain X n)

/-- Renard's finite length: `X` admits a composition chain of some length. -/
def IsFiniteLength (X : C) : Prop :=
  ∃ n : ℕ, HasCompositionChainOfLength X n

/-- Unfolded form of `HasCompositionChainOfLength`. -/
theorem hasCompositionChainOfLength_iff (X : C) (n : ℕ) :
    HasCompositionChainOfLength X n ↔
      ∃ (B : Fin (n + 1) → Subobject X) (hB : StrictMono B),
        B 0 = ⊥ ∧ B (Fin.last n) = ⊤ ∧
          ∀ i : Fin n, Simple (cokernel (Subobject.ofLE (B i.castSucc) (B i.succ)
            (hB i.castSucc_lt_succ).le)) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.subobject, c.strictMono, c.subobject_zero, c.subobject_last, c.simple_factor⟩
  · rintro ⟨B, hB, h0, hn, hs⟩
    exact ⟨⟨B, hB, h0, hn, hs⟩⟩

/-- A composition chain of length zero exists exactly for zero objects. -/
theorem hasCompositionChainOfLength_zero_iff (X : C) :
    HasCompositionChainOfLength X 0 ↔ IsZero X := by
  constructor
  · rintro ⟨c⟩
    by_contra hX
    have := Subobject.nontrivial_of_not_isZero hX
    exact bot_ne_top (c.subobject_zero.symm.trans c.subobject_last)
  · intro hX
    have := Subobject.subsingleton_of_isZero hX
    refine ⟨⟨fun _ => ⊥, fun a b hab => ?_, rfl, Subsingleton.elim _ _, fun i => i.elim0⟩⟩
    have hab' : a = b := Subsingleton.elim (α := Fin 1) a b
    subst hab'
    exact absurd hab (lt_irrefl a)

/-! ### Simple subquotient classes -/

/-- Renard's `JH(X)`: the set of isomorphism classes of simple actual
subquotients `B / A` of `X`, for subobjects `A ≤ B` of `X`. -/
def simpleSubquotientClasses (X : C) : Set (ObjectClass C) :=
  {q | ∃ (A B : Subobject X) (h : A ≤ B),
    Simple (cokernel (Subobject.ofLE A B h)) ∧
      objectClass (cokernel (Subobject.ofLE A B h)) = q}

theorem simpleSubquotientClasses_subset_simpleClasses (X : C) :
    simpleSubquotientClasses X ⊆ simpleClasses C := by
  rintro q ⟨A, B, h, hs, rfl⟩
  exact ⟨_, hs, rfl⟩

/-- Every composition factor of a composition chain of `X` is a simple subquotient. -/
theorem CompositionChain.factorClass_mem_simpleSubquotientClasses {X : C} {n : ℕ}
    (c : CompositionChain X n) (i : Fin n) :
    c.factorClass i ∈ simpleSubquotientClasses X :=
  ⟨_, _, c.le_succ i, c.simple_factor i, rfl⟩

end

end Langlands.Renard
