import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Renard A.IV.2: the concrete directed quotient

The quotient of the disjoint union by eventual equality, its inherited
abelian-group operations, canonical maps, and a cocone on the lifted diagram.
The raw quotient also exists for an empty index, when it is empty.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.FilteredColimit

universe uI uG uH

variable {I : Type uI} [PartialOrder I]
variable (G : I → Type uG) [∀ i, AddCommGroup (G i)]
variable (f : ∀ i j, i ≤ j → G i →+ G j)
variable [DirectedSystem G (f · · ·)]

/-- The original diagram, with factors lifted to the universe containing the quotient. -/
def diagram : I ⥤ AddCommGrpCat.{max uI uG} where
  obj i := AddCommGrpCat.of (ULift.{uI} (G i))
  map {i j} h := AddCommGrpCat.ofHom
    ((AddEquiv.ulift : ULift.{uI} (G j) ≃+ G j).symm.toAddMonoidHom.comp
      ((f i j (leOfHom h)).comp
        (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).toAddMonoidHom))
  map_id i := by
    apply AddCommGrpCat.ext
    intro x
    apply ULift.ext
    exact DirectedSystem.map_self' f x.down
  map_comp h k := by
    apply AddCommGrpCat.ext
    intro x
    apply ULift.ext
    exact (DirectedSystem.map_map' f (leOfHom h) (leOfHom k) x.down).symm

variable [IsDirectedOrder I]

/-- Renard's literal quotient of the disjoint union by equality at a common later stage. -/
abbrev Carrier := _root_.DirectLimit G f

/-- The class of a representative, available even without a nonempty-index hypothesis. -/
def classOf (i : I) (x : G i) : Carrier G f := ⟦⟨i, x⟩⟧

/-- Equality of classes is exactly eventual equality of representatives. -/
theorem classOf_eq_iff (i j : I) (x : G i) (y : G j) :
    classOf G f i x = classOf G f j y ↔
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k), f i k hik x = f j k hjk y :=
  Quotient.eq

/-- Moving a representative forward does not change its class. -/
theorem classOf_transition (i j : I) (h : i ≤ j) (x : G i) :
    classOf G f j (f i j h x) = classOf G f i x :=
  DirectLimit.mk_apply i j x h

/-- Every element of the literal quotient has a representative. -/
theorem exists_classOf (z : Carrier G f) :
    ∃ i x, z = classOf G f i x :=
  DirectLimit.exists_eq_mk f z

/-- For an empty index the literal quotient is empty, so cannot be a group carrier. -/
theorem carrier_isEmpty [IsEmpty I] : IsEmpty (Carrier G f) :=
  ⟨fun z => Quotient.inductionOn z fun x => isEmptyElim x.1⟩

section Nonempty

variable [Nonempty I]

/-- The canonical homomorphism from one component into the inherited quotient group. -/
noncomputable def of (i : I) : G i →+ Carrier G f where
  toFun := classOf G f i
  map_zero' := (DirectLimit.zero_def (f := f) i).symm
  map_add' x y := (DirectLimit.add_def (f := f) i x y).symm

@[simp]
theorem of_apply (i : I) (x : G i) :
    of G f i x = classOf G f i x := rfl

/-- The zero class may be represented by zero at any stage. -/
theorem zero_eq_classOf (i : I) :
    (0 : Carrier G f) = classOf G f i 0 :=
  DirectLimit.zero_def i

omit [Nonempty I] in
/-- Addition is computed after moving both representatives to a common stage. -/
theorem classOf_add (i j k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (x : G i) (y : G j) :
    classOf G f i x + classOf G f j y =
      classOf G f k (f i k hik x + f j k hjk y) := by
  rw [← classOf_transition G f i k hik x, ← classOf_transition G f j k hjk y]
  exact DirectLimit.add_def k _ _

/-- Negation is represented by negation in the original component. -/
theorem neg_classOf (i : I) (x : G i) :
    -classOf G f i x = classOf G f i (-x) :=
  DirectLimit.neg_def i x

/-- The canonical homomorphisms commute with every transition. -/
theorem of_comp (i j : I) (h : i ≤ j) :
    (of G f j).comp (f i j h) = of G f i := by
  ext x
  exact classOf_transition G f i j h x

/-- The concrete quotient, with the canonical maps from the lifted factors. -/
noncomputable def cocone : Cocone (diagram G f) where
  pt := AddCommGrpCat.of (Carrier G f)
  ι :=
    { app := fun i => AddCommGrpCat.ofHom
        ((of G f i).comp
          (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).toAddMonoidHom)
      naturality := by
        intro i j h
        apply AddCommGrpCat.ext
        intro x
        exact classOf_transition G f i j (leOfHom h) x.down }

/-- The homomorphism induced by a compatible family on the original components. -/
noncomputable def lift {H : Type uH} [AddCommGroup H]
    (g : ∀ i, G i →+ H)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x) :
    Carrier G f →+ H where
  toFun := DirectLimit.lift f (g · ·) fun i j h x => (hg i j h x).symm
  map_zero' := DirectLimit.lift_zero g _
  map_add' := DirectLimit.lift_add g _

@[simp]
theorem lift_classOf {H : Type uH} [AddCommGroup H]
    (g : ∀ i, G i →+ H)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)
    (i : I) (x : G i) :
    lift G f g hg (classOf G f i x) = g i x := rfl

end Nonempty

/-- The empty diagram is instead supplied with the singleton zero-group cocone. -/
def emptyCocone [IsEmpty I] : Cocone (diagram G f) where
  pt := AddCommGrpCat.of PUnit
  ι :=
    { app := fun i => isEmptyElim i
      naturality := by intro i; exact isEmptyElim i }

end Langlands.Renard.FilteredColimit
