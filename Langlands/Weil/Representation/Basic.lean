import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensional representations and their isomorphism classes

The carrier universe is independent of the coefficient and group universes.
No topology, irreducibility, or semisimplicity condition is built into this category.
-/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands

/-- The full subcategory of representations on finite-dimensional vector spaces. -/
abbrev FiniteRepresentation (K : Type uK) (G : Type uG)
    [Field K] [Monoid G] :=
  (show ObjectProperty (Rep.{uV} K G) from fun A => Module.Finite K A).FullSubcategory

namespace FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G]

instance : CoeSort (FiniteRepresentation.{uK, uG, uV} K G) (Type uV) :=
  ⟨fun A => A.obj⟩

instance (A : FiniteRepresentation K G) : AddCommGroup A :=
  inferInstanceAs (AddCommGroup A.obj)

instance (A : FiniteRepresentation K G) : Module K A :=
  inferInstanceAs (Module K A.obj)

instance (A : FiniteRepresentation K G) : Module.Finite K A := A.property

/-- The action on the actual carrier vector space. -/
abbrev representation (A : FiniteRepresentation K G) : Representation K G A := A.obj.ρ

/-- Bundle an existing representation, without replacing its carrier by coordinates. -/
abbrev of {V : Type uV} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : Representation K G V) : FiniteRepresentation.{uK, uG, uV} K G :=
  ⟨Rep.of ρ, inferInstance⟩

/-- The fully faithful inclusion in Mathlib's category of all representations. -/
abbrev forget : FiniteRepresentation.{uK, uG, uV} K G ⥤ Rep.{uV} K G :=
  (show ObjectProperty (Rep.{uV} K G) from fun A => Module.Finite K A).ι

/-- Morphisms are exactly linear intertwiners. -/
def homEquiv (A B : FiniteRepresentation.{uK, uG, uV} K G) :
    (A ⟶ B) ≃ A.representation.IntertwiningMap B.representation where
  toFun f := f.hom.hom
  invFun f := ObjectProperty.homMk (Rep.ofHom f)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A representation equivalence is an invertible linear intertwiner.
This interface also permits different carrier universes. -/
abbrev Equiv (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :=
  A.representation.Equiv B.representation

/-- Turn a representation equivalence into a categorical isomorphism. -/
def isoOfEquiv {A B : FiniteRepresentation.{uK, uG, uV} K G} (e : Equiv A B) : A ≅ B :=
  ObjectProperty.isoMk _ (Rep.mkIso e)

/-- Extract the actual linear representation equivalence from a categorical isomorphism. -/
def equivOfIso {A B : FiniteRepresentation.{uK, uG, uV} K G} (e : A ≅ B) : Equiv A B :=
  Representation.equivOfIso (forget.mapIso e)

/-- The rank, including rank zero. -/
def rank (A : FiniteRepresentation K G) : ℕ := Module.finrank K A

/-- Rank is invariant under actual linear representation equivalences. -/
theorem rank_eq_of_equiv {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A B) : A.rank = B.rank :=
  e.toLinearEquiv.finrank_eq

/-- Genuine isomorphism: existence of an invertible linear intertwiner. -/
def IsIsomorphic (A B : FiniteRepresentation.{uK, uG, uV} K G) : Prop := Nonempty (Equiv A B)

/-- Reflexivity, symmetry and transitivity are proved using the actual equivalence operations. -/
def isomorphismSetoid : Setoid (FiniteRepresentation.{uK, uG, uV} K G) where
  r := IsIsomorphic
  iseqv := {
    refl := fun A => ⟨Representation.Equiv.refl A.representation⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- The genuine quotient by representation isomorphism, not by equality of matrices. -/
def IsomorphismClasses (K : Type uK) (G : Type uG) [Field K] [Monoid G] :=
  Quotient (isomorphismSetoid : Setoid (FiniteRepresentation.{uK, uG, uV} K G))

/-- The isomorphism class of a representation. -/
def classOf (A : FiniteRepresentation.{uK, uG, uV} K G) : IsomorphismClasses.{uK, uG, uV} K G :=
  Quotient.mk _ A

/-- Equality of classes means exactly existence of a linear intertwining equivalence. -/
theorem classOf_eq_iff (A B : FiniteRepresentation.{uK, uG, uV} K G) :
    classOf A = classOf B ↔ Nonempty (Equiv A B) := Quotient.eq

/-- Rank descends to the quotient, using invariance under linear equivalence. -/
def classRank : IsomorphismClasses.{uK, uG, uV} K G → ℕ :=
  Quotient.lift rank fun _ _ ⟨e⟩ => rank_eq_of_equiv e

@[simp]
theorem classRank_classOf (A : FiniteRepresentation.{uK, uG, uV} K G) :
    classRank (classOf A) = A.rank := rfl

/-- Rank-`n` isomorphism classes. Positive ranks are unrestricted; zero is allowed internally. -/
def IsomorphismClassesOfRank
    (K : Type uK) (G : Type uG) [Field K] [Monoid G] (n : ℕ) :=
  {c : IsomorphismClasses.{uK, uG, uV} K G // classRank c = n}

/-- The same genuine isomorphism relation restricted to objects satisfying a predicate. -/
def propertyIsomorphismSetoid (P : FiniteRepresentation.{uK, uG, uV} K G → Prop) :
    Setoid {A // P A} :=
  Setoid.comap Subtype.val isomorphismSetoid

/-- Classes of representations satisfying an explicitly supplied condition.
No invariance theorem for that condition is assumed. -/
def IsomorphismClassesWith (P : FiniteRepresentation.{uK, uG, uV} K G → Prop) :=
  Quotient (propertyIsomorphismSetoid P)

/-- Forget the condition on a class, with the quotient compatibility proved. -/
def forgetPropertyClass (P : FiniteRepresentation.{uK, uG, uV} K G → Prop) :
    IsomorphismClassesWith P → IsomorphismClasses.{uK, uG, uV} K G :=
  Quotient.map Subtype.val (fun _ _ h => h)

/-- Rank-`n` classes with a condition, such as continuity and irreducibility. -/
def IsomorphismClassesOfRankWith
    (P : FiniteRepresentation.{uK, uG, uV} K G → Prop) (n : ℕ) :=
  {c : IsomorphismClassesWith P // classRank (forgetPropertyClass P c) = n}

end FiniteRepresentation

end Langlands
