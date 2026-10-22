import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.CategoryTheory.Skeletal
import Mathlib.RingTheory.FiniteLength

/-!
# Bundled smooth representations

The full subcategory of Mathlib `Rep` defined by the accepted open-stabilizer
predicate. The carrier universe remains explicit, and no topology or finite
dimensionality is required of the representation module.
-/

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands

universe uR uG uV

variable (R : Type uR) (G : Type uG) [CommRing R] [Group G]
  [TopologicalSpace G]

/-- Smoothness as a property of objects of Mathlib's representation category. -/
def smoothRepProperty : ObjectProperty (Rep.{uV} R G) :=
  fun A => IsSmooth A.ρ

/-- Smooth representations with carriers in `Type uV`. This category has objects
in `Type (max uR uG (uV + 1))`; no smallness assertion is made. -/
abbrev SmoothRep := (smoothRepProperty.{uR, uG, uV} R G).FullSubcategory

namespace SmoothRep

variable {R G}

instance : CoeSort (SmoothRep.{uR, uG, uV} R G) (Type uV) :=
  ⟨fun A => A.obj.V⟩

instance (A : SmoothRep.{uR, uG, uV} R G) : AddCommGroup A :=
  A.obj.hV1

instance (A : SmoothRep.{uR, uG, uV} R G) : Module R A :=
  A.obj.hV2

/-- The actual algebraic group action of a bundled smooth representation. -/
abbrev representation (A : SmoothRep.{uR, uG, uV} R G) :
    Representation R G A := A.obj.ρ

theorem isSmooth (A : SmoothRep.{uR, uG, uV} R G) :
    IsSmooth A.representation := A.property

/-- Bundle an algebraic representation with its proved smoothness. -/
abbrev of {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (hρ : IsSmooth ρ) : SmoothRep R G :=
  ⟨Rep.of ρ, hρ⟩

/-- The fully faithful inclusion in Mathlib's algebraic representation category. -/
abbrev toRep : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R G :=
  (smoothRepProperty R G).ι

/-- The underlying intertwiner of a morphism of smooth representations. -/
abbrev hom {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    A.representation.IntertwiningMap B.representation := f.hom.hom

/-- Every equivariant linear map is a morphism in the full smooth category. -/
abbrev ofHom {A B : SmoothRep.{uR, uG, uV} R G}
    (f : A.representation.IntertwiningMap B.representation) : A ⟶ B :=
  ObjectProperty.homMk (Rep.ofHom f)

@[simp] theorem hom_ofHom {A B : SmoothRep.{uR, uG, uV} R G}
    (f : A.representation.IntertwiningMap B.representation) :
    hom (ofHom f) = f := rfl

@[simp] theorem ofHom_hom {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    ofHom (hom f) = f := rfl

@[simp] theorem hom_id (A : SmoothRep.{uR, uG, uV} R G) :
    hom (𝟙 A) = Representation.IntertwiningMap.id A.representation := rfl

@[simp] theorem hom_comp {A B C : SmoothRep.{uR, uG, uV} R G}
    (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = (hom g).comp (hom f) := rfl

/-- Equivariant linear equivalences give isomorphisms in the smooth category. -/
noncomputable def mkIso {A B : SmoothRep.{uR, uG, uV} R G}
    (e : A.representation.Equiv B.representation) : A ≅ B :=
  ObjectProperty.isoMk (smoothRepProperty R G) (Rep.mkIso e)

/-- Recover an equivariant linear equivalence from a categorical isomorphism. -/
noncomputable def equivOfIso {A B : SmoothRep.{uR, uG, uV} R G}
    (e : A ≅ B) : A.representation.Equiv B.representation :=
  Representation.equivOfIso (toRep.mapIso e)

/-- Admissibility retains the accepted all-open-subgroups convention. -/
def IsAdmissible (A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  Langlands.IsAdmissible A.representation

/-- Finite length is finite composition length over the group algebra, not
finite dimension over the coefficient ring. -/
def HasFiniteLength (A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  IsFiniteLength R[G] A.representation.asModule

/-- A prescribed character acts by scalars on the center. Existence of such a
character is not asserted. -/
def HasCentralCharacter (A : SmoothRep.{uR, uG, uV} R G)
    (χ : Subgroup.center G →* Rˣ) : Prop :=
  ∀ (z : Subgroup.center G) (v : A),
    A.representation (z : G) v = (χ z : R) • v

variable (R G)

/-- Isomorphism classes at a fixed carrier universe. The quotient is not resized
to a small universe, and no representative or canonical quotient is selected. -/
def IsoClass := Quotient (isIsomorphicSetoid (SmoothRep.{uR, uG, uV} R G))

variable {R G}

/-- Send an actual smooth representation to its isomorphism class. -/
def isoClass (A : SmoothRep.{uR, uG, uV} R G) : IsoClass.{uR, uG, uV} R G :=
  Quotient.mk _ A

theorem isoClass_eq_iff (A B : SmoothRep.{uR, uG, uV} R G) :
    isoClass A = isoClass B ↔ Nonempty (A ≅ B) :=
  Quotient.eq

end SmoothRep

section Field

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Irreducibility is Mathlib's simplicity of the lattice of invariant submodules.
It includes nonzeroness and does not require finite dimension. -/
abbrev SmoothRep.IsIrreducible (A : SmoothRep.{uR, uG, uV} k G) : Prop :=
  Representation.IsIrreducible A.representation

/-- Actual irreducible admissible smooth representations, before passage to
isomorphism classes. -/
def irreducibleAdmissibleProperty :
    ObjectProperty (SmoothRep.{uR, uG, uV} k G) :=
  fun A => A.IsIrreducible ∧ A.IsAdmissible

/-- The full subcategory of irreducible admissible smooth representations. -/
abbrev IrreducibleAdmissibleRep :=
  (irreducibleAdmissibleProperty (k := k) (G := G)).FullSubcategory

/-- The smooth dual as isomorphism classes of actual irreducible admissible
objects with carriers in the specified universe. -/
def SmoothDualClass :=
  Quotient (isIsomorphicSetoid (IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)))

end Field
end Langlands
