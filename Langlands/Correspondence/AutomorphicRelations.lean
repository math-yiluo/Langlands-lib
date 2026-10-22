import Langlands.Group.GL.Padic
import Langlands.Correspondence.LocalConventions
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Category.Twist

/-!
# Concrete automorphic class relations for the LLC specification

The class space is the published `Langlands.SmoothDualClass` for `GL_n(F)`.
The relations compare actual representations through actual linear
equivalences. They do not assume preservation of irreducibility or admissibility.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Correspondence

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Actual irreducible admissible smooth representations of `GL_n(F)`.
The carrier universe is independent of the field universe. -/
abbrev AutomorphicObject (n : ℕ+) :=
  IrreducibleAdmissibleRep.{0, uF, uV}
    (k := ℂ) (G := GeneralLinear (n : ℕ) F.Carrier)

/-- Genuine isomorphism classes, with no finite-dimensional carrier restriction. -/
abbrev AutomorphicClass (n : ℕ+) :=
  SmoothDualClass.{0, uF, uV}
    (k := ℂ) (G := GeneralLinear (n : ℕ) F.Carrier)

/-- The existing category quotient applied to an actual object. -/
def automorphicClassOf {n : ℕ+} (A : AutomorphicObject.{uF, uV} F n) :
    AutomorphicClass.{uF, uV} F n :=
  Quotient.mk _ A

/-- The class space has actual representatives; it is not an arbitrary type. -/
theorem automorphicClass_has_representative {n : ℕ+}
    (π : AutomorphicClass.{uF, uV} F n) :
    ∃ A : AutomorphicObject.{uF, uV} F n, automorphicClassOf F A = π :=
  Quotient.exists_rep π

/-- Equality of classes is exactly genuine equivariant linear isomorphism. -/
theorem automorphicClassOf_eq_iff {n : ℕ+}
    (A B : AutomorphicObject.{uF, uV} F n) :
    automorphicClassOf F A = automorphicClassOf F B ↔
      Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  change Quotient.mk _ A = Quotient.mk _ B ↔ _
  rw [Quotient.eq]
  change Nonempty (A ≅ B) ↔ _
  constructor
  · rintro ⟨e⟩
    exact ⟨SmoothRep.equivOfIso
      ((irreducibleAdmissibleProperty (k := ℂ)
        (G := GeneralLinear (n : ℕ) F.Carrier)).ι.mapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e)⟩

/-- The actual character used to twist `GL_n(F)` is `χ ∘ det`. -/
def determinantQuasiCharacter (n : ℕ+) (χ : QuasiCharacter F) :
    GeneralLinear (n : ℕ) F.Carrier →* ℂˣ :=
  χ.toMonoidHom.comp GeneralLinear.determinant

/-- Scalar action at the actual scalar matrix, on a representative of a class.
Existence of a central character is not assumed. -/
def CentralActsBy {n : ℕ+} (π : AutomorphicClass.{uF, uV} F n)
    (a : F.Carrierˣ) (z : ℂˣ) : Prop :=
  ∃ A : AutomorphicObject.{uF, uV} F n,
    automorphicClassOf F A = π ∧
      ∀ v : A.obj,
        A.obj.representation (GeneralLinear.scalar a) v = (z : ℂ) • v

/-- A class is the actual character twist of another class.
This is a relation, not a constructor requiring an assumed closure theorem. -/
def IsCharacterTwist {n : ℕ+} (χ : QuasiCharacter F)
    (π π' : AutomorphicClass.{uF, uV} F n) : Prop :=
  ∃ A B : AutomorphicObject.{uF, uV} F n,
    automorphicClassOf F A = π ∧ automorphicClassOf F B = π' ∧
      Nonempty ((Langlands.twist (determinantQuasiCharacter F n χ)
        A.obj.representation).Equiv B.obj.representation)

/-- When `χ ∘ det` has open kernel, the relation is exactly the published
class twist map: it is realized, and its output is unique. -/
theorem isCharacterTwist_iff_eq_twist {n : ℕ+} (χ : QuasiCharacter F)
    (hχ : IsOpen ((determinantQuasiCharacter F n χ).ker :
      Set (GeneralLinear (n : ℕ) F.Carrier)))
    (π π' : AutomorphicClass.{uF, uV} F n) :
    IsCharacterTwist F χ π π' ↔
      π' = SmoothDualClass.twist (determinantQuasiCharacter F n χ) hχ π := by
  constructor
  · rintro ⟨A, B, rfl, rfl, e⟩
    exact ((automorphicClassOf_eq_iff F
      (IrreducibleAdmissibleRep.twist _ hχ A) B).mpr e).symm
  · rintro rfl
    obtain ⟨A, rfl⟩ := automorphicClass_has_representative F π
    exact ⟨A, IrreducibleAdmissibleRep.twist _ hχ A, rfl, rfl,
      ⟨equivOfRepresentationEq rfl⟩⟩

/-- A class is the actual smooth contragredient of another class.
The dual is the smooth-functional subspace of the full algebraic dual. -/
def IsSmoothDual {n : ℕ+}
    (π π' : AutomorphicClass.{uF, uV} F n) : Prop :=
  ∃ A B : AutomorphicObject.{uF, uV} F n,
    automorphicClassOf F A = π ∧ automorphicClassOf F B = π' ∧
      Nonempty ((smoothContragredient A.obj.representation).Equiv
        B.obj.representation)

/-- Rank-one reciprocity's automorphic side, via the actual determinant of `GL₁`.
Equivalence compares the scalar carrier with the object's independent carrier. -/
def IsRankOneCharacter (χ : QuasiCharacter F)
    (π : AutomorphicClass.{uF, uV} F 1) : Prop :=
  ∃ A : AutomorphicObject.{uF, uV} F 1,
    automorphicClassOf F A = π ∧
      Nonempty ((characterRepresentation (determinantQuasiCharacter F 1 χ)).Equiv
        A.obj.representation)

end Langlands.Correspondence
