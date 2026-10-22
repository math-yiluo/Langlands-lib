import Langlands.Representation.Category.Basic
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# Character twists of bundled smooth representations

An open-kernel character twists the actual action on the same carrier. The
twist is an endofunctor of the smooth category, preserves admissibility and
irreducibility, and descends to isomorphism classes with the group laws.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV

/-- An equality of actions on one carrier, as an actual equivalence. -/
def equivOfRepresentationEq {R : Type uR} {G : Type uG} {V : Type uV}
    [CommRing R] [Group G] [AddCommGroup V] [Module R V]
    {ρ σ : Representation R G V} (h : ρ = σ) : ρ.Equiv σ where
  toLinearEquiv := LinearEquiv.refl R V
  isIntertwining' g := by
    subst h
    rfl

namespace SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

/-- The twist of a bundled smooth representation by an open-kernel character. -/
abbrev twist (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) : SmoothRep.{uR, uG, uV} R G :=
  of (Langlands.twist χ A.representation)
    ((isSmooth_twist_iff χ A.representation hχ).mpr A.isSmooth)

@[simp]
theorem twist_representation (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    (A.twist χ hχ).representation = Langlands.twist χ A.representation := rfl

/-- Twisting is an endofunctor; it leaves the underlying linear maps unchanged. -/
def twistFunctor (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R G where
  obj A := A.twist χ hχ
  map f := ofHom (twistIntertwining χ (hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem twistFunctor_obj (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    (twistFunctor χ hχ).obj A = A.twist χ hχ := rfl

theorem hom_twistFunctor_map (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    hom ((twistFunctor χ hχ).map f) = twistIntertwining χ (hom f) := rfl

/-- Twisting by the trivial character is the identity, as an actual isomorphism. -/
def twistOneIso (h1 : IsOpen ((1 : G →* Rˣ).ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) : A.twist 1 h1 ≅ A :=
  mkIso (equivOfRepresentationEq (twist_one A.representation))

/-- Successive twists compose to the twist by the product character. -/
def twistTwistIso (χ η : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) (hχη : IsOpen ((χ * η).ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    (A.twist η hη).twist χ hχ ≅ A.twist (χ * η) hχη :=
  mkIso (equivOfRepresentationEq (twist_twist χ η A.representation))

/-- An isomorphism of smooth representations gives an isomorphism of twists. -/
def twistIso (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    {A B : SmoothRep.{uR, uG, uV} R G} (e : A ≅ B) : A.twist χ hχ ≅ B.twist χ hχ :=
  (twistFunctor χ hχ).mapIso e

theorem isAdmissible_twist_iff [IsNoetherianRing R] (χ : G →* Rˣ)
    (hχ : IsOpen (χ.ker : Set G)) (A : SmoothRep.{uR, uG, uV} R G) :
    (A.twist χ hχ).IsAdmissible ↔ A.IsAdmissible :=
  Langlands.isAdmissible_twist_iff χ A.representation hχ

/-- Twisting on isomorphism classes of smooth representations. -/
def IsoClass.twist (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsoClass.{uR, uG, uV} R G → IsoClass.{uR, uG, uV} R G :=
  Quotient.map (fun A => A.twist χ hχ) (fun _ _ ⟨e⟩ => ⟨twistIso χ hχ e⟩)

@[simp]
theorem IsoClass.twist_isoClass (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    IsoClass.twist χ hχ (isoClass A) = isoClass (A.twist χ hχ) := rfl

theorem IsoClass.twist_one (h1 : IsOpen ((1 : G →* Rˣ).ker : Set G))
    (a : IsoClass.{uR, uG, uV} R G) : IsoClass.twist 1 h1 a = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨twistOneIso h1 A⟩

theorem IsoClass.twist_twist (χ η : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) (hχη : IsOpen ((χ * η).ker : Set G))
    (a : IsoClass.{uR, uG, uV} R G) :
    IsoClass.twist χ hχ (IsoClass.twist η hη a) = IsoClass.twist (χ * η) hχη a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨twistTwistIso χ η hχ hη hχη A⟩

end SmoothRep

section Field

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

theorem SmoothRep.isIrreducible_twist_iff (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} k G) :
    (A.twist χ hχ).IsIrreducible ↔ A.IsIrreducible :=
  Langlands.isIrreducible_twist_iff χ A.representation

namespace IrreducibleAdmissibleRep

/-- The twist of an actual irreducible admissible object. -/
def twist (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G) :=
  ⟨A.obj.twist χ hχ, (SmoothRep.isIrreducible_twist_iff χ hχ A.obj).mpr A.property.1,
    (SmoothRep.isAdmissible_twist_iff χ hχ A.obj).mpr A.property.2⟩

/-- Twisting restricted to the full subcategory of irreducible admissible objects. -/
def twistFunctor (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G) ⥤
      IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G) :=
  ObjectProperty.lift _
    ((irreducibleAdmissibleProperty (k := k) (G := G)).ι ⋙ SmoothRep.twistFunctor χ hχ)
    (fun A => (twist χ hχ A).property)

@[simp]
theorem twistFunctor_obj (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    (twistFunctor χ hχ).obj A = twist χ hχ A := rfl

/-- Lift an isomorphism of underlying smooth objects to the full subcategory. -/
def isoMk {A B : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)}
    (e : A.obj ≅ B.obj) : A ≅ B :=
  ObjectProperty.isoMk _ e

end IrreducibleAdmissibleRep

/-- Twisting on the smooth dual: classes of irreducible admissible objects. -/
def SmoothDualClass.twist (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G)) :
    SmoothDualClass.{uR, uG, uV} (k := k) (G := G) →
      SmoothDualClass.{uR, uG, uV} (k := k) (G := G) :=
  Quotient.map (IrreducibleAdmissibleRep.twist χ hχ)
    (fun _ _ ⟨e⟩ => ⟨(IrreducibleAdmissibleRep.twistFunctor χ hχ).mapIso e⟩)

@[simp]
theorem SmoothDualClass.twist_mk (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    SmoothDualClass.twist χ hχ (Quotient.mk _ A) =
      Quotient.mk _ (IrreducibleAdmissibleRep.twist χ hχ A) := rfl

theorem SmoothDualClass.twist_one (h1 : IsOpen ((1 : G →* kˣ).ker : Set G))
    (a : SmoothDualClass.{uR, uG, uV} (k := k) (G := G)) :
    SmoothDualClass.twist 1 h1 a = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.twistOneIso h1 A.obj)⟩

theorem SmoothDualClass.twist_twist (χ η : G →* kˣ) (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) (hχη : IsOpen ((χ * η).ker : Set G))
    (a : SmoothDualClass.{uR, uG, uV} (k := k) (G := G)) :
    SmoothDualClass.twist χ hχ (SmoothDualClass.twist η hη a) =
      SmoothDualClass.twist (χ * η) hχη a := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound
      ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.twistTwistIso χ η hχ hη hχη A.obj)⟩

end Field

end Langlands
