import Langlands.Representation.Category.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Renard VI.8.1: the categories of `(G, B)`-modules and of admissible ones

A `(G, B)`-module is a smooth `B`-linear representation whose underlying `B`-module is
flat. `FamilyModule B G` is the full subcategory of the published `SmoothRep B G` on the
flat objects, so its morphisms are the `B`-linear `G`-equivariant maps.
`AdmissibleFamilyModule B G` is its full subcategory of objects whose fixed vectors under
every compact open subgroup form a finitely generated `B`-module.
-/

open CategoryTheory

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV

variable (B : Type uB) [CommRing B] (G : Type uG) [Group G] [TopologicalSpace G]

/-- Flatness of the underlying `B`-module, as a property of smooth representations. -/
def flatProperty : ObjectProperty (SmoothRep.{uB, uG, uV} B G) :=
  fun A => Module.Flat B A

/-- Renard's category `M(G, B)` of `(G, B)`-modules: smooth `B`-linear representations
on flat `B`-modules, with all `B`-linear `G`-equivariant maps. -/
abbrev FamilyModule := (flatProperty.{uB, uG, uV} B G).FullSubcategory

namespace FamilyModule

variable {B G}

instance : CoeSort (FamilyModule.{uB, uG, uV} B G) (Type uV) :=
  ⟨fun A => A.obj⟩

instance (A : FamilyModule.{uB, uG, uV} B G) : AddCommGroup A :=
  inferInstanceAs (AddCommGroup A.obj)

instance (A : FamilyModule.{uB, uG, uV} B G) : Module B A :=
  inferInstanceAs (Module B A.obj)

/-- The group action of a `(G, B)`-module. -/
abbrev representation (A : FamilyModule.{uB, uG, uV} B G) : Representation B G A :=
  A.obj.representation

theorem isSmooth (A : FamilyModule.{uB, uG, uV} B G) : IsSmooth A.representation :=
  A.obj.isSmooth

theorem flat (A : FamilyModule.{uB, uG, uV} B G) : Module.Flat B A :=
  A.property

/-- Bundle a smooth representation on a flat `B`-module as a `(G, B)`-module. -/
abbrev of {V : Type uV} [AddCommGroup V] [Module B V] (ρ : Representation B G V)
    (hρ : IsSmooth ρ) (hV : Module.Flat B V) : FamilyModule B G :=
  ⟨SmoothRep.of ρ hρ, hV⟩

/-- The fully faithful inclusion into smooth representations. -/
abbrev toSmoothRep : FamilyModule.{uB, uG, uV} B G ⥤ SmoothRep.{uB, uG, uV} B G :=
  (flatProperty B G).ι

/-- The underlying intertwiner of a morphism of `(G, B)`-modules. -/
abbrev hom {A A' : FamilyModule.{uB, uG, uV} B G} (f : A ⟶ A') :
    A.representation.IntertwiningMap A'.representation :=
  SmoothRep.hom f.hom

/-- Every `B`-linear `G`-equivariant map is a morphism of `(G, B)`-modules. -/
abbrev ofHom {A A' : FamilyModule.{uB, uG, uV} B G}
    (f : A.representation.IntertwiningMap A'.representation) : A ⟶ A' :=
  ObjectProperty.homMk (SmoothRep.ofHom f)

@[simp] theorem hom_ofHom {A A' : FamilyModule.{uB, uG, uV} B G}
    (f : A.representation.IntertwiningMap A'.representation) :
    hom (ofHom f) = f := rfl

@[simp] theorem ofHom_hom {A A' : FamilyModule.{uB, uG, uV} B G} (f : A ⟶ A') :
    ofHom (hom f) = f := rfl

end FamilyModule

/-- Renard's admissibility of a `(G, B)`-module: for every compact open subgroup `K`,
the fixed vectors `V^K` form a finitely generated `B`-module. -/
def admissibleProperty : ObjectProperty (FamilyModule.{uB, uG, uV} B G) :=
  fun A => ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    Module.Finite B (fixedVectors A.representation K.toSubgroup)

/-- The full subcategory of admissible `(G, B)`-modules. -/
abbrev AdmissibleFamilyModule := (admissibleProperty.{uB, uG, uV} B G).FullSubcategory

namespace AdmissibleFamilyModule

variable {B G}

/-- The fully faithful inclusion into `(G, B)`-modules. -/
abbrev toFamilyModule :
    AdmissibleFamilyModule.{uB, uG, uV} B G ⥤ FamilyModule.{uB, uG, uV} B G :=
  (admissibleProperty B G).ι

theorem finite_fixedVectors (A : AdmissibleFamilyModule.{uB, uG, uV} B G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Module.Finite B (fixedVectors A.obj.representation K.toSubgroup) :=
  A.property K hK

/-- Bundle an admissible `(G, B)`-module. -/
abbrev of {V : Type uV} [AddCommGroup V] [Module B V] (ρ : Representation B G V)
    (hρ : IsSmooth ρ) (hV : Module.Flat B V)
    (hK : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Module.Finite B (fixedVectors ρ K.toSubgroup)) :
    AdmissibleFamilyModule B G :=
  ⟨FamilyModule.of ρ hρ hV, hK⟩

end AdmissibleFamilyModule

end Langlands.Renard.AlgebraicFamily
