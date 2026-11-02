import Langlands.AlgebraicGeometry.Modules.FinitePresentation
import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Langlands.AlgebraicGeometry.Modules.SchemeTheoreticSupport
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The relative groupoid of flat finitely presented module families

Objects are actual locally finitely presented module sheaves flat over the
base. Finite presentation implies quasi-coherence. For a proper ambient
morphism, proper scheme-theoretic support follows after every base change.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

variable {Y B : Scheme.{u}}

/-- A locally finitely presented module sheaf flat over the actual base. -/
def IsFamily (p : Y ⟶ B) (M : Y.Modules) : Prop :=
  M.IsFinitePresentation ∧ Modules.IsFlatOver p M

/-- Family conditions are invariant under actual module isomorphisms. -/
lemma IsFamily.of_iso {p : Y ⟶ B} {M N : Y.Modules}
    (hM : IsFamily p M) (e : M ≅ N) : IsFamily p N :=
  ⟨ObjectProperty.prop_of_iso (SheafOfModules.isFinitePresentation Y.ringCatSheaf) e hM.1,
    (Modules.isFlatOver_iff_of_iso p e).mp hM.2⟩

instance (p : Y ⟶ B) : ObjectProperty.IsClosedUnderIsomorphisms (IsFamily p) where
  of_iso e hM := hM.of_iso e

/-- The full category of actual module families for a fixed structure map. -/
abbrev Family (p : Y ⟶ B) := ObjectProperty.FullSubcategory (IsFamily p)

namespace Family

variable (p : Y ⟶ B)

/-- Forget the family conditions, retaining the actual module sheaf and maps. -/
def forget : Family p ⥤ Y.Modules := ObjectProperty.ι (IsFamily p)

instance : (forget p).Full := by dsimp [forget]; infer_instance
instance : (forget p).Faithful := by dsimp [forget]; infer_instance

instance (M : Family p) : M.obj.IsFinitePresentation := M.property.1

/-- Every family is flat over its structure map. -/
lemma isFlatOver (M : Family p) : Modules.IsFlatOver p M.obj := M.property.2

/-- Finite affine sections are a consequence of the family conditions. -/
lemma hasFiniteAffineSections (M : Family p) : Modules.HasFiniteAffineSections M.obj :=
  Modules.hasFiniteAffineSections_of_isFinitePresentation M.obj

/-- Construct a family from an actual locally finitely presented module sheaf. -/
def ofModule (M : Y.Modules) [M.IsFinitePresentation] (hFlat : Modules.IsFlatOver p M) :
    Family p := ⟨M, inferInstance, hFlat⟩

/-- Transport a family across an isomorphism of actual module sheaves. -/
def ofIso (M : Family p) {N : Y.Modules} (e : M.obj ≅ N) : Family p :=
  ⟨N, M.property.of_iso e⟩

/-- The transported family is isomorphic to the original one. -/
def ofIsoIso (M : Family p) {N : Y.Modules} (e : M.obj ≅ N) : M ≅ ofIso p M e :=
  ObjectProperty.isoMk _ e

/-- A proper ambient structure map gives every family proper annihilator support. -/
lemma hasProperSupport [IsProper p] (M : Family p) :
    Modules.HasProperSupport M.obj p (hasFiniteAffineSections p M) :=
  Modules.hasProperSupport_of_isProper M.obj p (hasFiniteAffineSections p M)

end Family

variable {S X : Scheme.{u}}

/-- Actual flat finitely presented families on `T ×_S X`, with all and only
module isomorphisms as arrows. Proper support follows when `f` is proper. -/
abbrev FamilyGroupoid (f : X ⟶ S) (T : Over S) :=
  Core (Family ((Picard.relativeProjection f).app T))

namespace FamilyGroupoid

variable (f : X ⟶ S) (T : Over S)

/-- The faithful functor to actual module sheaves on the actual fibre product. -/
def forget : FamilyGroupoid f T ⥤ ((Picard.relativeSpace f).obj T).Modules :=
  Core.inclusion _ ⋙ Family.forget ((Picard.relativeProjection f).app T)

instance : (forget f T).Faithful := by dsimp [forget]; infer_instance

instance (M : FamilyGroupoid f T) : M.of.obj.IsFinitePresentation := M.of.property.1

/-- Every groupoid object is flat over the test scheme through its projection. -/
lemma isFlatOver (M : FamilyGroupoid f T) :
    Modules.IsFlatOver ((Picard.relativeProjection f).app T) M.of.obj := M.of.property.2

/-- Finite affine sections of a groupoid object's underlying module. -/
lemma hasFiniteAffineSections (M : FamilyGroupoid f T) :
    Modules.HasFiniteAffineSections M.of.obj :=
  Family.hasFiniteAffineSections _ M.of

/-- Every locally finitely presented module flat over the test scheme is an object. -/
def ofModule (M : ((Picard.relativeSpace f).obj T).Modules) [M.IsFinitePresentation]
    (hFlat : Modules.IsFlatOver ((Picard.relativeProjection f).app T) M) :
    FamilyGroupoid f T := ⟨Family.ofModule _ M hFlat⟩

/-- Arrows are exactly actual isomorphisms of the underlying module sheaves. -/
def homEquiv {M N : FamilyGroupoid f T} : (M ⟶ N) ≃ (M.of.obj ≅ N.of.obj) where
  toFun a := (Family.forget _).mapIso a.iso
  invFun e := ⟨ObjectProperty.isoMk _ e⟩
  left_inv a := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  right_inv e := by
    apply Iso.ext
    rfl

@[simp]
lemma homEquiv_hom {M N : FamilyGroupoid f T} (a : M ⟶ N) :
    (homEquiv f T a).hom = (forget f T).map a := rfl

@[simp]
lemma homEquiv_id (M : FamilyGroupoid f T) :
    homEquiv f T (𝟙 M) = Iso.refl M.of.obj := by
  apply Iso.ext
  rfl

@[simp]
lemma homEquiv_comp {M N P : FamilyGroupoid f T} (a : M ⟶ N) (b : N ⟶ P) :
    homEquiv f T (a ≫ b) = homEquiv f T a ≪≫ homEquiv f T b := by
  apply Iso.ext
  rfl

/-- Every family on every test scheme has proper scheme-theoretic support
when the original ambient morphism is proper. -/
lemma hasProperSupport [IsProper f] (M : FamilyGroupoid f T) :
    Modules.HasProperSupport M.of.obj ((Picard.relativeProjection f).app T)
      (hasFiniteAffineSections f T M) :=
  Modules.hasProperSupport_relativeSpace f T M.of.obj (hasFiniteAffineSections f T M)

/-- Proper support can equivalently be exhibited by an actual closed immersion
with the affine annihilator characterization of scheme-theoretic support. -/
lemma properSupportExists [IsProper f] (M : FamilyGroupoid f T) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ (Picard.relativeSpace f).obj T),
      Modules.IsSchemeTheoreticSupport M.of.obj ι ∧
        IsProper (ι ≫ (Picard.relativeProjection f).app T) :=
  (Modules.hasProperSupport_iff_exists M.of.obj _ (hasFiniteAffineSections f T M)).mp
    (hasProperSupport f T M)

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves
