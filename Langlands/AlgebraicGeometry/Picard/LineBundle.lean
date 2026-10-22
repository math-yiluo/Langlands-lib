import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Locally free sheaves of rank one on a scheme

The local definition uses actual restriction of scheme-module sheaves. Its
comparison with tensor-invertibility belongs to a subsequent statement.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A scheme-module sheaf has rank one locally if it is isomorphic to the
structure sheaf on some open neighborhood of each point. -/
def IsLocallyFreeRankOne {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- Local rank one is preserved by an isomorphism of sheaves. -/
lemma IsLocallyFreeRankOne.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsLocallyFreeRankOne M) (e : M ≅ N) : IsLocallyFreeRankOne N := by
  intro x
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM x
  exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eU⟩⟩

/-- A line bundle here means its locally free rank-one sheaf of modules. -/
abbrev LineBundle (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsLocallyFreeRankOne (X := X))

namespace LineBundle

variable (X : Scheme.{u})

/-- Forget the local rank-one property. -/
def forget : LineBundle X ⥤ X.Modules :=
  ObjectProperty.ι (IsLocallyFreeRankOne (X := X))

/-- The trivial line bundle, with its canonical local trivializations. -/
noncomputable def trivial : LineBundle X where
  obj := SheafOfModules.unit X.ringCatSheaf
  property x := ⟨⊤, by trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

variable {X}

/-- Transport a line bundle structure across an isomorphism of module sheaves. -/
def ofIso (L : LineBundle X) {M : X.Modules} (e : L.obj ≅ M) : LineBundle X :=
  ⟨M, L.property.of_iso e⟩

/-- The original line bundle is isomorphic to its transported structure. -/
def ofIsoIso (L : LineBundle X) {M : X.Modules} (e : L.obj ≅ M) :
    L ≅ ofIso L e :=
  ObjectProperty.isoMk _ e

/-- Global sections of the underlying sheaf of a line bundle. -/
noncomputable abbrev sections (L : LineBundle X) :=
  (Scheme.Modules.presheaf L.obj).obj (Opposite.op ⊤)

/-- A chosen trivializing neighborhood of a point. -/
noncomputable def trivializingOpen (L : LineBundle X) (x : X) : X.Opens :=
  (L.property x).choose

lemma mem_trivializingOpen (L : LineBundle X) (x : X) : x ∈ L.trivializingOpen x :=
  (L.property x).choose_spec.1

/-- The chosen isomorphism trivializing a line bundle near a point. -/
noncomputable def localTrivialization (L : LineBundle X) (x : X) :
    L.obj.restrict (L.trivializingOpen x).ι ≅
      SheafOfModules.unit (L.trivializingOpen x).toScheme.ringCatSheaf :=
  (L.property x).choose_spec.2.some

end LineBundle

end Langlands.AlgebraicGeometry.Picard
