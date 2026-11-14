import Langlands.GroupScheme.RelativeLevi.ModuliValue
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Representing the actual relative Levi subgroup images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}}

/-- An actual scheme represents relative Levi images when its points correspond
bijectively to those images, compatibly with their actual pullbacks. Naturality
is stated on the underlying all-test subgroup functors, without assuming a
base-change stability theorem as an additional premise. -/
structure ModuliRepresentation (P : GroupScheme S) (X : Over S) where
  pointsEquiv : ∀ T : Over S,
    (T ⟶ X) ≃ LeviImage ((GroupScheme.baseChange T.hom).obj P)
  naturality : ∀ {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ X),
    (pointsEquiv T' (a ≫ x)).val =
      ((pointsEquiv T x).val.baseChange a.left).comap
        (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) P).inv

/-- A point of a group over a scheme test is the corresponding base point of
the actual pulled-back group scheme. -/
def pulledBackPoint (P : GroupScheme S) (T : Over S) (g : T ⟶ P.X) :
    Over.mk (𝟙 T.left) ⟶ ((GroupScheme.baseChange T.hom).obj P).X :=
  Over.homMk
    (pullback.lift g.left (𝟙 T.left)
      ((Over.w g).trans (Category.id_comp T.hom).symm))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd P.X.hom T.hom = 𝟙 T.left
      exact pullback.lift_snd _ _ _)

namespace ModuliRepresentation

variable {P U : GroupScheme S} {X : Over S}

/-- The represented action is the supplied group's actual conjugation of
subgroup images on every scheme test. -/
def IsEquivariant (ρ : ModuliRepresentation P X) (r : U ⟶ P)
    [ModObj U.X X] : Prop :=
  ∀ (T : Over S) (g : T ⟶ U.X) (x : T ⟶ X),
    ρ.pointsEquiv T (g • x) =
      (ρ.pointsEquiv T x).conjugate (pulledBackPoint P T (g ≫ r.hom.hom))

/-- Read a section as a Levi subgroup image over the original base. The
canonical identity-pullback isomorphism removes the identity base change. -/
def ofSection (ρ : ModuliRepresentation P X) (s : S ⟶ X.left)
    (hs : s ≫ X.hom = 𝟙 S) : LeviImage P :=
  (ρ.pointsEquiv (Over.mk (𝟙 S)) (Over.homMk s hs)).mapIso (baseChangeIdIso P)

/-- A section gives an actual Levi inclusion representing its corresponding
subgroup image over the original base. -/
theorem ofSection_exists_presentation (ρ : ModuliRepresentation P X)
    (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S) :
    ∃ (L : GroupScheme S) (l : L ⟶ P),
      IsRelativeLeviSubgroup l ∧
        SubgroupFunctor.range l = (ρ.ofSection s hs).val :=
  (ρ.ofSection s hs).exists_presentation

/-- A section of a scheme representing the actual Levi images supplies a Levi
subgroup, with no additional existence hypothesis. -/
theorem exists_isRelativeLeviSubgroup_of_section
    (ρ : ModuliRepresentation P X) (s : S ⟶ X.left)
    (hs : s ≫ X.hom = 𝟙 S) :
    ∃ (L : GroupScheme S) (l : L ⟶ P), IsRelativeLeviSubgroup l := by
  obtain ⟨L, l, hl, _⟩ := ρ.ofSection_exists_presentation s hs
  exact ⟨L, l, hl⟩

end ModuliRepresentation
end Langlands.GroupScheme.RelativeLevi
