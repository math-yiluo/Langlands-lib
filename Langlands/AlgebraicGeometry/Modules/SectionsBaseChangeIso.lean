import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeComposition
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology

/-! # Canonical sections base change along isomorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The ordinary sections map is invertible when the scheme map is. -/
lemma isIso_sectionsBaseChangeMap_of_isIso [IsIso g] (M : X.Modules) :
    IsIso (sectionsBaseChangeMap φ f f' g w M) := by
  let : (Scheme.Modules.pushforward g).IsEquivalence :=
    (pushforwardEquivalence (asIso g)).isEquivalence_functor
  unfold sectionsBaseChangeMap
  infer_instance

/-- Package the specified ordinary sections map along a scheme isomorphism. -/
def sectionsBaseChangeIso [IsIso g] (M : X.Modules) :
    (relativeGlobalSections f).obj M ≅
      (ModuleCat.restrictScalars φ.hom).obj
        ((relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M)) := by
  let := isIso_sectionsBaseChangeMap_of_isIso φ f f' g w M
  exact asIso (sectionsBaseChangeMap φ f f' g w M)

/-- Over isomorphic base rings, an invertible ordinary sections map has an
invertible scalar-linear adjunct. -/
lemma isIso_scalarSectionsBaseChangeMap_of_isIso_sections [IsIso φ] (M : X.Modules)
    [IsIso (sectionsBaseChangeMap φ f f' g w M)] :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w M) := by
  let : (ModuleCat.restrictScalars φ.hom).IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars
      (asIso φ).commRingCatIsoToRingEquiv.toRingHom).IsEquivalence
  rw [scalarSectionsBaseChangeMap, Adjunction.homEquiv_counit]
  infer_instance

/-- The actual scalar sections map is invertible for a square of scheme and
base-ring isomorphisms. -/
lemma isIso_scalarSectionsBaseChangeMap_of_isIso [IsIso φ] [IsIso g] (M : X.Modules) :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w M) := by
  let := isIso_sectionsBaseChangeMap_of_isIso φ f f' g w M
  exact isIso_scalarSectionsBaseChangeMap_of_isIso_sections φ f f' g w M

/-- Package the actual scalar sections map for an isomorphism square. -/
def scalarSectionsBaseChangeIso [IsIso φ] [IsIso g] (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj M) ≅
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M) := by
  let := isIso_scalarSectionsBaseChangeMap_of_isIso φ f f' g w M
  exact asIso (scalarSectionsBaseChangeMap φ f f' g w M)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
