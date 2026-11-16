import Langlands.GroupScheme.AffineGmProducts
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Conjugation fixed and attracting schemes are the actual dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}
  (χ : (Gm S).toGrp ⟶ G)

/-- The actual conjugation action, viewed as an action on the underlying scheme. -/
abbrev conjugationAction : PointwiseSchemeAction (Gm S).toGrp G.X :=
  (AutomorphicAction.conjugation χ).toPointwiseSchemeAction

/-- Its actual orbit morphism is the orbit used to define the dynamic subgroups. -/
theorem conjugationAction_orbit {T : Over S} (g : T ⟶ G.X) :
    (conjugationAction χ).orbit g = orbit χ g := by
  simp only [PointwiseSchemeAction.orbit, conjugationAction,
    AutomorphicAction.toPointwiseSchemeAction_act, AutomorphicAction.conjugation_act,
    orbit]

/-- All-refinement fixedness is exactly membership in the dynamic centralizer. -/
theorem mem_centralizer_iff_conjugation_isFixed {T : Over S} (g : T ⟶ G.X) :
    g ∈ (centralizer χ).carrier T ↔ (conjugationAction χ).IsFixed g := by
  rw [mem_centralizer, PointwiseSchemeAction.isFixed_iff_universal]
  change orbit χ g = _ ↔ (conjugationAction χ).orbit g = _
  rw [conjugationAction_orbit]

/-- Attraction is the same actual affine-line orbit extension on every relative test. -/
theorem mem_parabolic_iff_conjugation_isAttracted {T : Over S} (g : T ⟶ G.X) :
    g ∈ (parabolic χ).carrier T ↔ (conjugationAction χ).IsAttracted g := by
  simp only [mem_parabolic, IsOrbitExtension, PointwiseSchemeAction.IsAttracted,
    conjugationAction_orbit]

namespace Affine

open GmCoordinateAction

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

local instance : Mono (centralizerHom χ).hom.hom :=
  (isRepresentedBy_centralizerHom χ).1

local instance : Mono (parabolicHom χ).hom.hom :=
  (isRepresentedBy_parabolicHom χ).1

/-- The existing centralizer inclusion represents all-test conjugation fixedness. -/
theorem exists_centralizer_factor_iff_fixed {T : Over (Spec R)} (g : T ⟶ G.X) :
    (∃ y : T ⟶ (centralizerScheme χ).X, y ≫ (centralizerHom χ).hom.hom = g) ↔
      (conjugationAction χ).IsFixed g := by
  rw [← mem_centralizer_iff_conjugation_isFixed,
    ← (isRepresentedBy_centralizerHom χ).2, SubgroupFunctor.mem_range]

/-- The existing parabolic inclusion represents all-test conjugation attraction. -/
theorem exists_parabolic_factor_iff_attracted {T : Over (Spec R)} (g : T ⟶ G.X) :
    (∃ y : T ⟶ (parabolicScheme χ).X, y ≫ (parabolicHom χ).hom.hom = g) ↔
      (conjugationAction χ).IsAttracted g := by
  rw [← mem_parabolic_iff_conjugation_isAttracted,
    ← (isRepresentedBy_parabolicHom χ).2, SubgroupFunctor.mem_range]

/-- Map the actual conjugation fixed scheme to the existing dynamic centralizer. -/
def fixedToCentralizer : schemeActionFixedScheme (conjugationAction χ) ⟶
    (centralizerScheme χ).X :=
  ((exists_centralizer_factor_iff_fixed χ _).mpr
    (schemeActionFixedHom_isFixed (conjugationAction χ))).choose

@[reassoc] theorem fixedToCentralizer_comp :
    fixedToCentralizer χ ≫ (centralizerHom χ).hom.hom =
      schemeActionFixedHom (conjugationAction χ) :=
  ((exists_centralizer_factor_iff_fixed χ _).mpr
    (schemeActionFixedHom_isFixed (conjugationAction χ))).choose_spec

/-- Map the existing centralizer to the actual conjugation fixed scheme. -/
def centralizerToFixed : (centralizerScheme χ).X ⟶
    schemeActionFixedScheme (conjugationAction χ) :=
  ((exists_schemeActionFixed_factor_iff_all (conjugationAction χ) _).mpr
    ((exists_centralizer_factor_iff_fixed χ _).mp
      ⟨𝟙 _, Category.id_comp _⟩)).choose

@[reassoc] theorem centralizerToFixed_comp :
    centralizerToFixed χ ≫ schemeActionFixedHom (conjugationAction χ) =
      (centralizerHom χ).hom.hom :=
  ((exists_schemeActionFixed_factor_iff_all (conjugationAction χ) _).mpr
    ((exists_centralizer_factor_iff_fixed χ _).mp
      ⟨𝟙 _, Category.id_comp _⟩)).choose_spec

/-- The fixed scheme of actual conjugation is the existing centralizer scheme. -/
def conjugationFixedIso :
    schemeActionFixedScheme (conjugationAction χ) ≅ (centralizerScheme χ).X where
  hom := fixedToCentralizer χ
  inv := centralizerToFixed χ
  hom_inv_id := by
    apply (cancel_mono (schemeActionFixedHom (conjugationAction χ))).mp
    rw [Category.assoc, centralizerToFixed_comp, fixedToCentralizer_comp,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (centralizerHom χ).hom.hom).mp
    rw [Category.assoc, fixedToCentralizer_comp, centralizerToFixed_comp,
      Category.id_comp]

/-- The fixed comparison identifies the two actual inclusions into the same group. -/
theorem conjugationFixedIso_hom_comp :
    (conjugationFixedIso χ).hom ≫ (centralizerHom χ).hom.hom =
      schemeActionFixedHom (conjugationAction χ) :=
  fixedToCentralizer_comp χ

/-- Map the actual conjugation attracting scheme to the existing dynamic parabolic. -/
def attractingToParabolic : schemeActionAttractingScheme (conjugationAction χ) ⟶
    (parabolicScheme χ).X :=
  ((exists_parabolic_factor_iff_attracted χ _).mpr
    (schemeActionAttractingHom_isAttracted (conjugationAction χ))).choose

@[reassoc] theorem attractingToParabolic_comp :
    attractingToParabolic χ ≫ (parabolicHom χ).hom.hom =
      schemeActionAttractingHom (conjugationAction χ) :=
  ((exists_parabolic_factor_iff_attracted χ _).mpr
    (schemeActionAttractingHom_isAttracted (conjugationAction χ))).choose_spec

/-- Map the existing parabolic to the actual conjugation attracting scheme. -/
def parabolicToAttracting : (parabolicScheme χ).X ⟶
    schemeActionAttractingScheme (conjugationAction χ) :=
  ((exists_schemeActionAttracting_factor_iff_all (conjugationAction χ) _).mpr
    ((exists_parabolic_factor_iff_attracted χ _).mp
      ⟨𝟙 _, Category.id_comp _⟩)).choose

@[reassoc] theorem parabolicToAttracting_comp :
    parabolicToAttracting χ ≫ schemeActionAttractingHom (conjugationAction χ) =
      (parabolicHom χ).hom.hom :=
  ((exists_schemeActionAttracting_factor_iff_all (conjugationAction χ) _).mpr
    ((exists_parabolic_factor_iff_attracted χ _).mp
      ⟨𝟙 _, Category.id_comp _⟩)).choose_spec

/-- The attracting scheme of actual conjugation is the existing dynamic parabolic scheme. -/
def conjugationAttractingIso :
    schemeActionAttractingScheme (conjugationAction χ) ≅ (parabolicScheme χ).X where
  hom := attractingToParabolic χ
  inv := parabolicToAttracting χ
  hom_inv_id := by
    apply (cancel_mono (schemeActionAttractingHom (conjugationAction χ))).mp
    rw [Category.assoc, parabolicToAttracting_comp, attractingToParabolic_comp,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (parabolicHom χ).hom.hom).mp
    rw [Category.assoc, attractingToParabolic_comp, parabolicToAttracting_comp,
      Category.id_comp]

/-- The attracting comparison identifies the actual inclusions into the same group. -/
theorem conjugationAttractingIso_hom_comp :
    (conjugationAttractingIso χ).hom ≫ (parabolicHom χ).hom.hom =
      schemeActionAttractingHom (conjugationAction χ) :=
  attractingToParabolic_comp χ

end Affine

end Langlands.GroupScheme.Dynamic
