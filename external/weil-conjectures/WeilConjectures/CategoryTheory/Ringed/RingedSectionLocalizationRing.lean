/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# The ring structure on sheafified section localization

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

/-- The localization restrictions preserve identities as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both maps extend the identity of R(U); uniqueness of localization lifts applies. -/
theorem ringedLocalizationRing_map_id (U : Cᵒᵖ) :
    ringedSectionLocalizationMap R s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMap]

/-- The localization restrictions preserve composites as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both composites extend the same restriction of R, by naturality of s;
uniqueness of localization lifts gives equality. -/
theorem ringedLocalizationRing_map_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ringedSectionLocalizationMap R s (f ≫ g) =
      (ringedSectionLocalizationMap R s g).comp (ringedSectionLocalizationMap R s f) := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMap, Functor.map_comp]

/-- The actual presheaf of commutative rings U ↦ R(U)[1/s(U)].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (ringedSectionLocalizationCarrier R s U)
  map f := CommRingCat.ofHom (ringedSectionLocalizationMap R s f)
  map_id U := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_id R s U)
  map_comp f g := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_comp R s f g)

/-- The section localization algebra maps commute with restrictions.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: each localization lift extends exactly the specified restriction map. -/
theorem ringedLocalizationRing_unit_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    R.obj.map f ≫ CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s V)) =
      CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s U)) ≫
        (ringedLocalizationRingPresheaf R s).map f := by
  ext r
  simp [ringedLocalizationRingPresheaf, ringedSectionLocalizationMap]

/-- The sectionwise algebra map into localization.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafUnit : R.obj ⟶ ringedLocalizationRingPresheaf R s where
  app U := CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s U))
  naturality _ _ f := ringedLocalizationRing_unit_naturality R s f

/-- Sheafified section localization as a sheaf of commutative rings.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRing : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (ringedLocalizationRingPresheaf R s)

/-- The canonical map of ring sheaves from R to R[1/s].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingUnit : R ⟶ ringedLocalizationRing R s :=
  ⟨ringedLocalizationRingPresheafUnit R s ≫
    toSheafify J (ringedLocalizationRingPresheaf R s)⟩

-- Budget for elaborating both ring and module sheafification constructions.
end CategoryTheory
