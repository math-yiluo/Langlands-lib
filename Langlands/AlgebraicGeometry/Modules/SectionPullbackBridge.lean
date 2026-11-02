import Langlands.AlgebraicGeometry.SectionPullback
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackSections
import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeComposition

/-! # Linear maps on actual pulled-back global sections -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X Y : Scheme.{u}}

/-- The adjunction section of the structure module is the inverse unit comparison
applied to one. -/
lemma sectionPullback_unit_one (f : Y ⟶ X) :
    Langlands.Scheme.Modules.sectionPullback f (structureModule X) ⊤
        (1 : Γ(X, ⊤)) =
      (pullbackUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤)) := by
  have hu := pullbackUnitAdjunction Y X f
  rw [Adjunction.homEquiv_unit] at hu
  have hv := congrArg (fun a => a.app ⊤ (1 : Γ(X, ⊤))) hu
  change (pullbackUnitIso f).hom.app ⊤
      (Langlands.Scheme.Modules.sectionPullback f (structureModule X) ⊤
        (1 : Γ(X, ⊤))) = f.appTop 1 at hv
  rw [show f.appTop (1 : Γ(X, ⊤)) = (1 : Γ(Y, ⊤)) from map_one f.appTop.hom] at hv
  have hi := congrArg (fun x => (pullbackUnitIso f).inv.app ⊤ x) hv
  have hid := congrArg (fun a => a.app ⊤
      (Langlands.Scheme.Modules.sectionPullback f (structureModule X) ⊤
        (1 : Γ(X, ⊤))))
    (pullbackUnitIso f).hom_inv_id
  change (pullbackUnitIso f).inv.app ⊤
      ((pullbackUnitIso f).hom.app ⊤
        (Langlands.Scheme.Modules.sectionPullback f (structureModule X) ⊤
          (1 : Γ(X, ⊤)))) =
    Langlands.Scheme.Modules.sectionPullback f (structureModule X) ⊤
      (1 : Γ(X, ⊤)) at hid
  exact hid.symm.trans hi

/-- Pullback via the section morphism agrees with the actual adjunction-unit
section map used by scalar base change. -/
lemma pullbackSection_eq_sectionPullback (f : Y ⟶ X) (M : X.Modules)
    (s : GlobalSections M) :
    pullbackSection f M s = Langlands.Scheme.Modules.sectionPullback f M ⊤ s := by
  change ((Scheme.Modules.pullback f).map (sectionHom M s)).app ⊤
      ((pullbackUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤))) = _
  rw [← sectionPullback_unit_one]
  erw [← Langlands.Scheme.Modules.sectionPullback_naturality f
    (sectionHom M s) ⊤ (1 : Γ(X, ⊤))]
  rw [sectionHom_app_one]
  change Langlands.Scheme.Modules.sectionPullback f M ⊤
      (M.presheaf.map (𝟙 _) s) = _
  rw [M.presheaf.map_id]
  rfl

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Pushforward along equal scheme maps acts identically on top sections. -/
lemma pushforwardCongr_hom_app_top {Z W : Scheme.{u}} {a b : Z ⟶ W}
    (e : a = b) (Q : Z.Modules) (s : Γ(Q, ⊤)) :
    ((Scheme.Modules.pushforwardCongr e).hom.app Q).app ⊤ s = s := by
  subst e
  have h₁ : (Scheme.Modules.pushforwardCongr (rfl : a = a)).hom.app Q = 𝟙 _ :=
    Scheme.Modules.hom_ext _ _ fun U => by simp
  rw [h₁]
  rfl

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The canonical linear map on relative global sections is actual section
pullback, without an extra comparison hypothesis. -/
lemma relativeGlobalSectionsPullback_apply (h : Y ⟶ X) (M : X.left.Modules)
    (s : (relativeGlobalSections X.hom).obj M) :
    relativeGlobalSectionsPullback h M s =
      Langlands.SchemeModule.pullbackSection h.left M s := by
  rw [Langlands.SchemeModule.pullbackSection_eq_sectionPullback]
  unfold relativeGlobalSectionsPullback relativePushforwardSectionsIso
    relativeGlobalSectionsCompIso
  change ((Scheme.Modules.pushforwardCongr h.w).hom.app _).app ⊤
    (Langlands.Scheme.Modules.sectionPullback h.left M ⊤ s) = _
  exact pushforwardCongr_hom_app_top h.w _ _

/-- The linear subspace of sections whose actual pullback along `h` vanishes. -/
def sectionsVanishingAlong (h : Y ⟶ X) (M : X.left.Modules) :
    Submodule R ((relativeGlobalSections X.hom).obj M) :=
  LinearMap.ker (relativeGlobalSectionsPullback h M).hom

/-- Membership in the canonical kernel means actual pullback-section vanishing. -/
lemma mem_sectionsVanishingAlong_iff (h : Y ⟶ X) (M : X.left.Modules)
    (s : (relativeGlobalSections X.hom).obj M) :
    s ∈ sectionsVanishingAlong h M ↔
      Langlands.SchemeModule.pullbackSection h.left M s = 0 := by
  change relativeGlobalSectionsPullback h M s = 0 ↔ _
  rw [relativeGlobalSectionsPullback_apply]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
