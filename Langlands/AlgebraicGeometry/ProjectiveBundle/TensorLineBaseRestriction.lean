import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrameOverlap
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.LinearSystem.ScalarTwist
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationRestriction

/-! # Line chart restriction scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.SectionClearing
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {N : S.Modules} {U V : S.Opens}

/-- The pullback trivialization corresponding to an actual line chart. -/
def openLineIso (t : N.restrict U.ι ≅ structureSheaf U.toScheme) :
    (Scheme.Modules.pullback U.ι).obj N ≅ structureSheaf U.toScheme :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm ≪≫ t

/-- Coordinates on the original chart agree with the actual pullback trivialization. -/
lemma lineCoordinates_openSection
    (t : N.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(N, U)) :
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm ≪≫ t).hom.app ⊤
      (openSection N U s) = U.topIso.inv (lineCoordinates t U le_rfl s) := by
  let θ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N
  have hid := congrArg (fun f => f.app ⊤
      ((N.restrictAppIso U.ι ⊤).inv (N.presheaf.map (eqToHom U.ι_image_top).op s)))
    θ.hom_inv_id
  change θ.inv.app ⊤ (openSection N U s) =
      (N.restrictAppIso U.ι ⊤).inv (N.presheaf.map (eqToHom U.ι_image_top).op s) at hid
  change t.hom.app ⊤ (θ.inv.app ⊤ (openSection N U s)) = _
  rw [hid]
  rw [lineCoordinates_eq_chartE]
  have hc : U.topIso.inv (chartE t U le_rfl s) =
      (structureSheaf U.toScheme).presheaf.map (homOfLE U.ι_preimage_self.ge).op
        (t.hom.app (U.ι ⁻¹ᵁ U)
          (ofImage N (N.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s))) := by
    unfold chartE
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    change S.presheaf.map (eqToHom U.ι_image_top).op
        (S.presheaf.map (homOfLE (le_image_preimage (le_refl U))).op _) =
      S.presheaf.map _ _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hc, ← hom_app_map]
  apply congrArg (fun x : Γ(N.restrict U.ι, ⊤) => t.hom.app ⊤ x)
  change N.presheaf.map (eqToHom U.ι_image_top).op s =
    N.presheaf.map (homOfLE (U.ι.image_mono U.ι_preimage_self.ge)).op
      (N.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Line coordinates on original opens commute with actual section restriction. -/
lemma lineCoordinates_restrict
    (t : N.restrict V.ι ≅ structureSheaf V.toScheme) (h : U ≤ V) (s : Γ(N, V)) :
    lineCoordinates t U h (N.presheaf.map (homOfLE h).op s) =
      S.presheaf.map (homOfLE h).op (lineCoordinates t V le_rfl s) := by
  simp only [lineCoordinates_eq_chartE]
  exact chartE_res t V U le_rfl h s

/-- The unit on the smaller open that compares two original line charts. -/
def openLineTransitionUnit
    (tV : N.restrict V.ι ≅ structureSheaf V.toScheme)
    (tU : N.restrict U.ι ≅ structureSheaf U.toScheme) (h : U ≤ V) :
    Γ(U.toScheme, ⊤)ˣ :=
  Units.map U.topIso.inv.hom.toMonoidHom (lineComparisonUnit tV tU U h le_rfl)

/-- Restrict the larger pullback trivialization to the smaller open. -/
def openLineRestrictionIso
    (tV : N.restrict V.ι ≅ structureSheaf V.toScheme) (h : U ≤ V) :
    (Scheme.Modules.pullback (S.homOfLE h)).obj
      ((Scheme.Modules.pullback V.ι).obj N) ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.pullback (S.homOfLE h)).mapIso (openLineIso tV) ≪≫
    pullbackUnitIso (S.homOfLE h)

/-- The scalar comparing original coordinates is the actual pullback restriction scalar. -/
lemma openLineIso_restrict
    (tV : N.restrict V.ι ≅ structureSheaf V.toScheme)
    (tU : N.restrict U.ι ≅ structureSheaf U.toScheme) (h : U ≤ V) :
    openLineRestrictionIso tV h ≪≫
        Scheme.Modules.unitAut (structureSheaf U.toScheme) (openLineTransitionUnit tV tU h) =
      openPullbackIso N h ≪≫ openLineIso tU := by
  let f := S.homOfLE h
  let e := openLineRestrictionIso tV h
  let s := lineBasisSection tV V le_rfl
  let q := pullbackSection f ((Scheme.Modules.pullback V.ι).obj N) (openSection N V s)
  have hev : (openLineIso tV).hom.app ⊤ (openSection N V s) =
      (1 : Γ(V.toScheme, ⊤)) := by
    dsimp only [openLineIso]
    rw [lineCoordinates_openSection, lineCoordinates_lineBasisSection]
    exact map_one V.topIso.inv.hom
  have heq : e.hom.app ⊤ q = (1 : Γ(U.toScheme, ⊤)) := by
    change ((Scheme.Modules.pullback f).map (openLineIso tV).hom ≫
      (pullbackUnitIso f).hom).app ⊤
        (pullbackSection f ((Scheme.Modules.pullback V.ι).obj N) (openSection N V s)) = (1 : Γ(U.toScheme, ⊤))
    rw [LinearSystem.pullbackMap_comp_coordinate, hev]
    have hu : pullbackSection f (structureSheaf V.toScheme) (1 : Γ(V.toScheme, ⊤)) =
        (pullbackUnitIso f).inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) :=
      (pullbackSection_eq_sectionPullback f _ _).trans (sectionPullback_unit_one f)
    rw [hu]
    exact congrArg (fun a => a.app ⊤ (1 : Γ(U.toScheme, ⊤))) (pullbackUnitIso f).inv_hom_id
  have heinv : e.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) = q := by
    rw [← heq, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id]
    rfl
  apply Iso.ext
  apply (cancel_epi e.inv).mp
  apply structureEnd_ext
  change (Scheme.Modules.unitAut (structureSheaf U.toScheme)
      (openLineTransitionUnit tV tU h)).hom.app ⊤
        (e.hom.app ⊤ (e.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)))) =
    (openLineIso tU).hom.app ⊤
      ((openPullbackIso N h).hom.app ⊤ (e.inv.app ⊤ (1 : Γ(U.toScheme, ⊤))))
  rw [heinv, heq, unitAut_hom_app_top]
  change (openLineTransitionUnit tV tU h : Γ(U.toScheme, ⊤)) * 1 = _
  rw [mul_one]
  change _ = (openLineIso tU).hom.app ⊤
    ((openPullbackIso N h).hom.app ⊤
      (pullbackSection (S.homOfLE h) ((Scheme.Modules.pullback V.ι).obj N)
        (openSection N V s)))
  rw [openPullbackIso_hom_openSection]
  dsimp only [openLineIso]
  rw [lineCoordinates_openSection,
    lineCoordinates_change tV tU h le_rfl, lineCoordinates_restrict,
    lineCoordinates_lineBasisSection, map_one, mul_one]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveBundle
