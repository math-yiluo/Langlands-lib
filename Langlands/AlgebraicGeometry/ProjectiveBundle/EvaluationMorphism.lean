import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationCoordinates
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
import Langlands.AlgebraicGeometry.LinearSystem.RelativeLinearActionTwist

/-! # Actual local projective morphisms from frame evaluations -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- The actual relative linear-system map transforms by the coefficient action. -/
lemma relativeLinearSystemMap_linearChange {K : Type u} [CommRing K]
    {X S : Scheme.{u}} (p : X ⟶ S) (a : S ⟶ Spec (CommRingCat.of K))
    {L : LineBundle X} {n : ℕ} (s : Fin (n + 1) → GlobalSections L.obj)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.linearAction a e =
      relativeLinearSystemMap p (linearChangeSections_generate (p ≫ a) s e hs) := by
  apply RelativeProjectiveSpace.hom_ext_toPolynomial a
  · simp
  · rw [Category.assoc, RelativeProjectiveSpace.linearAction_toPolynomial,
      ← Category.assoc, relativeLinearSystemMap_toPolynomial,
      relativeLinearSystemMap_toPolynomial]
    exact linearSystemMap_linearChange (p ≫ a) s e hs

/-- Global functions act through the actual structure-sheaf map of the morphism. -/
lemma scalarsFromBase_comp_toSpecΓ {X S : Scheme.{u}} (p : X ⟶ S) :
    Scheme.Modules.scalarsFromBase (p ≫ S.toSpecΓ) = p.appTop.hom := by
  rw [scalarsFromBase_comp]
  simp [Scheme.Modules.scalarsFromBase, Scheme.toSpecΓ_appTop]

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

open Langlands.AlgebraicGeometry.LinearSystem

variable {X S : Scheme.{u}}

/-- Regard a section over an actual open as a global section of the actual pullback. -/
def openSection (N : X.Modules) (A : X.Opens) :
    Γ(N, A) →+ GlobalSections ((Scheme.Modules.pullback A.ι).obj N) :=
  (((Scheme.Modules.restrictFunctorIsoPullback A.ι).hom.app N).app ⊤).hom.comp
    ((N.restrictAppIso A.ι ⊤).inv.hom.comp
      (N.presheaf.map (eqToHom A.ι_image_top).op).hom)

/-- The conversion to an open subscheme transports precisely its genuine scalars. -/
lemma openSection_smul (N : X.Modules) (A : X.Opens) (r : Γ(X, A)) (s : Γ(N, A)) :
    openSection N A (r • s) = A.topIso.inv r • openSection N A s := by
  change (((Scheme.Modules.restrictFunctorIsoPullback A.ι).hom.app N).app ⊤)
      ((N.restrictAppIso A.ι ⊤).inv (N.presheaf.map _ (r • s))) = _
  rw [Scheme.Modules.map_smul N (eqToHom A.ι_image_top) r s,
    Scheme.Modules.smul_restrictAppIso_inv_apply]
  rw [Scheme.Modules.Hom.app_smul]
  simp [Scheme.Opens.ι_appIso, Scheme.Opens.topIso, openSection]
  rfl

variable (p : X ⟶ S) {M : S.Modules} (L : LineBundle X) {n : ℕ}
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)

/-- The actual base morphism on the inverse-image open. -/
abbrev evaluationBase (W : S.Opens) :
    (p ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  p.resLE W (p ⁻¹ᵁ W) le_rfl

/-- The canonical scalar square for the actual morphism between open subschemes. -/
lemma evaluationBase_scalar (W : S.Opens) (r : Γ(S, W)) :
    (evaluationBase p W).appTop (W.topIso.inv r) =
      (p ⁻¹ᵁ W).topIso.inv (p.app W r) := by
  change (evaluationBase p W).app ⊤ (W.topIso.inv r) = _
  rw [Scheme.Hom.resLE_app_top]
  change (p ⁻¹ᵁ W).topIso.inv
    (p.appLE W (p ⁻¹ᵁ W) le_rfl (W.topIso.hom (W.topIso.inv r))) = _
  rw [Iso.inv_hom_id_apply]
  rw [Scheme.Hom.appLE_eq_app]

/-- The genuine line bundle on the inverse-image open. -/
abbrev evaluationLineBundle (W : S.Opens) : LineBundle (p ⁻¹ᵁ W).toScheme :=
  (LineBundle.pullback (p ⁻¹ᵁ W).ι).obj L

/-- The actual global sections defining the local projective evaluation map. -/
def localEvaluationSections {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U) :
    Fin (n + 1) → GlobalSections (evaluationLineBundle p L W).obj :=
  fun i => openSection L.obj (p ⁻¹ᵁ W) (evaluationSections p ev e W h i)

/-- Evaluation on two actual frames gives exactly their dual-coordinate change. -/
lemma localEvaluationSections_change {U V W : S.Opens}
    (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    localEvaluationSections p L ev f W hWV =
      linearChangeSections (L := evaluationLineBundle p L W)
        (evaluationBase p W ≫ W.toScheme.toSpecΓ)
        (localEvaluationSections p L ev e W hWU)
        (coordinatesOnOpen n W (e.dual.change f.dual W hWU hWV)).toLinearMap := by
  funext i
  dsimp only [localEvaluationSections]
  rw [evaluationSections_change p ev e f hWU hWV i, map_sum]
  change (∑ j, openSection L.obj (p ⁻¹ᵁ W)
      (p.app W (e.dual.change f.dual W hWU hWV (Pi.single j 1) i) •
        evaluationSections p ev e W hWU j)) =
    ∑ j, Scheme.Modules.scalarsFromBase (evaluationBase p W ≫ W.toScheme.toSpecΓ)
      (ProjectiveSpace.coordinateBaseChange n W.topIso.inv.hom
        (e.dual.change f.dual W hWU hWV) (Pi.single j 1) i) •
      openSection L.obj (p ⁻¹ᵁ W) (evaluationSections p ev e W hWU j)
  simp only [openSection_smul, ProjectiveSpace.coordinateBaseChange_coeff,
    scalarsFromBase_comp_toSpecΓ, evaluationBase_scalar]

/-- Changing the actual frame preserves pointwise generation of evaluation sections. -/
lemma localEvaluationSections_change_generate {U V W : S.Opens}
    (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W hWU i)) :
    ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev f W hWV i) := by
  rw [localEvaluationSections_change p L ev e f hWU hWV]
  exact linearChangeSections_generate _ _
    (coordinatesOnOpen n W (e.dual.change f.dual W hWU hWV)) hs

/-- The actual local projective morphism defined by a frame evaluation. -/
def localEvaluationMap {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i)) :
    (p ⁻¹ᵁ W).toScheme ⟶ RelativeProjectiveSpace W.toScheme n :=
  relativeLinearSystemMap (evaluationBase p W) hs

@[reassoc (attr := simp)]
lemma localEvaluationMap_toBase {U : S.Opens} (e : LocalFrame M n U)
    (W : S.Opens) (h : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W h i)) :
    localEvaluationMap p L ev e W h hs ≫ RelativeProjectiveSpace.toBase W.toScheme n =
      evaluationBase p W :=
  relativeLinearSystemMap_toBase _ hs

/-- The local morphisms from actual evaluations obey the actual frame action. -/
lemma localEvaluationMap_change {U V W : S.Opens}
    (e : LocalFrame M n U) (f : LocalFrame M n V)
    (hWU : W ≤ U) (hWV : W ≤ V)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W hWU i)) :
    localEvaluationMap p L ev e W hWU hs ≫
        RelativeProjectiveSpace.globalLinearAction n
          (coordinatesOnOpen n W (e.dual.change f.dual W hWU hWV)) =
      localEvaluationMap p L ev f W hWV
        (localEvaluationSections_change_generate p L ev e f hWU hWV hs) := by
  dsimp only [localEvaluationMap, RelativeProjectiveSpace.globalLinearAction]
  have h := relativeLinearSystemMap_linearChange (evaluationBase p W)
    W.toScheme.toSpecΓ (localEvaluationSections p L ev e W hWU)
    (coordinatesOnOpen n W (e.dual.change f.dual W hWU hWV)) hs
  simpa only [← localEvaluationSections_change p L ev e f hWU hWV] using h

end Langlands.AlgebraicGeometry.ProjectiveBundle
