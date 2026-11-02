import Langlands.AlgebraicGeometry.LinearSystem.CoordinateIdentity
import Langlands.AlgebraicGeometry.LinearSystem.CoordinateChange
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof

/-! # The degree-one twist under linear projective actions -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

/-- Equality transport of pullbacks preserves the pulled-back section. -/
lemma pullbackCongr_coordinate {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤ (pullbackSection f M s) =
      pullbackSection g M s := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

/-- The identity pullback comparison preserves the actual section. -/
lemma pullbackId_coordinate {X : Scheme.{u}} (M : X.Modules) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackId X).hom.app M).app ⊤ (pullbackSection (𝟙 X) M s) = s := by
  apply sectionHom_injective
  rw [sectionHom_naturality, sectionHom_pullbackSection, pullbackSectionHom]
  have hn := (Scheme.Modules.pullbackId X).hom.naturality (sectionHom M s)
  simp only [Functor.id_map] at hn
  have hu : (Langlands.Scheme.Modules.pullbackUnitIso (𝟙 X)).hom =
      (Scheme.Modules.pullbackId X).hom.app (structureModule X) :=
    Langlands.Scheme.Modules.pullbackUnitIdentity X
  rw [Category.assoc, hn, ← Category.assoc, ← hu, Iso.inv_hom_id, Category.id_comp]
  rfl

/-- A family of sections whose frame opens cover determines every module-sheaf map. -/
lemma hom_ext_of_generating_sections {X : Scheme.{u}} {M N : X.Modules} {ι : Type*}
    (s : ι → GlobalSections M) (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    {f g : M ⟶ N} (h : ∀ i, f.app ⊤ (s i) = g.app ⊤ (s i)) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  apply F.eq_of_locally_eq' (fun i ↦ U ⊓ trivializationOpen M (s i)) U
    (fun _ ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, hs, inf_top_eq])
  intro i
  let V := U ⊓ trivializationOpen M (s i)
  obtain ⟨c, hc⟩ := exists_smul_sectionRes_eq
    (M := M) (s := s i) (V := V) inf_le_right
    (M.presheaf.map (homOfLE (show V ≤ U from inf_le_left)).op a)
  change N.presheaf.map (homOfLE (show V ≤ U from inf_le_left)).op (f.app U a) =
    N.presheaf.map (homOfLE (show V ≤ U from inf_le_left)).op (g.app U a)
  rw [← LineBundleDescent.hom_app_map, ← LineBundleDescent.hom_app_map, ← hc,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  simp only [sectionRes, LineBundleDescent.hom_app_map, h i]

/-- Pullback carries a covering family of line-bundle frames to a covering family. -/
lemma frameCover_pullback {X Y : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤) (f : Y ⟶ X) :
    (⨆ i, trivializationOpen ((Scheme.Modules.pullback f).obj M)
      (pullbackSection f M (s i))) = ⊤ := by
  calc
    _ = ⨆ i, f ⁻¹ᵁ trivializationOpen M (s i) := by
      apply iSup_congr
      intro i
      exact lineBundlePullbackSectionOpen X Y f ⟨M, hM⟩ (s i)
    _ = ⊤ := f.iSup_preimage_eq_top hs

/-- Pulled-back generating sections determine maps out of the pulled-back line bundle. -/
lemma hom_ext_of_pullback_generating_sections {X Y : Scheme.{u}} {L : LineBundle X}
    {N : Y.Modules} {n : ℕ} (s : Fin (n + 1) → GlobalSections L.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (f : Y ⟶ X)
    {φ ψ : (Scheme.Modules.pullback f).obj L.obj ⟶ N}
    (h : ∀ i, φ.app ⊤ (pullbackSection f L.obj (s i)) =
      ψ.app ⊤ (pullbackSection f L.obj (s i))) : φ = ψ :=
  hom_ext_of_generating_sections _
    (isOpenCover_trivializationOpen (L := (LineBundle.pullback f).obj L)
      (pullbackSections_generate (L := L) f hs)) h

/-- Evaluation of a pulled-back morphism followed by another morphism on a section. -/
lemma pullbackMap_comp_coordinate {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} {P : Y.Modules} (φ : M ⟶ N)
    (ψ : (Scheme.Modules.pullback f).obj N ⟶ P) (s : GlobalSections M) :
    ((Scheme.Modules.pullback f).map φ ≫ ψ).app ⊤ (pullbackSection f M s) =
      ψ.app ⊤ (pullbackSection f N (φ.app ⊤ s)) := by
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [← pullbackSection_naturality]

/-- Evaluation of canonical pullback composition and equality transport on a section. -/
lemma pullbackComp_comparison_coordinate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    (M : Z.Modules) {N : X.Modules} (φ : (Scheme.Modules.pullback h).obj M ⟶ N)
    (s : GlobalSections M) :
    ((Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.pullbackCongr w).hom.app M ≫ φ).app ⊤
        (pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s)) =
      φ.app ⊤ (pullbackSection h M s) := by
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackSection_comp M g f s, pullbackCongr_coordinate]

/-- Comparisons on a covering family of frames determine the pullback composition law. -/
lemma pullback_comparison_comp {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) {ι : Type*} (s : ι → GlobalSections M)
    (hs : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (a b c : X ⟶ X) (w : a ≫ b = c)
    (α : (Scheme.Modules.pullback a).obj M ⟶ M)
    (β : (Scheme.Modules.pullback b).obj M ⟶ M)
    (γ : (Scheme.Modules.pullback c).obj M ⟶ M)
    (h : ∀ i, α.app ⊤ (pullbackSection a M (β.app ⊤ (pullbackSection b M (s i)))) =
      γ.app ⊤ (pullbackSection c M (s i))) :
    (Scheme.Modules.pullback a).map β ≫ α =
      (Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M ≫ γ := by
  have hs' := frameCover_pullback hM s hs b
  have hs'' := frameCover_pullback (hM.pullback b)
    (fun i ↦ pullbackSection b M (s i)) hs' a
  apply hom_ext_of_generating_sections
    (fun i ↦ pullbackSection a ((Scheme.Modules.pullback b).obj M)
      (pullbackSection b M (s i))) hs''
  intro i
  exact (pullbackMap_comp_coordinate a β α (pullbackSection b M (s i))).trans
    ((h i).trans (pullbackComp_comparison_coordinate a b w M γ (s i)).symm)

section Polynomial

variable (R : Type u) [CommRing R] (n : ℕ)
  (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))

/-- The homogeneous coordinates transformed by an invertible linear map. -/
def changedProjectiveCoordinates :
    Fin (n + 1) → GlobalSections (twistOne R n) :=
  linearChangeSections (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (twistOneCoordinate R n) e.toLinearMap

/-- An invertible transformation preserves generation by projective coordinates. -/
lemma changedProjectiveCoordinates_generate :
    ∀ x : ProjectiveSpace R n, ∃ i,
      x ∈ nonvanishingLocus (twistOne R n) (changedProjectiveCoordinates R n e i) :=
  linearChangeSections_generate (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (twistOneCoordinate R n) e
    (projectiveCoordinates_generate R n)

/-- The changed projective coordinates define the actual polynomial linear action. -/
lemma linearSystemMap_changedProjectiveCoordinates :
    linearSystemMap (L := projectiveCoordinateLineBundle R n) (projectiveSpaceToSpec R n)
        (changedProjectiveCoordinates_generate R n e) =
      ProjectiveSpace.linearAction R n e := by
  have h := linearSystemMap_linearChange (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (twistOneCoordinate R n) e
    (projectiveCoordinates_generate R n)
  rw [linearSystemMap_projectiveCoordinates, Category.id_comp] at h
  exact h.symm

/-- The actual pullback of the degree-one twist under a polynomial linear action. -/
def linearActionTwistIso :
    (Scheme.Modules.pullback (ProjectiveSpace.linearAction R n e)).obj (twistOne R n) ≅
      twistOne R n :=
  (Scheme.Modules.pullbackCongr (linearSystemMap_changedProjectiveCoordinates R n e).symm).app
      (twistOne R n) ≪≫
    linearSystemTwistIso (L := projectiveCoordinateLineBundle R n)
      (projectiveSpaceToSpec R n) (changedProjectiveCoordinates R n e)
      (changedProjectiveCoordinates_generate R n e)

/-- The twist comparison sends each pulled-back coordinate to its actual linear combination. -/
lemma linearActionTwistIso_coordinate (i : Fin (n + 1)) :
    (linearActionTwistIso R n e).hom.app ⊤
        (pullbackSection (ProjectiveSpace.linearAction R n e) (twistOne R n)
          (twistOneCoordinate R n i)) =
      changedProjectiveCoordinates R n e i := by
  change (linearSystemTwistIso (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (changedProjectiveCoordinates R n e)
    (changedProjectiveCoordinates_generate R n e)).hom.app ⊤
      (((Scheme.Modules.pullbackCongr
        (linearSystemMap_changedProjectiveCoordinates R n e).symm).hom.app
          (twistOne R n)).app ⊤ _) = _
  rw [pullbackCongr_coordinate, linearSystemTwistIso_coordinate]

/-- At the identity coordinate map, the comparison is the canonical identity pullback. -/
lemma linearActionTwistIso_refl :
    linearActionTwistIso R n (LinearEquiv.refl R _) =
      (Scheme.Modules.pullbackCongr (ProjectiveSpace.linearAction_refl R n)).app
          (twistOne R n) ≪≫
        (Scheme.Modules.pullbackId (ProjectiveSpace R n)).app (twistOne R n) := by
  apply Iso.ext
  apply hom_ext_of_pullback_generating_sections (L := projectiveCoordinateLineBundle R n)
    (twistOneCoordinate R n) (projectiveCoordinates_generate R n)
    (ProjectiveSpace.linearAction R n (LinearEquiv.refl R _))
  intro i
  change (linearActionTwistIso R n (LinearEquiv.refl R _)).hom.app ⊤
    (pullbackSection (ProjectiveSpace.linearAction R n (LinearEquiv.refl R _))
      (twistOne R n) (twistOneCoordinate R n i)) =
    ((Scheme.Modules.pullbackId (ProjectiveSpace R n)).hom.app (twistOne R n)).app ⊤
      (((Scheme.Modules.pullbackCongr (ProjectiveSpace.linearAction_refl R n)).hom.app
        (twistOne R n)).app ⊤
          (pullbackSection (ProjectiveSpace.linearAction R n (LinearEquiv.refl R _))
            (twistOne R n) (twistOneCoordinate R n i)))
  rw [linearActionTwistIso_coordinate, pullbackCongr_coordinate, pullbackId_coordinate]
  exact congrFun (linearChangeSections_id (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (twistOneCoordinate R n)) i

/-- The comparison commutes with every further linear combination of coordinates. -/
lemma linearActionTwistIso_linearChange
    (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) (i : Fin (n + 1)) :
    (linearActionTwistIso R n e).hom.app ⊤
        (pullbackSection (ProjectiveSpace.linearAction R n e) (twistOne R n)
          (linearChangeSections (L := projectiveCoordinateLineBundle R n)
            (projectiveSpaceToSpec R n) (twistOneCoordinate R n) f i)) =
      linearChangeSections (L := projectiveCoordinateLineBundle R n)
        (projectiveSpaceToSpec R n) (changedProjectiveCoordinates R n e) f i := by
  have hc (r : R) : (ProjectiveSpace.linearAction R n e).appTop
      (Scheme.Modules.scalarsFromBase (projectiveSpaceToSpec R n) r) =
        Scheme.Modules.scalarsFromBase (projectiveSpaceToSpec R n) r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (projectiveSpaceToSpec R n).appTop ≫
        (ProjectiveSpace.linearAction R n e).appTop) r = _
    rw [← Scheme.Hom.comp_appTop, ProjectiveSpace.linearAction_comp_toSpec]
    rfl
  simp only [linearChangeSections, linComb, pullbackSection_sum, pullbackSection_smul,
    map_sum, Scheme.Modules.Hom.app_smul, hc, linearActionTwistIso_coordinate]

set_option maxHeartbeats 800000 in
/-- The comparisons satisfy the canonical composition law for pullback. -/
lemma linearActionTwistIso_comp
    (f : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    (Scheme.Modules.pullback (ProjectiveSpace.linearAction R n e)).map
        (linearActionTwistIso R n f).hom ≫ (linearActionTwistIso R n e).hom =
      (Scheme.Modules.pullbackComp (ProjectiveSpace.linearAction R n e)
        (ProjectiveSpace.linearAction R n f)).hom.app (twistOne R n) ≫
      (Scheme.Modules.pullbackCongr (ProjectiveSpace.linearAction_comp R n e f)).hom.app
        (twistOne R n) ≫ (linearActionTwistIso R n (e.trans f)).hom := by
  apply pullback_comparison_comp (projectiveSpaceTwistOneLocalFrames R n).2
    (twistOneCoordinate R n)
    (isOpenCover_trivializationOpen (L := projectiveCoordinateLineBundle R n)
      (projectiveCoordinates_generate R n))
    (ProjectiveSpace.linearAction R n e) (ProjectiveSpace.linearAction R n f)
    (ProjectiveSpace.linearAction R n (e.trans f))
    (ProjectiveSpace.linearAction_comp R n e f)
  intro i
  rw [linearActionTwistIso_coordinate, linearActionTwistIso_coordinate]
  change (linearActionTwistIso R n e).hom.app ⊤
    (pullbackSection (ProjectiveSpace.linearAction R n e) (twistOne R n)
      (linearChangeSections (L := projectiveCoordinateLineBundle R n)
        (projectiveSpaceToSpec R n) (twistOneCoordinate R n) f.toLinearMap i)) = _
  rw [linearActionTwistIso_linearChange]
  exact congrFun (linearChangeSections_comp (L := projectiveCoordinateLineBundle R n)
    (projectiveSpaceToSpec R n) (twistOneCoordinate R n) e.toLinearMap f.toLinearMap) i

end Polynomial

end Langlands.AlgebraicGeometry.LinearSystem
