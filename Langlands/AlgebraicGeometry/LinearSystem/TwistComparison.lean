import Langlands.AlgebraicGeometry.LinearSystem.RelativeMorphism
import Langlands.AlgebraicGeometry.Picard.AffineNilpotentLineBundle
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Modules.SectionCoefficients
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul

/-! # Coordinate ratios and the line bundle of a linear system -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y T : Scheme.{u}}

/-- Pullback of a global section, restricted to an inverse-image open, is the
pullback-adjunction unit applied to the original local section. -/
lemma pullbackSection_restrict (f : Y ⟶ X) (M : X.Modules)
    (σ : GlobalSections M) (U : X.Opens) :
    sectionRes ((Scheme.Modules.pullback f).obj M) (pullbackSection f M σ) (f ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U
        (sectionRes M σ U) := by
  rw [pullbackSection_eq_unit]
  exact (LineBundleDescent.hom_app_map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    (le_top : U ≤ ⊤) σ).symm

/-- A local coefficient identity pulls back to the same identity with the actual
pullback of the coefficient, on the whole inverse-image open. -/
lemma pullbackSection_restrict_smul (f : Y ⟶ X) (M : X.Modules)
    (σ τ : GlobalSections M) (U : X.Opens) (a : Γ(X, U))
    (h : sectionRes M σ U = a • sectionRes M τ U) :
    sectionRes ((Scheme.Modules.pullback f).obj M) (pullbackSection f M σ) (f ⁻¹ᵁ U) =
      f.app U a • sectionRes ((Scheme.Modules.pullback f).obj M)
        (pullbackSection f M τ) (f ⁻¹ᵁ U) := by
  rw [pullbackSection_restrict, h, Scheme.Modules.Hom.app_smul,
    ← pullbackSection_restrict]
  rfl

/-- A local coefficient identity becomes a global identity after pullback by a
morphism landing in its open of definition. -/
lemma pullbackSection_smul_of_restrict (f : Y ⟶ X) (M : X.Modules)
    (σ τ : GlobalSections M) (U : X.Opens) (a : Γ(X, U))
    (h : sectionRes M σ U = a • sectionRes M τ U) (hf : ⊤ ≤ f ⁻¹ᵁ U) :
    pullbackSection f M σ = f.appLE U ⊤ hf a • pullbackSection f M τ := by
  have h' := congrArg
    (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hf).op)
    (pullbackSection_restrict_smul f M σ τ U a h)
  simpa only [Scheme.Modules.map_smul, sectionRes_res, sectionRes,
    LineBundleDescent.map_id_apply, Scheme.Hom.appLE, CommRingCat.comp_apply] using h'

/-- The pullback unit along an open subscheme is injective on sections over that open. -/
lemma pullbackUnit_open_injective (M : X.Modules) (U : X.Opens) :
    Function.Injective
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U) := by
  have : IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have he : U.ι ''ᵁ U.ι ⁻¹ᵁ U = U := by simp
    have hh : homOfLE (U.ι.image_preimage_le U) = eqToHom he :=
      Subsingleton.elim _ _
    rw [hh]
    infer_instance
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M
  change (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
    (Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) = _ at h
  have hc := congrArg (fun k ↦ k.app U) h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at hc
  rw [← hc]
  exact (ConcreteCategory.bijective_of_isIso _).injective

/-- A coefficient identity can be checked after pullback to its open subscheme. -/
lemma restrict_smul_of_open_pullback (M : X.Modules)
    (σ τ : GlobalSections M) (U : X.Opens) (a : Γ(X, U))
    (h : pullbackSection U.ι M σ =
      U.ι.appLE U ⊤ (by simp) a • pullbackSection U.ι M τ) :
    sectionRes M σ U = a • sectionRes M τ U := by
  apply pullbackUnit_open_injective M U
  rw [Scheme.Modules.Hom.app_smul, ← pullbackSection_restrict,
    ← pullbackSection_restrict]
  change sectionRes _ (pullbackSection U.ι M σ) (U.ι ⁻¹ᵁ U) =
    U.ι.app U a • sectionRes _ (pullbackSection U.ι M τ) (U.ι ⁻¹ᵁ U)
  have h' := congrArg
    (((Scheme.Modules.pullback U.ι).obj M).presheaf.map
      (homOfLE (le_top : U.ι ⁻¹ᵁ U ≤ ⊤)).op) h
  have hc : U.ι.appLE U ⊤ (by simp) ≫
      U.toScheme.presheaf.map (homOfLE (le_top : U.ι ⁻¹ᵁ U ≤ ⊤)).op = U.ι.app U := by
    rw [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
    simp
    exact Category.comp_id _
  simpa only [Scheme.Modules.map_smul, sectionRes, ← CommRingCat.comp_apply, hc] using h'

section ChartFunctions

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Pulling a degree-zero localization function back along its chart map recovers
its defining localization homomorphism. -/
lemma chartMap_appLE_awayToSection (e : A →+* Γ(T, ⊤)) {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (e t))
    (h : ⊤ ≤ chartMap 𝒜 e ht hd hu ⁻¹ᵁ Proj.basicOpen 𝒜 t) :
    Proj.awayToSection 𝒜 t ≫ (chartMap 𝒜 e ht hd hu).appLE
        (Proj.basicOpen 𝒜 t) ⊤ h = CommRingCat.ofHom (awayLift 𝒜 e t hu) := by
  let U := Proj.basicOpen 𝒜 t
  let a := Proj.basicOpenIsoSpec 𝒜 t ht hd
  let q := T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayLift 𝒜 e t hu)) ≫ a.inv
  have hi : ⊤ ≤ U.ι ⁻¹ᵁ U := by simp
  have hι : U.ι.appLE U ⊤ hi = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  have ha : Proj.awayToSection 𝒜 t ≫ U.topIso.inv =
      (Scheme.ΓSpecIso _).inv ≫ a.hom.appTop := by
    rw [show a.hom.appTop = (Proj.basicOpenToSpec 𝒜 t).app ⊤ from rfl,
      Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]
  have hq : chartMap 𝒜 e ht hd hu = q ≫ U.ι := by
    simp only [chartMap, Proj.awayι, q, a, U, Category.assoc]
  simp only [hq] at h ⊢
  rw [← Scheme.Hom.appLE_comp_appLE q U.ι U ⊤ ⊤ hi (by simp), hι,
    ← Category.assoc, ha]
  have hqt : q.appLE ⊤ ⊤ (by simp) = q.appTop := by simp [Scheme.Hom.appLE]
  rw [hqt]
  have hc : q ≫ a.hom =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayLift 𝒜 e t hu)) := by simp [q]
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, hc, Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

end ChartFunctions

section MatchingFrames

/-- A restricted global section is a local frame wherever it generates. -/
lemma isFrameOn_sectionRes (M : X.Modules) (σ : GlobalSections M) {U : X.Opens}
    (hU : U ≤ trivializationOpen M σ) :
    Scheme.Modules.IsFrameOn (sectionRes M σ U) U := by
  intro W hWU _
  rw [sectionRes_res]
  have hb := bijective_sectionHom_app_of_le M σ (hWU.trans hU)
  have he : ((sectionHom M σ).app W : Γ(X, W) → Γ(M, W)) =
      fun (a : Γ(X, W)) ↦ a • sectionRes M σ W := by
    funext a
    exact LineBundleDescent.sectionHom_app M σ W a
  rw [he] at hb
  exact hb

/-- Global sections with matching local coefficient relations determine a
section-preserving isomorphism of the actual module sheaves. -/
lemma exists_iso_of_matching_sections {M N : X.Modules} {ι : Type*}
    (s : ι → GlobalSections M) (t : ι → GlobalSections N)
    (hcov : (⨆ i, trivializationOpen M (s i)) = ⊤)
    (ht : ∀ i, trivializationOpen M (s i) ≤ trivializationOpen N (t i))
    (hcoeff : ∀ (i j : ι) (U : X.Opens), U ≤ trivializationOpen M (s i) →
      ∀ a : Γ(X, U), sectionRes M (s j) U = a • sectionRes M (s i) U →
        sectionRes N (t j) U = a • sectionRes N (t i) U) :
    ∃ e : N ≅ M, ∀ i, e.hom.app ⊤ (t i) = s i := by
  let S : ∀ W : X.Opens, Set (Γ(N, W) × Γ(M, W)) := fun W ↦
    {pq | ∃ i, W ≤ trivializationOpen M (s i) ∧
      pq = (sectionRes N (t i) W, sectionRes M (s i) W)}
  obtain ⟨e, he⟩ := Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul S
    (by
      intro W pq hpq
      obtain ⟨i, hi, rfl⟩ := hpq
      exact ⟨isFrameOn_sectionRes N _ (hi.trans (ht i)), isFrameOn_sectionRes M _ hi⟩)
    (by
      intro x
      have hx : x ∈ (⨆ i, trivializationOpen M (s i)) := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact ⟨trivializationOpen M (s i), hi, _,
        ⟨i, le_rfl, rfl⟩⟩)
    (by
      intro W W' h pq hpq
      obtain ⟨i, hi, rfl⟩ := hpq
      exact ⟨i, h.trans hi, by simp only [sectionRes_res]⟩)
    (by
      intro W pq pq' hpq hpq'
      obtain ⟨i, hi, rfl⟩ := hpq
      obtain ⟨j, _, rfl⟩ := hpq'
      obtain ⟨a, ha⟩ := exists_smul_sectionRes_eq hi (sectionRes M (s j) W)
      exact ⟨a, hcoeff i j W hi a ha.symm, ha.symm⟩)
  refine ⟨e, fun j ↦ ?_⟩
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun i ↦ trivializationOpen M (s i)) ⊤
    (fun _ ↦ homOfLE le_top) hcov.ge
  intro i
  change sectionRes M (e.hom.app ⊤ (t j)) (trivializationOpen M (s i)) =
    sectionRes M (s j) (trivializationOpen M (s i))
  rw [sectionRes, ← LineBundleDescent.hom_app_map]
  change e.hom.app (trivializationOpen M (s i))
      (sectionRes N (t j) (trivializationOpen M (s i))) =
    sectionRes M (s j) (trivializationOpen M (s i))
  obtain ⟨a, ha⟩ := exists_smul_sectionRes_eq (le_rfl :
      trivializationOpen M (s i) ≤ trivializationOpen M (s i))
    (sectionRes M (s j) (trivializationOpen M (s i)))
  rw [hcoeff i j _ le_rfl a ha.symm, Scheme.Modules.Hom.app_smul]
  rw [he _ _ ⟨i, le_rfl, rfl⟩, ha]

end MatchingFrames

section Coordinates

variable {K : Type u} [CommRing K] {L : LineBundle X} {n : ℕ}
  (p : X ⟶ Spec (CommRingCat.of K)) (s : Fin (n + 1) → GlobalSections L.obj)

/-- A coordinate ratio pulls back along a point map to the corresponding ratio
of the generating sections. -/
lemma pointMap_appLE_coordinateRatio (g : T ⟶ X) (i j : Fin (n + 1))
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s i))
    (h : ⊤ ≤ pointMap p s g i hg ⁻¹ᵁ projectiveSpaceCoordinateOpen K n i) :
    (pointMap p s g i hg).appLE (projectiveSpaceCoordinateOpen K n i) ⊤ h
        (projectiveSpaceCoordinateRatio K n i j) =
      sectionRatio L g (s j) (s i) := by
  change (Proj.awayToSection (projectiveSpaceGrading K n) (MvPolynomial.X i) ≫
    (pointMap p s g i hg).appLE (projectiveSpaceCoordinateOpen K n i) ⊤ h)
      (HomogeneousLocalization.Away.mk _ (projectiveSpace_X_mem K n i) 1
        (MvPolynomial.X j) (by simpa using projectiveSpace_X_mem K n j)) = _
  unfold ProjectiveSpace projectiveSpaceCoordinateOpen at h ⊢
  unfold pointMap at h ⊢
  rw [chartMap_appLE_awayToSection]
  change awayLift _ _ _ _
    (HomogeneousLocalization.Away.mk _ (projectiveSpace_X_mem K n i) 1
      (MvPolynomial.X j) _) = _
  rw [awayLift_mk_eq_iff]
  simp only [chartRingHom_X, sectionRatio_self hg, one_pow, mul_one]

/-- The pulled-back coordinate sections satisfy precisely the scalar identities
of the generating sections on a point-map chart. -/
lemma pointMap_pullbackCoordinate (g : T ⟶ X) (i j : Fin (n + 1))
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s i)) :
    pullbackSection (pointMap p s g i hg) (twistOne K n) (twistOneCoordinate K n j) =
      sectionRatio L g (s j) (s i) •
        pullbackSection (pointMap p s g i hg) (twistOne K n)
          (twistOneCoordinate K n i) := by
  have h : ⊤ ≤ pointMap p s g i hg ⁻¹ᵁ projectiveSpaceCoordinateOpen K n i := by
    rw [pointMap_preimage p s hg, sectionRatio_self hg, Scheme.basicOpen_one]
  rw [pullbackSection_smul_of_restrict _ _ _ _
    (projectiveSpaceCoordinateOpen K n i) (projectiveSpaceCoordinateRatio K n i j)
    (twistOneCoordinate_restrict_coordinateOpen K n i j) h,
    pointMap_appLE_coordinateRatio]

/-- Every local coefficient relation for the generating sections holds for the
pulled-back coordinate sections on the same open. -/
lemma linearSystemMap_coordinate_smul_of_restrict
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (i j : Fin (n + 1)) (U : X.Opens) (hU : U ≤ trivializationOpen L.obj (s i))
    (a : Γ(X, U)) (ha : sectionRes L.obj (s j) U = a • sectionRes L.obj (s i) U) :
    sectionRes ((Scheme.Modules.pullback (linearSystemMap p hs)).obj (twistOne K n))
        (pullbackSection (linearSystemMap p hs) (twistOne K n)
          (twistOneCoordinate K n j)) U =
      a • sectionRes ((Scheme.Modules.pullback (linearSystemMap p hs)).obj (twistOne K n))
        (pullbackSection (linearSystemMap p hs) (twistOne K n)
          (twistOneCoordinate K n i)) U := by
  apply restrict_smul_of_open_pullback
  have hgi : ∀ t, U.ι t ∈ trivializationOpen L.obj (s i) := fun t ↦ hU t.2
  have hr : sectionRatio L U.ι (s j) (s i) = U.ι.appLE U ⊤ (by simp) a := by
    apply (sectionRatio_eq_iff hgi _ _).mpr
    exact (pullbackSection_smul_of_restrict U.ι L.obj (s j) (s i) U a ha (by simp)).symm
  have : IsIso (((Scheme.Modules.pullbackComp U.ι (linearSystemMap p hs)).hom.app
      (twistOne K n)).app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp U.ι (linearSystemMap p hs)).hom.app
      (twistOne K n)).app ⊤)).injective
  rw [Scheme.Modules.Hom.app_smul, pullbackSection_comp, pullbackSection_comp,
    comp_linearSystemMap p hs U.ι i hgi, pointMap_pullbackCoordinate, hr]

/-- The actual pullback of `𝒪(1)` is isomorphic to the line bundle, preserving
every specified generating section. -/
lemma exists_linearSystemTwistIso
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    ∃ e : (Scheme.Modules.pullback (linearSystemMap p hs)).obj (twistOne K n) ≅ L.obj,
      ∀ i, e.hom.app ⊤ (pullbackSection (linearSystemMap p hs) (twistOne K n)
        (twistOneCoordinate K n i)) = s i := by
  have hcov : (⨆ i, trivializationOpen L.obj (s i)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  apply exists_iso_of_matching_sections (M := L.obj) (ι := Fin (n + 1)) s
    (fun (i : Fin (n + 1)) ↦ pullbackSection (linearSystemMap p hs) (twistOne K n)
      (twistOneCoordinate K n i)) hcov
  · intro i
    rw [lineBundlePullbackSectionOpen _ _ (linearSystemMap p hs)
      ⟨twistOne K n, (projectiveSpaceTwistOneLocalFrames K n).2⟩,
      projectiveSpaceCoordinateGenerationOpen, linearSystemMap_preimage]
  · exact linearSystemMap_coordinate_smul_of_restrict p s hs

/-- The section-preserving comparison between the pulled-back projective twist
and the original line bundle. -/
def linearSystemTwistIso
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    (Scheme.Modules.pullback (linearSystemMap p hs)).obj (twistOne K n) ≅ L.obj :=
  (exists_linearSystemTwistIso p s hs).choose

/-- The twist comparison carries each actual pulled-back coordinate section to
the corresponding specified section. -/
lemma linearSystemTwistIso_coordinate
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (i : Fin (n + 1)) :
    (linearSystemTwistIso p s hs).hom.app ⊤
        (pullbackSection (linearSystemMap p hs) (twistOne K n)
          (twistOneCoordinate K n i)) = s i :=
  (exists_linearSystemTwistIso p s hs).choose_spec i

end Coordinates

section RelativeCoordinates

variable {L : LineBundle X} {n : ℕ}
  (s : Fin (n + 1) → GlobalSections L.obj)

/-- The actual relative projective twist pulls back to the line bundle defining
the relative linear-system map. -/
def relativeLinearSystemTwistIso {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    (Scheme.Modules.pullback (relativeLinearSystemMap p hs)).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅ L.obj :=
  (Scheme.Modules.pullbackComp (relativeLinearSystemMap p hs)
      (RelativeProjectiveSpace.toIntegral S n)).app
      (RelativeProjectiveSpace.integralTwistOne n).obj ≪≫
    (Scheme.Modules.pullbackCongr (relativeLinearSystemMap_toIntegral p hs)).app
      (RelativeProjectiveSpace.integralTwistOne n).obj ≪≫
    linearSystemTwistIso (specULiftZIsTerminal.from X) s hs

/-- The relative twist comparison preserves every actual coordinate section. -/
lemma relativeLinearSystemTwistIso_coordinate {S : Scheme.{u}} (p : X ⟶ S)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) (i : Fin (n + 1)) :
    (relativeLinearSystemTwistIso s p hs).hom.app ⊤
        (pullbackSection (relativeLinearSystemMap p hs)
          (RelativeProjectiveSpace.twistOne S n).obj
          (RelativeProjectiveSpace.twistOneCoordinate S n i)) = s i := by
  change (linearSystemTwistIso (specULiftZIsTerminal.from X) s hs).hom.app ⊤
    (((Scheme.Modules.pullbackComp (relativeLinearSystemMap p hs)
        (RelativeProjectiveSpace.toIntegral S n)).hom.app
        (RelativeProjectiveSpace.integralTwistOne n).obj ≫
      (Scheme.Modules.pullbackCongr (relativeLinearSystemMap_toIntegral p hs)).hom.app
        (RelativeProjectiveSpace.integralTwistOne n).obj).app ⊤
      (pullbackSection (relativeLinearSystemMap p hs)
        ((Scheme.Modules.pullback (RelativeProjectiveSpace.toIntegral S n)).obj
          (RelativeProjectiveSpace.integralTwistOne n).obj)
        (pullbackSection (RelativeProjectiveSpace.toIntegral S n)
          (RelativeProjectiveSpace.integralTwistOne n).obj
          (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) n i)))) = s i
  rw [RelativeProjectiveSpace.pullbackSection_comp_eq]
  exact linearSystemTwistIso_coordinate _ s hs i

end RelativeCoordinates

end Langlands.AlgebraicGeometry.LinearSystem
