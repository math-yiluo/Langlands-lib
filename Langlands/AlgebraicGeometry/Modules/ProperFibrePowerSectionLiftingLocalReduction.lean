import Langlands.AlgebraicGeometry.Modules.ProperFibrePowerSectionLiftingStatement
import Langlands.AlgebraicGeometry.Modules.QCQSLineBundleSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.LocalizationSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSectionBridge
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Flat

/-! # Reduction of fibre power section lifting to a local base -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

/-- Section lifting from the closed fibre of a proper scheme over a noetherian
local ring. The closed fibre is any base change `Z` of `Spec (A/𝔪) → Spec A`; if
the pullback of `L` to `Z` is ample, then every global section of every
sufficiently high power of `L` on `Z` is the pullback of a global section on `X`. -/
def LocalClosedFibrePowerSectionLifting : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] [IsLocalRing A]
    (X Z : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f] (L : LineBundle X)
    (i : Z ⟶ X) (g : Z ⟶ Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))),
    IsPullback i g f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) →
    ((LineBundle.pullback i).obj L).IsAmple →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        Function.Surjective (sectionPullback i (tensorPow L.obj n) ⊤)

namespace LocalReduction

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
  (s : S) (hs : s ∈ U)

/-- The base change of `f` to the canonical chart of an affine open. -/
abbrev chart := pullback f hU.fromSpec

/-- The base change of `f` to the spectrum of the local ring at `s`. -/
abbrev localBase := pullback (pullback.snd f hU.fromSpec) (Spec.map (S.presheaf.germ U s hs))

/-- The projection of the local base change to `X`. -/
abbrev localToX : localBase f hU s hs ⟶ X :=
  pullback.fst _ _ ≫ pullback.fst f hU.fromSpec

/-- The structure morphism of the local base change. -/
abbrev localHom : localBase f hU s hs ⟶ Spec (S.presheaf.stalk s) := pullback.snd _ _

lemma isPullback_local :
    IsPullback (localToX f hU s hs) (localHom f hU s hs) f
      (Spec.map (S.presheaf.germ U s hs) ≫ hU.fromSpec) :=
  (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)

lemma fromSpecResidueField_eq :
    S.fromSpecResidueField s =
      Spec.map (S.residue s) ≫ Spec.map (S.presheaf.germ U s hs) ≫ hU.fromSpec := by
  rw [Scheme.fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hs]
  rfl

/-- The actual fibre of `f` over `s`, mapped into the local base change. -/
def fibreToLocal : f.fiber s ⟶ localBase f hU s hs :=
  (isPullback_local f hU s hs).lift (f.fiberι s)
    (f.fiberToSpecResidueField s ≫ Spec.map (S.residue s)) (by
      rw [Category.assoc, ← fromSpecResidueField_eq hU s hs]
      exact f.fiber_fac s)

@[reassoc (attr := simp)]
lemma fibreToLocal_toX : fibreToLocal f hU s hs ≫ localToX f hU s hs = f.fiberι s :=
  (isPullback_local f hU s hs).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fibreToLocal_hom :
    fibreToLocal f hU s hs ≫ localHom f hU s hs =
      f.fiberToSpecResidueField s ≫ Spec.map (S.residue s) :=
  (isPullback_local f hU s hs).lift_snd _ _ _

/-- The actual fibre of `f` over `s` is the closed fibre of the local base change. -/
lemma isPullback_fibreToLocal :
    IsPullback (fibreToLocal f hU s hs) (f.fiberToSpecResidueField s)
      (localHom f hU s hs) (Spec.map (S.residue s)) := by
  refine IsPullback.of_right ?_ (fibreToLocal_hom f hU s hs) (isPullback_local f hU s hs)
  rw [fibreToLocal_toX, ← fromSpecResidueField_eq hU s hs]
  exact IsPullback.of_hasPullback f (S.fromSpecResidueField s)

lemma isPullback_fibreToLocal_quotient :
    IsPullback (fibreToLocal f hU s hs) (f.fiberToSpecResidueField s)
      (localHom f hU s hs)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s))))) :=
  isPullback_fibreToLocal f hU s hs

instance [IsProper f] : IsProper (localHom f hU s hs) := by
  dsimp only [localHom]
  infer_instance

/-- The projection of the chart base change to `X`. -/
abbrev chartToX : chart f hU ⟶ X := pullback.fst f hU.fromSpec

/-- The structure morphism of the chart base change. -/
abbrev chartHom : chart f hU ⟶ Spec Γ(S, U) := pullback.snd f hU.fromSpec

/-- The projection of the local base change to the chart base change. -/
abbrev localToChart : localBase f hU s hs ⟶ chart f hU := pullback.fst _ _

lemma localToX_comp :
    localToX f hU s hs ≫ f = localHom f hU s hs ≫ S.fromSpecStalk s := by
  rw [(isPullback_local f hU s hs).w, ← hU.fromSpecStalk_eq_fromSpecStalk hs]
  rfl

/-- Every point of the local base change lies over every neighbourhood of `s`. -/
lemma top_le_localToX_preimage {V : S.Opens} (hsV : s ∈ V) :
    ⊤ ≤ localToX f hU s hs ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  intro x _
  change f (localToX f hU s hs x) ∈ V
  have h : f (localToX f hU s hs x) = S.fromSpecStalk s (localHom f hU s hs x) := by
    rw [← Scheme.Hom.comp_apply, localToX_comp, Scheme.Hom.comp_apply]
  have hsp : S.fromSpecStalk s (localHom f hU s hs x) ⤳ s := by
    have hm : S.fromSpecStalk s (localHom f hU s hs x) ∈ Set.range (S.fromSpecStalk s) :=
      Set.mem_range_self _
    rwa [Scheme.range_fromSpecStalk] at hm
  rw [h]
  exact hsp.mem_open V.isOpen hsV

lemma appLE_congr_hom {T Y : Scheme.{u}} {g g' : T ⟶ Y} (hg : g = g') {W : Y.Opens}
    {W' : T.Opens} (e : W' ≤ g ⁻¹ᵁ W) (e' : W' ≤ g' ⁻¹ᵁ W) :
    g.appLE W W' e = g'.appLE W W' e' := by
  subst hg
  rfl

/-- The global ring map of a scheme over `Spec 𝒪_{S,s}` restricts the germ map. -/
lemma appLE_eq_germ_comp_structureRingHom {T : Scheme.{u}} (g : T ⟶ S)
    (q : T ⟶ Spec (S.presheaf.stalk s)) (hg : g = q ≫ hU.fromSpecStalk hs)
    (e : ⊤ ≤ g ⁻¹ᵁ U) :
    g.appLE U ⊤ e = S.presheaf.germ U s hs ≫ DerivedSections.structureRingHom q := by
  have h1 : (⊤ : (Spec Γ(S, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h4 : (⊤ : T.Opens) ≤ (q ≫ Spec.map (S.presheaf.germ U s hs)) ⁻¹ᵁ ⊤ := le_top
  have h2 : (⊤ : (Spec (S.presheaf.stalk s)).Opens) ≤
      Spec.map (S.presheaf.germ U s hs) ⁻¹ᵁ ⊤ := le_top
  have h3 : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤ := le_top
  calc g.appLE U ⊤ e
      = ((q ≫ Spec.map (S.presheaf.germ U s hs)) ≫ hU.fromSpec).appLE U ⊤
          (h4.trans ((TopologicalSpace.Opens.map (q ≫ Spec.map _).base).map
            (homOfLE h1)).le) :=
        appLE_congr_hom (by rw [hg, IsAffineOpen.fromSpecStalk, Category.assoc]) _ _
    _ = hU.fromSpec.appLE U ⊤ h1 ≫ (q ≫ Spec.map (S.presheaf.germ U s hs)).appLE ⊤ ⊤ h4 :=
        (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    _ = (Scheme.ΓSpecIso Γ(S, U)).inv ≫
          ((Spec.map (S.presheaf.germ U s hs)).appLE ⊤ ⊤ h2 ≫ q.appLE ⊤ ⊤ h3) := by
        rw [isAffineOpen_fromSpec_appLE_top, Scheme.Hom.appLE_comp_appLE]
    _ = (Scheme.ΓSpecIso Γ(S, U)).inv ≫
          ((Spec.map (S.presheaf.germ U s hs)).appTop ≫ q.appTop) := by
        congr 2; exact Scheme.Hom.appLE_eq_app _
    _ = S.presheaf.germ U s hs ≫ DerivedSections.structureRingHom q := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
        rfl

section Descent

variable [QuasiCompact f] [QuasiSeparated f]

omit [QuasiCompact f] [QuasiSeparated f] in
instance : IsAffineHom (localToChart f hU s hs) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _
    (inferInstance : IsAffineHom (Spec.map (S.presheaf.germ U s hs)))

instance : CompactSpace (chart f hU) :=
  QuasiCompact.compactSpace_of_compactSpace (chartHom f hU)

instance : QuasiSeparatedSpace (chart f hU) :=
  quasiSeparatedSpace_of_quasiSeparated (chartHom f hU)

omit [QuasiCompact f] [QuasiSeparated f] in
lemma chartToX_preimage : chartToX f hU ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
    hU.fromSpec_preimage_self]
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
lemma preimage_le_chartToX_opensRange : f ⁻¹ᵁ U ≤ (chartToX f hU).opensRange := by
  rw [Scheme.Hom.opensRange_pullbackFst, hU.opensRange_fromSpec]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The ring identity behind descent: restricting `a` to an open `V ⊆ U`, pulling back to
`f ⁻¹ᵁ V` and then to the local base change agrees with the image of the germ of `a`. -/
lemma localToX_appLE_app_map {V : S.Opens} (hVU : V ≤ U) (hsV : s ∈ V) (a : Γ(S, U)) :
    (localToX f hU s hs).appLE (f ⁻¹ᵁ V) ⊤ (top_le_localToX_preimage f hU s hs hsV)
        (f.app V (S.presheaf.map (homOfLE hVU).op a)) =
      (DerivedSections.structureRingHom (localHom f hU s hs)).hom
        (S.presheaf.germ U s hs a) := by
  have hg : localToX f hU s hs ≫ f = localHom f hU s hs ≫ hU.fromSpecStalk hs := by
    rw [localToX_comp, hU.fromSpecStalk_eq_fromSpecStalk]
  have h := appLE_eq_germ_comp_structureRingHom hU s hs (localToX f hU s hs ≫ f)
    (localHom f hU s hs) hg (top_le_localToX_preimage f hU s hs hs)
  have key : S.presheaf.map (homOfLE hVU).op ≫ f.app V ≫
      (localToX f hU s hs).appLE (f ⁻¹ᵁ V) ⊤ (top_le_localToX_preimage f hU s hs hsV) =
        S.presheaf.germ U s hs ≫ DerivedSections.structureRingHom (localHom f hU s hs) := by
    rw [← h, f.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.map_appLE]
  exact congrArg (fun φ => φ.hom a) key

/-- A global section of a line bundle pulled back to the base change of a quasi-compact
quasi-separated morphism to `Spec 𝒪_{S,s}` comes from a section over the inverse image of an
affine neighbourhood of `s`. -/
lemma exists_sectionPullbackLE_eq (M : LineBundle X)
    (y : Γ((Scheme.Modules.pullback (localToX f hU s hs)).obj M.obj, ⊤)) :
    ∃ (V : S.Opens) (hsV : s ∈ V), IsAffineOpen V ∧
      ∃ τ : Γ(M.obj, f ⁻¹ᵁ V),
        sectionPullbackLE (localToX f hU s hs) M.obj
          (top_le_localToX_preimage f hU s hs hsV) τ = y := by
  let : Algebra Γ(S, U) (S.presheaf.stalk s) := (S.presheaf.germ U s hs).hom.toAlgebra
  let P := (hU.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl
  have hloc : IsLocalization P (S.presheaf.stalk s) := hU.isLocalization_stalk ⟨s, hs⟩
  let φ : Γ(S, U) ⟶ S.presheaf.stalk s :=
    CommRingCat.ofHom (algebraMap Γ(S, U) (S.presheaf.stalk s))
  have hflat : φ.hom.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ P)
  have w : localToChart f hU s hs ≫ chartHom f hU = localHom f hU s hs ≫ Spec.map φ :=
    pullback.condition
  have hpb : IsPullback (localToChart f hU s hs) (localHom f hU s hs) (chartHom f hU)
      (Spec.map φ) := IsPullback.of_hasPullback _ _
  let M₁ : LineBundle (chart f hU) := (LineBundle.pullback (chartToX f hU)).obj M
  have := CechResolution.isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs φ (chartHom f hU)
    (localHom f hU s hs) (localToChart f hU s hs) w M₁ hpb hflat
  have hlm := DerivedSections.isLocalizedModule_sectionsBaseChangeMap P (chartHom f hU)
    (localHom f hU s hs) (localToChart f hU s hs) w M₁.obj
  let y' : Γ((Scheme.Modules.pullback (localToChart f hU s hs)).obj M₁.obj, ⊤) :=
    ((Scheme.Modules.pullbackComp (localToChart f hU s hs) (chartToX f hU)).inv.app
      M.obj).app ⊤ y
  obtain ⟨⟨m, a⟩, hma⟩ := IsLocalizedModule.surj P
    (DerivedSections.sectionsBaseChangeMap φ (chartHom f hU) (localHom f hU s hs)
      (localToChart f hU s hs) w M₁.obj).hom y'
  let e : Γ(localBase f hU s hs, ⊤) :=
    (DerivedSections.structureRingHom (localHom f hU s hs)).hom (S.presheaf.germ U s hs a)
  have h1 : e • y' = sectionPullback (localToChart f hU s hs) M₁.obj ⊤ m := hma
  -- descend `m` along the open immersion `chartToX`
  obtain ⟨t₀, ht₀⟩ := (sectionPullbackLE_bijective_of_isOpenImmersion (chartToX f hU) M.obj
    (preimage_le_chartToX_opensRange f hU) (chartToX_preimage f hU).ge
    (chartToX_preimage f hU)).2 m
  have h2 : e • y = sectionPullbackLE (localToX f hU s hs) M.obj
      (top_le_localToX_preimage f hU s hs hs) t₀ := by
    have h3 := congrArg
      (((Scheme.Modules.pullbackComp (localToChart f hU s hs) (chartToX f hU)).hom.app
        M.obj).app ⊤) h1
    rw [Scheme.Modules.Hom.app_smul] at h3
    have h4 : ((Scheme.Modules.pullbackComp (localToChart f hU s hs) (chartToX f hU)).hom.app
        M.obj).app ⊤ y' = y := by
      simp only [y', ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Scheme.Modules.Hom.id_app]
      rfl
    rw [h4] at h3
    rw [h3, ← ht₀, ← sectionPullbackLE_self]
    exact pullbackComp_hom_sectionPullbackLE _ _ _ _ _ _ _
  -- the neighbourhood on which `a` is invertible
  have hau : IsUnit (S.presheaf.germ U s hs a) :=
    IsLocalization.map_units (S.presheaf.stalk s) a
  have hsV : s ∈ S.basicOpen (a : Γ(S, U)) := (Scheme.mem_basicOpen S _ s hs).2 hau
  let V := S.basicOpen (a : Γ(S, U))
  have hVU : V ≤ U := S.basicOpen_le _
  have hu : IsUnit (f.app V (S.presheaf.map (homOfLE hVU).op a)) :=
    (RingedSpace.isUnit_res_basicOpen S.toRingedSpace (a : Γ(S, U))).map (f.app V).hom
  refine ⟨V, hsV, hU.basicOpen _, ((hu.unit⁻¹ : (Γ(X, f ⁻¹ᵁ V))ˣ) : Γ(X, f ⁻¹ᵁ V)) •
    M.obj.presheaf.map (homOfLE (f.preimage_mono hVU)).op t₀, ?_⟩
  rw [sectionPullbackLE_smul, sectionPullbackLE_restrict]
  have h5 : (localToX f hU s hs).appLE (f ⁻¹ᵁ V) ⊤ (top_le_localToX_preimage f hU s hs hsV)
      ↑hu.unit⁻¹ * e = 1 := by
    rw [show e = (localToX f hU s hs).appLE (f ⁻¹ᵁ V) ⊤
      (top_le_localToX_preimage f hU s hs hsV) ↑hu.unit from
        (localToX_appLE_app_map f hU s hs hVU hsV a).symm, ← map_mul, Units.inv_mul,
      map_one]
  rw [← h2, smul_smul, h5, one_smul]

end Descent

lemma inv_app_hom_app {Y : Scheme.{u}} {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens)
    (n : Γ(N, W)) : e.inv.app W (e.hom.app W n) = n := by
  change (e.hom.app W ≫ e.inv.app W) n = n
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

lemma hom_app_inv_app {Y : Scheme.{u}} {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens)
    (n : Γ(N', W)) : e.hom.app W (e.inv.app W n) = n := by
  change (e.inv.app W ≫ e.hom.app W) n = n
  rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

/-- Pulling back sections over a smaller open commutes with morphisms of modules. -/
lemma sectionPullbackLE_naturality {T Y : Scheme.{u}} (g : T ⟶ Y) {M N : Y.Modules}
    (φ : M ⟶ N) {W : T.Opens} {V : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) (m : Γ(M, V)) :
    sectionPullbackLE g N h (φ.app V m) =
      ((Scheme.Modules.pullback g).map φ).app W (sectionPullbackLE g M h m) := by
  rw [sectionPullbackLE, sectionPullbackLE, sectionPullback_naturality]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback g).map φ).val
    (homOfLE h).op _).symm

/-- The pullback of `L` to the local base change is ample on the actual fibre whenever `L` is. -/
lemma isAmple_fibreToLocal (L : LineBundle X)
    (hamp : ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple) :
    ((LineBundle.pullback (fibreToLocal f hU s hs)).obj
      ((LineBundle.pullback (localToX f hU s hs)).obj L)).IsAmple :=
  LineBundle.IsAmple.of_iso hamp
    (((Scheme.Modules.pullbackCongr (fibreToLocal_toX f hU s hs)).app L.obj).symm ≪≫
      ((Scheme.Modules.pullbackComp (fibreToLocal f hU s hs) (localToX f hU s hs)).app
        L.obj).symm)

/-- A section of `L ^ n` on the actual fibre, transported to the pullback of the `n`-th power
of the pullback of `L` to the local base change. -/
def fibreSectionTransport (L : LineBundle X) (n : ℕ)
    (σ : GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj (tensorPow L.obj n))) :
    Γ((Scheme.Modules.pullback (fibreToLocal f hU s hs)).obj
      (tensorPow ((Scheme.Modules.pullback (localToX f hU s hs)).obj L.obj) n), ⊤) :=
  ((Scheme.Modules.pullback (fibreToLocal f hU s hs)).map
      (actualPullbackTensorPowIso (localToX f hU s hs) L.obj n).hom).app ⊤
    (((Scheme.Modules.pullbackComp (fibreToLocal f hU s hs) (localToX f hU s hs)).inv.app
        (tensorPow L.obj n)).app ⊤
      (((Scheme.Modules.pullbackCongr (fibreToLocal_toX f hU s hs)).inv.app
        (tensorPow L.obj n)).app ⊤ σ))

lemma natIso_hom_app_inv_app {T Y : Scheme.{u}} {F G : Y.Modules ⥤ T.Modules} (e : F ≅ G)
    (M : Y.Modules) (W : T.Opens) (n : Γ(G.obj M, W)) :
    (e.hom.app M).app W ((e.inv.app M).app W n) = n :=
  hom_app_inv_app (e.app M) W n

lemma pullback_map_inv_app_map_hom_app {T Y : Scheme.{u}} (g : T ⟶ Y) {N N' : Y.Modules}
    (e : N ≅ N') (W : T.Opens) (n : Γ((Scheme.Modules.pullback g).obj N, W)) :
    ((Scheme.Modules.pullback g).map e.inv).app W
      (((Scheme.Modules.pullback g).map e.hom).app W n) = n :=
  inv_app_hom_app ((Scheme.Modules.pullback g).mapIso e) W n

/-- Transport of a section along a factorization `q = i ≫ p`: if `y` lifts the transported
section `σ` along `i`, and `τ` pulls back along `p` to the corresponding section, then `τ` pulls
back along `q` to `σ`. -/
lemma sectionPullbackLE_eq_of_lift {Z Y W : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ W) (q : Z ⟶ W)
    (hip : i ≫ p = q) (M : W.Modules) (N : Y.Modules)
    (Φ : (Scheme.Modules.pullback p).obj M ≅ N) {V : W.Opens} (hp : ⊤ ≤ p ⁻¹ᵁ V)
    (hq : ⊤ ≤ q ⁻¹ᵁ V) (σ : Γ((Scheme.Modules.pullback q).obj M, ⊤)) (y : Γ(N, ⊤))
    (hy : sectionPullback i N ⊤ y =
      ((Scheme.Modules.pullback i).map Φ.hom).app ⊤
        (((Scheme.Modules.pullbackComp i p).inv.app M).app ⊤
          (((Scheme.Modules.pullbackCongr hip).inv.app M).app ⊤ σ)))
    (τ : Γ(M, V)) (hτ : sectionPullbackLE p M hp τ = Φ.inv.app ⊤ y) :
    sectionPullbackLE q M hq τ = σ := by
  have hi : (⊤ : Z.Opens) ≤ i ⁻¹ᵁ ⊤ := le_top
  have hip' : (⊤ : Z.Opens) ≤ (i ≫ p) ⁻¹ᵁ V := by
    rw [hip]
    exact hq
  have hy' : sectionPullbackLE i N hi y = sectionPullback i N ⊤ y :=
    sectionPullbackLE_self i N ⊤ y
  calc sectionPullbackLE q M hq τ
      = ((Scheme.Modules.pullbackCongr hip).hom.app M).app ⊤
          (sectionPullbackLE (i ≫ p) M hip' τ) :=
        (pullbackCongr_hom_sectionPullbackLE hip M hip' hq τ).symm
    _ = ((Scheme.Modules.pullbackCongr hip).hom.app M).app ⊤
          (((Scheme.Modules.pullbackComp i p).hom.app M).app ⊤
            (sectionPullbackLE i ((Scheme.Modules.pullback p).obj M) hi
              (sectionPullbackLE p M hp τ))) := by
        rw [pullbackComp_hom_sectionPullbackLE i p M hp hi hip' τ]
    _ = σ := by
        rw [hτ, sectionPullbackLE_naturality i Φ.inv hi y, hy', hy,
          pullback_map_inv_app_map_hom_app]
        rw [natIso_hom_app_inv_app, natIso_hom_app_inv_app]

/-- If a section on the local base change lifts the transported fibre section and descends to a
neighbourhood section `τ`, then `τ` restricts to the original fibre section. -/
lemma fibreNeighbourhoodSection_eq_of_lift (L : LineBundle X) (n : ℕ)
    (σ : GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj (tensorPow L.obj n)))
    (y : Γ(tensorPow ((Scheme.Modules.pullback (localToX f hU s hs)).obj L.obj) n, ⊤))
    (hy : sectionPullback (fibreToLocal f hU s hs) _ ⊤ y = fibreSectionTransport f hU s hs L n σ)
    {V : S.Opens} (hsV : s ∈ V) (τ : Γ(tensorPow L.obj n, f ⁻¹ᵁ V))
    (hτ : sectionPullbackLE (localToX f hU s hs) (tensorPow L.obj n)
      (top_le_localToX_preimage f hU s hs hsV) τ =
        (actualPullbackTensorPowIso (localToX f hU s hs) L.obj n).inv.app ⊤ y) :
    fibreNeighbourhoodSection f s (tensorPow L.obj n) hsV τ = σ :=
  sectionPullbackLE_eq_of_lift (fibreToLocal f hU s hs) (localToX f hU s hs) (f.fiberι s)
    (fibreToLocal_toX f hU s hs) (tensorPow L.obj n) _
    (actualPullbackTensorPowIso (localToX f hU s hs) L.obj n)
    (top_le_localToX_preimage f hU s hs hsV) (fibre_preimage_neighbourhood f s hsV) σ y hy τ hτ

end LocalReduction

open LocalReduction in
/-- The proper fibre power section lifting statement follows from its closed-fibre case over
noetherian local bases, applied to the base change of `f` to `Spec 𝒪_{S,s}`. -/
theorem properFibrePowerSectionLifting_of_local
    (h : LocalClosedFibrePowerSectionLifting.{u}) :
    ProperFibrePowerSectionLiftingStatement.{u} := by
  intro X S _ f _ L s hamp
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  obtain ⟨n₀, hn₀⟩ := h (S.presheaf.stalk s) (localBase f hU s hsU) (f.fiber s)
    (localHom f hU s hsU) _ (fibreToLocal f hU s hsU) (f.fiberToSpecResidueField s)
    (isPullback_fibreToLocal_quotient f hU s hsU) (isAmple_fibreToLocal f hU s hsU L hamp)
  refine ⟨n₀, fun n hn σ => ?_⟩
  obtain ⟨y, hy⟩ := hn₀ n hn (fibreSectionTransport f hU s hsU L n σ)
  obtain ⟨V, hsV, hV, τ, hτ⟩ := exists_sectionPullbackLE_eq f hU s hsU
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
    ((actualPullbackTensorPowIso (localToX f hU s hsU) L.obj n).inv.app ⊤ y)
  exact ⟨V, hsV, hV, τ, fibreNeighbourhoodSection_eq_of_lift f hU s hsU L n σ y hy hsV τ hτ⟩

end Langlands.AlgebraicGeometry.Modules
