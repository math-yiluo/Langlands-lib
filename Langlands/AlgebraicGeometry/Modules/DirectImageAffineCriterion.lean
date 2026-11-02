import Langlands.AlgebraicGeometry.Modules.AffineDirectImageRank
import Langlands.AlgebraicGeometry.Modules.OpenCartesianDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Finite projective affine sections of specified rank, with their canonical scalar comparisons. -/
def AffineSectionsData {S X : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (r : ℕ) : Prop :=
  ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ S) (XR : Scheme.{u})
    (p : XR ⟶ X) (fR : XR ⟶ Spec R), IsPullback p fR f x →
    Module.Finite R ((relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj M)) ∧
    Module.Projective R ((relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj M)) ∧
    (∀ q : PrimeSpectrum R,
      Module.rankAtStalk ((relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj M)) q = r) ∧
    ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (XT : Scheme.{u}) (p' : XT ⟶ XR)
      (fT : XT ⟶ Spec T) (h' : IsPullback p' fT fR (Spec.map φ)),
      IsIso (scalarSectionsBaseChangeMap φ fR fT p' h'.w ((Scheme.Modules.pullback p).obj M))

lemma AffineSectionsData.isQuasicoherent {S X : Scheme.{u}} {f : X ⟶ S}
    {M : X.Modules} {r : ℕ} (H : AffineSectionsData f M r)
    (R : CommRingCat.{u}) (x : Spec R ⟶ S) (XR : Scheme.{u})
    (p : XR ⟶ X) (fR : XR ⟶ Spec R) (h : IsPullback p fR f x) :
    ((Scheme.Modules.pushforward fR).obj ((Scheme.Modules.pullback p).obj M)).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_affineScalarBaseChange fR _ (H R x XR p fR h).2.2.2

lemma AffineSectionsData.isIso_affineBaseChange {S X : Scheme.{u}} {f : X ⟶ S}
    {M : X.Modules} {r : ℕ} (H : AffineSectionsData f M r)
    (R : CommRingCat.{u}) (x : Spec R ⟶ S) (XR : Scheme.{u})
    (p : XR ⟶ X) (fR : XR ⟶ Spec R) (h : IsPullback p fR f x)
    (T : CommRingCat.{u}) (φ : R ⟶ T) (XT : Scheme.{u}) (q : XT ⟶ XR)
    (fT : XT ⟶ Spec T) (hq : IsPullback q fT fR (Spec.map φ)) :
    IsIso (pushforwardBaseChange (Spec.map φ) fR fT q hq.w ((Scheme.Modules.pullback p).obj M)) := by
  have := H.isQuasicoherent R x XR p fR h
  have hc := H.isQuasicoherent T (Spec.map φ ≫ x) XT (q ≫ p) fT (hq.paste_horiz h)
  let e := (Scheme.Modules.pushforward fT).mapIso ((Scheme.Modules.pullbackComp q p).app M)
  have : ((Scheme.Modules.pushforward fT).obj
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec T).ringCatSheaf).prop_of_iso e.symm hc
  have := (H R x XR p fR h).2.2.2 T φ XT q fT hq
  exact isIso_pushforwardBaseChange_of_isIso_scalarSectionsBaseChangeMap φ fR fT q hq.w _

/-- Affine open neighborhoods on the source can be chosen over affine neighborhoods of the image. -/
lemma exists_affineOpenFactorization {S S' : Scheme.{u}} (b : S' ⟶ S) (y : S') :
    ∃ (R T : CommRingCat.{u}) (x : Spec R ⟶ S) (c : Spec T ⟶ S') (φ : R ⟶ T),
      IsOpenImmersion x ∧ IsOpenImmersion c ∧
      (∃ t : Spec T, c t = y) ∧ c ≫ b = Spec.map φ ≫ x := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show b y ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ b ⁻¹ᵁ U from hyU)
  let k := hV.isoSpec.inv ≫ b.resLE U V hVU ≫ hU.isoSpec.hom
  refine ⟨_, _, hU.fromSpec, hV.fromSpec, Spec.preimage k,
    inferInstance, inferInstance, ⟨hV.isoSpec.hom ⟨y, hyV⟩, ?_⟩, ?_⟩
  · change (hV.isoSpec.hom ≫ hV.isoSpec.inv ≫ V.ι) ⟨y, hyV⟩ = y
    simp
  · rw [Spec.map_preimage]
    dsimp only [k, IsAffineOpen.fromSpec]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

/-- Isomorphisms of module sheaves are detected by pullback to affine open neighborhoods. -/
lemma isIso_of_affineOpenPullbacks {S : Scheme.{u}} {P Q : S.Modules} (a : P ⟶ Q)
    (H : ∀ y : S, ∃ (T : CommRingCat.{u}) (c : Spec T ⟶ S), IsOpenImmersion c ∧
      ∃ t : Spec T, c t = y ∧ IsIso ((Scheme.Modules.pullback c).map a)) : IsIso a := by
  apply (Langlands.SchemeModule.isIso_iff_stalk_isIso a).mpr
  intro y
  obtain ⟨T, c, hc, t, hty, hi⟩ := H y
  have := hc
  have hr : IsIso ((Scheme.Modules.restrictFunctor c).map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback c) a).mpr hi
  have ht : IsIso ((TopCat.Presheaf.stalkFunctor Ab t).map
      ((Scheme.Modules.toPresheaf (Spec T)).map ((Scheme.Modules.restrictFunctor c).map a))) :=
    inferInstance
  rw [← hty]
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso c t) a).mp ht

lemma isIso_pushforwardBaseChange_congr {S S' X X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (M : X.Modules)
    {b₁ b₂ : S' ⟶ S} {p₁ p₂ : X' ⟶ X}
    (w₁ : p₁ ≫ f = f' ≫ b₁) (w₂ : p₂ ≫ f = f' ≫ b₂)
    (hb : b₁ = b₂) (hp : p₁ = p₂) :
    IsIso (pushforwardBaseChange b₁ f f' p₁ w₁ M) ↔
      IsIso (pushforwardBaseChange b₂ f f' p₂ w₂ M) := by
  subst b₂
  subst p₂
  rfl

lemma AffineSectionsData.isIso_pullback_baseChange {S S' X X' : Scheme.{u}}
    {f : X ⟶ S} {M : X.Modules} {r : ℕ} (H : AffineSectionsData f M r)
    (b : S' ⟶ S) (f' : X' ⟶ S') (p : X' ⟶ X) (h : IsPullback p f' f b)
    (R T : CommRingCat.{u}) (x : Spec R ⟶ S) (c : Spec T ⟶ S') (φ : R ⟶ T)
    [IsOpenImmersion x] [IsOpenImmersion c] (w : c ≫ b = Spec.map φ ≫ x) :
    IsIso ((Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p h.w M)) := by
  let XR := pullback f x
  let pR : XR ⟶ X := pullback.fst f x
  let fR : XR ⟶ Spec R := pullback.snd f x
  have hR : IsPullback pR fR f x := IsPullback.of_hasPullback f x
  let XT := pullback f' c
  let pT : XT ⟶ X' := pullback.fst f' c
  let fT : XT ⟶ Spec T := pullback.snd f' c
  have hT : IsPullback pT fT f' c := IsPullback.of_hasPullback f' c
  have wq : (pT ≫ p) ≫ f = (fT ≫ Spec.map φ) ≫ x := by
    rw [Category.assoc, h.w, ← Category.assoc, hT.w, Category.assoc, w, Category.assoc]
  let q : XT ⟶ XR := pullback.lift (pT ≫ p) (fT ≫ Spec.map φ) wq
  have hqp : q ≫ pR = pT ≫ p := pullback.lift_fst _ _ _
  have hqf : q ≫ fR = fT ≫ Spec.map φ := pullback.lift_snd _ _ _
  have hout : IsPullback (q ≫ pR) fT f (Spec.map φ ≫ x) := by
    rw [hqp, ← w]
    exact hT.paste_horiz h
  have hq : IsPullback q fT fR (Spec.map φ) := hout.of_right hqf hR
  have := isIso_pushforwardBaseChange_of_isOpenImmersion x f fR pR hR M
  have := H.isIso_affineBaseChange R x XR pR fR hR T φ XT q fT hq
  have hi : IsIso (iteratedPushforwardBaseChange x (Spec.map φ) f fR fT pR q hR.w hq.w M) := by
    unfold iteratedPushforwardBaseChange
    infer_instance
  rw [← pushforwardBaseChange_composition] at hi
  have hfull : IsIso (pushforwardBaseChange (Spec.map φ ≫ x) f fT (q ≫ pR)
      (compositeBaseChangeSquare x (Spec.map φ) f fR fT pR q hR.w hq.w) M) :=
    IsIso.of_isIso_comp_left
      ((Scheme.Modules.pullbackComp (Spec.map φ) x).hom.app
        ((Scheme.Modules.pushforward f).obj M)) _
  have hfull' := (isIso_pushforwardBaseChange_congr f fT M
    (compositeBaseChangeSquare x (Spec.map φ) f fR fT pR q hR.w hq.w)
    (hT.paste_horiz h).w w.symm hqp).mp hfull
  have ht : IsIso (iteratedPushforwardBaseChange b c f f' fT p pT h.w hT.w M) := by
    rw [← pushforwardBaseChange_composition]
    infer_instance
  have := isIso_pushforwardBaseChange_of_isOpenImmersion c f' fT pT hT
    ((Scheme.Modules.pullback p).obj M)
  unfold iteratedPushforwardBaseChange at ht
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p h.w M))
    (pushforwardBaseChange c f' fT pT hT.w ((Scheme.Modules.pullback p).obj M) ≫
      (Scheme.Modules.pushforward fT).map ((Scheme.Modules.pullbackComp pT p).hom.app M))

/-- Affine scalar comparisons force the specified sheaf comparison to be invertible. -/
theorem AffineSectionsData.isIso_baseChange {S S' X X' : Scheme.{u}}
    {f : X ⟶ S} {M : X.Modules} {r : ℕ} (H : AffineSectionsData f M r)
    (b : S' ⟶ S) (f' : X' ⟶ S') (p : X' ⟶ X) (h : IsPullback p f' f b) :
    IsIso (pushforwardBaseChange b f f' p h.w M) := by
  apply isIso_of_affineOpenPullbacks
  intro y
  obtain ⟨R, T, x, c, φ, hx, hc, ⟨t, hty⟩, w⟩ := exists_affineOpenFactorization b y
  have := hx
  have := hc
  exact ⟨T, c, hc, t, hty,
    H.isIso_pullback_baseChange b f' p h R T x c φ w⟩

/-- A free chart along an open immersion gives a free chart on its open image. -/
def freeChartOnOpensRange {S Y : Scheme.{u}} (P : S.Modules)
    (j : Y ⟶ S) [IsOpenImmersion j] (I : Type u)
    (e : P.restrict j ≅ SheafOfModules.free (R := Y.ringCatSheaf) I) :
    P.restrict j.opensRange.ι ≅
      SheafOfModules.free (R := j.opensRange.toScheme.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp.symm).app P ≪≫
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app P ≪≫
    (Scheme.Modules.restrictFunctor j.isoOpensRange.inv).mapIso e ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback j.isoOpensRange.inv).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso j.isoOpensRange.inv.toRingCatSheafHom I

/-- Finite projective affine sections with constant rank give the actual fixed-rank condition. -/
theorem AffineSectionsData.isLocallyFreeOfRank {S X : Scheme.{u}}
    {f : X ⟶ S} {M : X.Modules} {r : ℕ} (H : AffineSectionsData f M r) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank ((Scheme.Modules.pushforward f).obj M) r := by
  let P := (Scheme.Modules.pushforward f).obj M
  apply Langlands.Scheme.Modules.isLocallyFreeOfRank_of_freeNeighborhoods P r
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : S.Opens) from trivial)
  let R := Γ(S, U)
  let x : Spec R ⟶ S := hU.fromSpec
  let t : Spec R := hU.isoSpec.hom ⟨y, hyU⟩
  have hty : x t = y := by
    change (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ U.ι) ⟨y, hyU⟩ = y
    simp
  let XR := pullback f x
  let pR : XR ⟶ X := pullback.fst f x
  let fR : XR ⟶ Spec R := pullback.snd f x
  have hR : IsPullback pR fR f x := IsPullback.of_hasPullback f x
  let PR := (Scheme.Modules.pushforward fR).obj ((Scheme.Modules.pullback pR).obj M)
  have : PR.IsQuasicoherent := H.isQuasicoherent R x XR pR fR hR
  have hData := H R x XR pR fR hR
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj PR) := hData.1
  have : Module.Projective R ((moduleSpecΓFunctor (R := R)).obj PR) := hData.2.1
  obtain ⟨W, htW, ⟨eW⟩⟩ :=
    exists_freeNeighborhood_of_finite_projective_rankAtStalk PR r hData.2.2.1 t
  let eR : P.restrict x ≅ PR :=
    (Scheme.Modules.restrictFunctorIsoPullback x).app P ≪≫
      openCartesianBaseChangeIso x f fR pR hR M
  let j : W.toScheme ⟶ S := W.ι ≫ x
  let e : P.restrict j ≅
      SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (Scheme.Modules.restrictFunctorComp W.ι x).app P ≪≫
      (Scheme.Modules.restrictFunctor W.ι).mapIso eR ≪≫ eW
  exact ⟨j.opensRange, ⟨⟨t, htW⟩, hty⟩,
    ⟨freeChartOnOpensRange P j (ULift.{u} (Fin r)) e⟩⟩

/-- The sheaf-level endpoint for finite projective affine sections and canonical scalar base change. -/
theorem pushforward_isLocallyFreeOfRank_and_isIso_pushforwardBaseChange
    {S X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (L : Picard.LineBundle X) (r : ℕ)
    (H : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ S) (XR : Scheme.{u})
      (p : XR ⟶ X) (fR : XR ⟶ Spec R), IsPullback p fR f x →
      Module.Finite R ((relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj L.obj)) ∧
      Module.Projective R ((relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj L.obj)) ∧
      (∀ q : PrimeSpectrum R,
        Module.rankAtStalk ((relativeGlobalSections fR).obj
          ((Scheme.Modules.pullback p).obj L.obj)) q = r) ∧
      ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (XT : Scheme.{u}) (p' : XT ⟶ XR)
        (fT : XT ⟶ Spec T) (h' : IsPullback p' fT fR (Spec.map φ)),
        IsIso (scalarSectionsBaseChangeMap φ fR fT p' h'.w
          ((Scheme.Modules.pullback p).obj L.obj))) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank ((Scheme.Modules.pushforward f).obj L.obj) r ∧
      ∀ {S' X' : Scheme.{u}} (b : S' ⟶ S) (f' : X' ⟶ S') (p : X' ⟶ X)
        (h : IsPullback p f' f b), IsIso (pushforwardBaseChange b f f' p h.w L.obj) := by
  have hData : AffineSectionsData f L.obj r := H
  exact ⟨hData.isLocallyFreeOfRank, fun b f' p h => hData.isIso_baseChange b f' p h⟩

end Langlands.AlgebraicGeometry.Modules.DerivedSections
