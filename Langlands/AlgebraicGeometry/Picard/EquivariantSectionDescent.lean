import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow
import Langlands.AlgebraicGeometry.SectionPullback
import Langlands.AlgebraicGeometry.Modules.QCQSLineBundleSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange
import Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof

/-! # Invariant sections of equivariant line bundles on cartesian étale relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Pullback of global sections, landing in the global sections of the pullback. -/
def gpull (f : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) →+ Γ((Scheme.Modules.pullback f).obj M, ⊤) where
  toFun x := sectionPullback f M ⊤ x
  map_zero' := map_zero (sectionPullback f M ⊤)
  map_add' x y := map_add (sectionPullback f M ⊤) x y

lemma gpull_naturality (f : X ⟶ Y) {M N : Y.Modules} (g : M ⟶ N) (x : Γ(M, ⊤)) :
    gpull f N (g.app ⊤ x) = ((Scheme.Modules.pullback f).map g).app ⊤ (gpull f M x) :=
  sectionPullback_naturality f g ⊤ x

lemma gpull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
        (gpull f ((Scheme.Modules.pullback g).obj M) (gpull g M x)) = gpull (f ≫ g) M x :=
  sectionPullback_comp f g M ⊤ x

lemma gpull_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤ (gpull (f ≫ g) M x) =
      gpull f ((Scheme.Modules.pullback g).obj M) (gpull g M x) := by
  rw [← gpull_comp]
  change (((Scheme.Modules.pullbackComp f g).hom.app M ≫
    (Scheme.Modules.pullbackComp f g).inv.app M).app ⊤) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

lemma gpull_id (M : X.Modules) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app M).app ⊤ (gpull (𝟙 X) M x) = x :=
  sectionPullback_id M ⊤ x

lemma gpull_congr {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr e).hom.app M).app ⊤ (gpull f M x) = gpull f' M x := by
  subst e
  rfl

section RelPull

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}}

/-- Pullback of relative global sections along a morphism over `Spec R`. -/
def relPull (fX : X ⟶ Spec R) (fY : Y ⟶ Spec R) (h : Y ⟶ X) (w : h ≫ fX = fY) (M : X.Modules) :
    (relativeGlobalSections fX).obj M ⟶ (relativeGlobalSections fY).obj
      ((Scheme.Modules.pullback h).obj M) :=
  relativeGlobalSectionsPullback (Over.homMk h w : Over.mk fY ⟶ Over.mk fX) M

lemma relPull_apply (fX : X ⟶ Spec R) (fY : Y ⟶ Spec R) (h : Y ⟶ X) (w : h ≫ fX = fY)
    (M : X.Modules) (x : (relativeGlobalSections fX).obj M) :
    relPull fX fY h w M x = gpull h M x := by
  have h1 := relativeGlobalSectionsPullback_apply (Over.homMk h w : Over.mk fY ⟶ Over.mk fX) M x
  have h2 := Langlands.SchemeModule.pullbackSection_eq_sectionPullback h M x
  exact h1.trans h2

end RelPull

section Residue

open Langlands.SchemeModule

lemma residueSection_smul (M : X.Modules) (r : Γ(X, ⊤)) (s : GlobalSections M) (x : X) :
    residueSection M (r • s) x = (X.fromSpecResidueField x).appTop r • residueSection M s x := by
  unfold residueSection
  rw [pullbackSection_eq_sectionPullback, pullbackSection_eq_sectionPullback]
  exact (sectionPullback (X.fromSpecResidueField x) M ⊤).map_smulₛₗ r s

lemma residueSection_zero (M : X.Modules) (x : X) : residueSection M 0 x = 0 :=
  Langlands.SchemeModule.pullbackSection_zero _ M

end Residue

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- A module sheaf on the chart of an étale equivalence relation, with coherent identifications
of its pullbacks along all related pairs of scheme-valued points. -/
structure EquivariantModule (E : EtaleEquivalenceRelation.{u}) (F : E.U.Modules) where
  transport {T : Scheme.{u}} (a b : T ⟶ E.U) (h : E.Related a b) :
    (Scheme.Modules.pullback a).obj F ≅ (Scheme.Modules.pullback b).obj F
  transport_self {T : Scheme.{u}} (a : T ⟶ E.U) (h : E.Related a a) :
    transport a a h = Iso.refl _
  transport_trans {T : Scheme.{u}} (a b c : T ⟶ E.U)
      (hab : E.Related a b) (hbc : E.Related b c) (hac : E.Related a c) :
    transport a b hab ≪≫ transport b c hbc = transport a c hac
  transport_precompose {T W : Scheme.{u}} (k : W ⟶ T) (a b : T ⟶ E.U)
      (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) :
    transport (k ≫ a) (k ≫ b) h' =
      ((Scheme.Modules.pullbackComp k a).app F).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (transport a b h) ≪≫
          (Scheme.Modules.pullbackComp k b).app F

variable {E : EtaleEquivalenceRelation.{u}}

/-- The tensor powers of an actual equivariant line bundle, as equivariant modules. -/
def EquivariantLineBundle.tensorPowModule (B : EquivariantLineBundle E) (n : ℕ) :
    EquivariantModule E (tensorPow B.bundle.obj n) where
  transport a b h := B.tensorPowTransport n a b h
  transport_self a h := B.tensorPowTransport_self n a h
  transport_trans a b c hab hbc hac := B.tensorPowTransport_trans n a b c hab hbc hac
  transport_precompose k a b h h' := B.tensorPowTransport_precompose n k a b h h'

namespace EquivariantModule

variable {F : E.U.Modules} (D : EquivariantModule E F)

/-- The transported pullback of a global section along a related pair. -/
def tr {T : Scheme.{u}} (a b : T ⟶ E.U) (h : E.Related a b) (m : Γ(F, ⊤)) :
    Γ((Scheme.Modules.pullback b).obj F, ⊤) :=
  ((D.transport a b h).hom.app ⊤) (gpull a F m)

lemma tr_self {T : Scheme.{u}} (a : T ⟶ E.U) (h : E.Related a a) (m : Γ(F, ⊤)) :
    D.tr a a h m = gpull a F m := by
  rw [tr, D.transport_self]
  rfl

lemma transport_tr {T : Scheme.{u}} (a b c : T ⟶ E.U)
    (hab : E.Related a b) (hbc : E.Related b c) (hac : E.Related a c) (m : Γ(F, ⊤)) :
    ((D.transport b c hbc).hom.app ⊤) (D.tr a b hab m) = D.tr a c hac m := by
  rw [tr, tr, ← D.transport_trans a b c hab hbc hac]
  rfl

lemma pullback_tr {T W : Scheme.{u}} (k : W ⟶ T) (a b : T ⟶ E.U)
    (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) (m : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp k b).hom.app F).app ⊤
        (gpull k ((Scheme.Modules.pullback b).obj F) (D.tr a b h m)) =
      D.tr (k ≫ a) (k ≫ b) h' m := by
  rw [tr, tr, D.transport_precompose k a b h h', gpull_naturality]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [gpull_comp_inv]

lemma tr_congr_left {T : Scheme.{u}} {a a' : T ⟶ E.U} (ha : a = a') (b : T ⟶ E.U)
    (h : E.Related a b) (h' : E.Related a' b) (m : Γ(F, ⊤)) : D.tr a b h m = D.tr a' b h' m := by
  subst ha
  rfl

lemma tr_congr_right {T : Scheme.{u}} (a : T ⟶ E.U) {b b' : T ⟶ E.U} (hb : b = b')
    (h : E.Related a b) (h' : E.Related a b') (m : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackCongr hb).hom.app F).app ⊤ (D.tr a b h m) = D.tr a b' h' m := by
  subst hb
  rfl

lemma transport_precompose_hom_inv {T W : Scheme.{u}} (k : W ⟶ T) (a b : T ⟶ E.U)
    (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b)) :
    (D.transport (k ≫ a) (k ≫ b) h').hom ≫ (Scheme.Modules.pullbackComp k b).inv.app F =
      (Scheme.Modules.pullbackComp k a).inv.app F ≫
        (Scheme.Modules.pullback k).map (D.transport a b h).hom := by
  rw [D.transport_precompose k a b h h']
  simp

lemma transport_precompose_apply {T W : Scheme.{u}} (k : W ⟶ T) (a b : T ⟶ E.U)
    (h : E.Related a b) (h' : E.Related (k ≫ a) (k ≫ b))
    (w : Γ((Scheme.Modules.pullback (k ≫ a)).obj F, ⊤)) :
    ((Scheme.Modules.pullbackComp k b).inv.app F).app ⊤
        (((D.transport (k ≫ a) (k ≫ b) h').hom.app ⊤) w) =
      (((Scheme.Modules.pullback k).map (D.transport a b h).hom).app ⊤)
        (((Scheme.Modules.pullbackComp k a).inv.app F).app ⊤ w) := by
  have key := congrArg (fun φ => (φ.app ⊤) w) (D.transport_precompose_hom_inv k a b h h')
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using key

section Coalgebra

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {S U : Scheme.{u}} [IsAffine S] [IsAffine U] (p : U ⟶ S) (f : E.U ⟶ U)

omit [IsAffine S] [IsAffine U] in
/-- The relation's symmetry gives the transposed cartesian square. -/
lemma isPullback_symm (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    IsPullback E.s (E.t ≫ f) (f ≫ p) p := by
  obtain ⟨σ, h1, h2⟩ := E.symm E.R (𝟙 _)
  rw [Category.id_comp] at h1 h2
  have hσσ : σ ≫ σ = 𝟙 _ := by
    have := E.mono_lift
    rw [← cancel_mono (prod.lift E.t E.s)]
    ext <;> simp [h1, h2]
  let e : E.R ≅ E.R := ⟨σ, σ, hσσ, hσσ⟩
  exact hcart.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [e, h2])
    (by simp [e, reassoc_of% h1]) (by simp) (by simp)

/-- The transposed cartesian square over the spectra of global sections. -/
lemma isPullback_spec (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    IsPullback E.s (E.t ≫ f ≫ U.isoSpec.hom) ((f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop)
      (Spec.map p.appTop) := by
  refine (isPullback_symm p f hcart).of_iso (Iso.refl _) (Iso.refl _) U.isoSpec S.isoSpec
    (by simp) (by simp) ?_ ?_
  · simp [Scheme.isoSpec_hom_naturality]
  · simp [Scheme.isoSpec_hom_naturality]

variable {p f} in
/-- The base-change comparison `B ⊗_A Γ(X, F) → Γ(R, s^*F)`, through the transposed cartesian
square. -/
def baseChange (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) :
    (ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
      ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)) ⟶
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj ((Scheme.Modules.pullback E.s).obj F) :=
  (ModuleCat.extendScalars p.appTop.hom).map
      ((relativeGlobalSectionsBaseRingIso p.appTop ((f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop)
        (f ≫ U.isoSpec.hom) rfl).hom.app F) ≫
    scalarSectionsBaseChangeMap p.appTop ((f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop)
      (E.t ≫ f ≫ U.isoSpec.hom) E.s (isPullback_spec p f hcart).w F

lemma isIso_baseChange [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (hF : IsLocallyFreeRankOne F) [CompactSpace E.U] [QuasiSeparatedSpace E.U] :
    IsIso (baseChange hcart F) := by
  have : IsAffineHom E.s := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_symm p f hcart).flip (inferInstance : IsAffineHom p)
  have := Modules.CechResolution.isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs p.appTop
    ((f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop) (E.t ≫ f ≫ U.isoSpec.hom) E.s
    (isPullback_spec p f hcart).w ⟨F, hF⟩ (isPullback_spec p f hcart) p.flat_appTop
  unfold baseChange
  infer_instance

lemma baseChange_one_tmul (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    baseChange hcart F ((1 : Γ(U, ⊤)) ⊗ₜ[Γ(S, ⊤), p.appTop.hom] m) = gpull E.s F m := by
  unfold baseChange
  rw [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul, scalarSectionsBaseChangeMap_one_tmul]
  rfl


/-- A diagonal point of the relation. -/
def diag (E : EtaleEquivalenceRelation.{u}) : E.U ⟶ E.R := (E.refl E.U (𝟙 _)).choose

@[reassoc (attr := simp)]
lemma diag_t (E : EtaleEquivalenceRelation.{u}) : diag E ≫ E.t = 𝟙 _ :=
  (E.refl E.U (𝟙 _)).choose_spec.1

@[reassoc (attr := simp)]
lemma diag_s (E : EtaleEquivalenceRelation.{u}) : diag E ≫ E.s = 𝟙 _ :=
  (E.refl E.U (𝟙 _)).choose_spec.2

lemma related_t_s (E : EtaleEquivalenceRelation.{u}) : E.Related E.t E.s :=
  ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩

/-- Transported pullback of sections from the chart to the relation. -/
def transportPull (F : E.U.Modules) (D : EquivariantModule E F) :
    (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F ⟶
      (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
        ((Scheme.Modules.pullback E.s).obj F) :=
  relPull (f ≫ U.isoSpec.hom) (E.t ≫ f ≫ U.isoSpec.hom) E.t rfl F ≫
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).map
      (D.transport E.t E.s (related_t_s E)).hom

lemma transportPull_apply (F : E.U.Modules) (D : EquivariantModule E F)
    (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    transportPull (f := f) F D m = D.tr E.t E.s (related_t_s E) m := by
  unfold transportPull
  rw [ModuleCat.comp_apply, relPull_apply]
  rfl

/-- Pullback along the diagonal, identified with the original sections. -/
def diagPull (F : E.U.Modules) :
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
        ((Scheme.Modules.pullback E.s).obj F) ⟶
      (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F :=
  relPull (E.t ≫ f ≫ U.isoSpec.hom) (f ≫ U.isoSpec.hom) (diag E) (by simp)
      ((Scheme.Modules.pullback E.s).obj F) ≫
    (relativeGlobalSections (f ≫ U.isoSpec.hom)).map
      ((Scheme.Modules.pullbackComp (diag E) E.s).hom.app F ≫
        (Scheme.Modules.pullbackCongr (diag_s E)).hom.app F ≫
          (Scheme.Modules.pullbackId E.U).hom.app F)

lemma diagPull_apply (F : E.U.Modules)
    (y : (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
      ((Scheme.Modules.pullback E.s).obj F)) :
    diagPull (f := f) F y =
      ((Scheme.Modules.pullbackId E.U).hom.app F).app ⊤
        (((Scheme.Modules.pullbackCongr (diag_s E)).hom.app F).app ⊤
          (((Scheme.Modules.pullbackComp (diag E) E.s).hom.app F).app ⊤
            (gpull (diag E) ((Scheme.Modules.pullback E.s).obj F) y))) := by
  unfold diagPull
  rw [ModuleCat.comp_apply, relPull_apply]
  rfl

lemma diagPull_gpull (F : E.U.Modules) (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    diagPull (f := f) F (gpull E.s F m) = m := by
  rw [diagPull_apply, gpull_comp, gpull_congr, gpull_id]

lemma diagPull_tr (F : E.U.Modules) (D : EquivariantModule E F)
    (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    diagPull (f := f) F (D.tr E.t E.s (related_t_s E) m) = m := by
  have h₁ : E.Related (diag E ≫ E.t) (diag E ≫ E.s) := ⟨diag E, rfl, rfl⟩
  have h₂ : E.Related (diag E ≫ E.t) (𝟙 E.U) := by simpa using h₁
  have h₃ : E.Related (𝟙 E.U) (𝟙 E.U) := by simpa using h₁
  rw [diagPull_apply, D.pullback_tr (diag E) E.t E.s (related_t_s E) h₁,
    D.tr_congr_right _ (diag_s E) h₁ h₂, D.tr_congr_left (diag_t E) _ h₂ h₃, D.tr_self, gpull_id]


/-- The base change of the relation (over the cover ring through its target) along the cover. -/
abbrev R₂ : Scheme.{u} :=
  pullback ((E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop) (Spec.map p.appTop)

/-- The projection of `R₂` to the relation. -/
abbrev g₂ : R₂ p f ⟶ E.R := pullback.fst _ _

/-- The projection of `R₂` to the spectrum of the cover ring. -/
abbrev f₂ : R₂ p f ⟶ Spec Γ(U, ⊤) := pullback.snd _ _

lemma g₂_t_f_p : g₂ p f ≫ E.t ≫ f ≫ p = (f₂ p f ≫ U.isoSpec.inv) ≫ p := by
  rw [← cancel_mono S.isoSpec.hom]
  simp only [Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    pullback.condition (f := (E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop)
      (g := Spec.map p.appTop)

variable {p f} in
/-- The relation point over `(u, r)` whose source is the source of `r`. -/
def kappa (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) : R₂ p f ⟶ E.R :=
  (isPullback_symm p f hcart).lift (g₂ p f ≫ E.s) (f₂ p f ≫ U.isoSpec.inv) (by
    rw [Category.assoc, ← g₂_t_f_p, ← Category.assoc E.s, ← hcart.w])

variable {p f} in
/-- The relation point over `(u, r)` whose source is the target of `r`. -/
def lam (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) : R₂ p f ⟶ E.R :=
  (isPullback_symm p f hcart).lift (g₂ p f ≫ E.t) (f₂ p f ≫ U.isoSpec.inv) (by
    rw [Category.assoc, ← g₂_t_f_p])

lemma kappa_s (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) : kappa hcart ≫ E.s = g₂ p f ≫ E.s :=
  (isPullback_symm p f hcart).lift_fst _ _ _

lemma kappa_t_f (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    kappa hcart ≫ E.t ≫ f = f₂ p f ≫ U.isoSpec.inv :=
  (isPullback_symm p f hcart).lift_snd _ _ _

lemma lam_s (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) : lam hcart ≫ E.s = g₂ p f ≫ E.t :=
  (isPullback_symm p f hcart).lift_fst _ _ _

lemma lam_t_f (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    lam hcart ≫ E.t ≫ f = f₂ p f ≫ U.isoSpec.inv :=
  (isPullback_symm p f hcart).lift_snd _ _ _

lemma kappa_t_eq_lam_t (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    kappa hcart ≫ E.t = lam hcart ≫ E.t := by
  obtain ⟨r₃, h₃t, h₃s⟩ := E.trans _ (lam hcart) (g₂ p f) (lam_s p f hcart)
  have : r₃ = kappa hcart := by
    apply (isPullback_symm p f hcart).hom_ext
    · rw [h₃s, kappa_s]
    · rw [reassoc_of% h₃t, lam_t_f, kappa_t_f]
  rw [← this, h₃t]

lemma kappa_w (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    kappa hcart ≫ E.t ≫ f ≫ U.isoSpec.hom = f₂ p f := by
  rw [reassoc_of% (kappa_t_f p f hcart), Iso.inv_hom_id, Category.comp_id]

lemma lam_w (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) :
    lam hcart ≫ E.t ≫ f ≫ U.isoSpec.hom = f₂ p f := by
  rw [reassoc_of% (lam_t_f p f hcart), Iso.inv_hom_id, Category.comp_id]


variable {p f} in
/-- Pullback along `κ`, identified with pullback along `g₂`. -/
def kPull (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) :
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
        ((Scheme.Modules.pullback E.s).obj F) ⟶
      (relativeGlobalSections (f₂ p f)).obj
        ((Scheme.Modules.pullback (g₂ p f)).obj ((Scheme.Modules.pullback E.s).obj F)) :=
  relPull (E.t ≫ f ≫ U.isoSpec.hom) (f₂ p f) (kappa hcart) (kappa_w p f hcart)
      ((Scheme.Modules.pullback E.s).obj F) ≫
    (relativeGlobalSections (f₂ p f)).map
      ((Scheme.Modules.pullbackComp (kappa hcart) E.s).hom.app F ≫
        (Scheme.Modules.pullbackCongr (kappa_s p f hcart)).hom.app F ≫
          (Scheme.Modules.pullbackComp (g₂ p f) E.s).inv.app F)

variable {p f} in
/-- Pullback along `λ`, identified through `g₂` and the transport on the relation. -/
def lPull (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (D : EquivariantModule E F) :
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
        ((Scheme.Modules.pullback E.s).obj F) ⟶
      (relativeGlobalSections (f₂ p f)).obj
        ((Scheme.Modules.pullback (g₂ p f)).obj ((Scheme.Modules.pullback E.s).obj F)) :=
  relPull (E.t ≫ f ≫ U.isoSpec.hom) (f₂ p f) (lam hcart) (lam_w p f hcart)
      ((Scheme.Modules.pullback E.s).obj F) ≫
    (relativeGlobalSections (f₂ p f)).map
      ((Scheme.Modules.pullbackComp (lam hcart) E.s).hom.app F ≫
        (Scheme.Modules.pullbackCongr (lam_s p f hcart)).hom.app F ≫
          (Scheme.Modules.pullbackComp (g₂ p f) E.t).inv.app F ≫
            (Scheme.Modules.pullback (g₂ p f)).map (D.transport E.t E.s (related_t_s E)).hom)

lemma kPull_apply (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (y : (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
      ((Scheme.Modules.pullback E.s).obj F)) :
    kPull hcart F y = ((Scheme.Modules.pullbackComp (g₂ p f) E.s).inv.app F).app ⊤
      (((Scheme.Modules.pullbackCongr (kappa_s p f hcart)).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp (kappa hcart) E.s).hom.app F).app ⊤
          (gpull (kappa hcart) ((Scheme.Modules.pullback E.s).obj F) y))) := by
  unfold kPull
  rw [ModuleCat.comp_apply, relPull_apply]
  rfl

lemma lPull_apply (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (D : EquivariantModule E F)
    (y : (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj
      ((Scheme.Modules.pullback E.s).obj F)) :
    lPull hcart F D y = (((Scheme.Modules.pullback (g₂ p f)).map
        (D.transport E.t E.s (related_t_s E)).hom).app ⊤)
      (((Scheme.Modules.pullbackComp (g₂ p f) E.t).inv.app F).app ⊤
        (((Scheme.Modules.pullbackCongr (lam_s p f hcart)).hom.app F).app ⊤
          (((Scheme.Modules.pullbackComp (lam hcart) E.s).hom.app F).app ⊤
            (gpull (lam hcart) ((Scheme.Modules.pullback E.s).obj F) y)))) := by
  unfold lPull
  rw [ModuleCat.comp_apply, relPull_apply]
  rfl

lemma kPull_gpull (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    kPull hcart F (gpull E.s F m) = gpull (g₂ p f) _ (gpull E.s F m) := by
  rw [kPull_apply, gpull_comp, gpull_congr, gpull_comp_inv]

lemma lPull_gpull (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (D : EquivariantModule E F) (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    lPull hcart F D (gpull E.s F m) = gpull (g₂ p f) _ (D.tr E.t E.s (related_t_s E) m) := by
  rw [lPull_apply, gpull_comp, gpull_congr, gpull_comp_inv, ← gpull_naturality]
  rfl

lemma kPull_tr_eq_lPull_tr (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (D : EquivariantModule E F) (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    kPull hcart F (D.tr E.t E.s (related_t_s E) m) =
      lPull hcart F D (D.tr E.t E.s (related_t_s E) m) := by
  have hk : E.Related (kappa hcart ≫ E.t) (kappa hcart ≫ E.s) := ⟨kappa hcart, rfl, rfl⟩
  have hl : E.Related (lam hcart ≫ E.t) (lam hcart ≫ E.s) := ⟨lam hcart, rfl, rfl⟩
  have hk' : E.Related (kappa hcart ≫ E.t) (g₂ p f ≫ E.s) := by
    simpa [kappa_s p f hcart] using hk
  have hl' : E.Related (lam hcart ≫ E.t) (g₂ p f ≫ E.t) := by
    simpa [lam_s p f hcart] using hl
  have hl'' : E.Related (lam hcart ≫ E.t) (g₂ p f ≫ E.s) := by
    simpa [kappa_t_eq_lam_t p f hcart] using hk'
  have hg : E.Related (g₂ p f ≫ E.t) (g₂ p f ≫ E.s) := ⟨g₂ p f, rfl, rfl⟩
  rw [kPull_apply, D.pullback_tr _ _ _ _ hk, D.tr_congr_right _ (kappa_s p f hcart) hk hk',
    D.tr_congr_left (kappa_t_eq_lam_t p f hcart) _ hk' hl'', lPull_apply,
    D.pullback_tr _ _ _ _ hl, D.tr_congr_right _ (lam_s p f hcart) hl hl',
    ← D.transport_precompose_apply (g₂ p f) E.t E.s (related_t_s E) hg, D.transport_tr]


variable {p f} in
/-- The base-change comparison for the relation, from `B ⊗_A Γ(R, s^*F)` to `Γ(R₂, g₂^*s^*F)`. -/
def baseChange₂ (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) :
    (ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
      ((ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
        ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)))) ⟶
    (relativeGlobalSections (f₂ p f)).obj
        ((Scheme.Modules.pullback (g₂ p f)).obj ((Scheme.Modules.pullback E.s).obj F)) :=
  (ModuleCat.extendScalars p.appTop.hom).map
      ((ModuleCat.restrictScalars p.appTop.hom).map (baseChange hcart F)) ≫
    (ModuleCat.extendScalars p.appTop.hom).map
      ((relativeGlobalSectionsBaseRingIso p.appTop
        ((E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop) (E.t ≫ f ≫ U.isoSpec.hom) rfl).hom.app
          ((Scheme.Modules.pullback E.s).obj F)) ≫
    scalarSectionsBaseChangeMap p.appTop ((E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop)
      (f₂ p f) (g₂ p f) pullback.condition ((Scheme.Modules.pullback E.s).obj F)

lemma baseChange₂_one_tmul (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (z : (ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
        ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F))) :
    baseChange₂ hcart F ((1 : Γ(U, ⊤)) ⊗ₜ[Γ(S, ⊤), p.appTop.hom] z) =
      gpull (g₂ p f) _ (baseChange hcart F z) := by
  unfold baseChange₂
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul, scalarSectionsBaseChangeMap_one_tmul]
  rfl

lemma isIso_baseChange₂ [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p)
    (F : E.U.Modules) (hF : IsLocallyFreeRankOne F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] : IsIso (baseChange₂ hcart F) := by
  have : IsAffineHom E.s := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_symm p f hcart).flip (inferInstance : IsAffineHom p)
  have : CompactSpace E.R := QuasiCompact.compactSpace_of_compactSpace E.s
  have : QuasiSeparatedSpace E.R := quasiSeparatedSpace_of_quasiSeparated E.s
  have := isIso_baseChange p f hcart F hF
  have : IsAffineHom (g₂ p f) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip (inferInstance : IsAffineHom (Spec.map p.appTop))
  have := Modules.CechResolution.isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs p.appTop
    ((E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map p.appTop) (f₂ p f) (g₂ p f) pullback.condition
    ⟨(Scheme.Modules.pullback E.s).obj F, hF.pullback E.s⟩ (IsPullback.of_hasPullback _ _)
    p.flat_appTop
  unfold baseChange₂
  infer_instance


variable {p f} in
/-- The base-change comparison for the chart, as an isomorphism. -/
def baseChangeIso [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (hF : IsLocallyFreeRankOne F) [CompactSpace E.U] [QuasiSeparatedSpace E.U] :
    (ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
      ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)) ≅
    (relativeGlobalSections (E.t ≫ f ≫ U.isoSpec.hom)).obj ((Scheme.Modules.pullback E.s).obj F) :=
  haveI := isIso_baseChange p f hcart F hF
  asIso (baseChange hcart F)

lemma baseChangeIso_hom [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p)
    (F : E.U.Modules) (hF : IsLocallyFreeRankOne F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] : (baseChangeIso hcart F hF).hom = baseChange hcart F := rfl

lemma baseChange_homEquiv (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (m : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :
    ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _ (baseChange hcart F)) m =
      gpull E.s F m := by
  unfold baseChange
  rw [Adjunction.homEquiv_naturality_left, scalarSectionsBaseChangeMap_homEquiv]
  rfl

lemma baseChange₂_homEquiv (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (z : (ModuleCat.extendScalars p.appTop.hom).obj ((ModuleCat.restrictScalars p.appTop.hom).obj
        ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F))) :
    ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _ (baseChange₂ hcart F)) z =
      gpull (g₂ p f) _ (baseChange hcart F z) := by
  unfold baseChange₂
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    scalarSectionsBaseChangeMap_homEquiv]
  rfl

lemma counit_eq (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) :
    (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).counit.app
        ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) =
      baseChange hcart F ≫ diagPull f F := by
  apply ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _).injective
  have h1 : (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _
      ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).counit.app
        ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  rw [h1, Adjunction.homEquiv_naturality_right]
  ext m
  have h2 := baseChange_homEquiv p f hcart F m
  rw [ModuleCat.comp_apply, h2]
  exact (diagPull_gpull f F m).symm

lemma delta_eq (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) :
    (ModuleCat.extendScalars p.appTop.hom).map
        ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
          ((ModuleCat.restrictScalars p.appTop.hom).obj
            ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F))) ≫ baseChange₂ hcart F =
      baseChange hcart F ≫ kPull hcart F := by
  apply ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  ext m
  have h2 := baseChange_homEquiv p f hcart F m
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  erw [baseChange₂_homEquiv, h2]
  exact (kPull_gpull p f hcart F m).symm

lemma map_eq [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (hF : IsLocallyFreeRankOne F) (D : EquivariantModule E F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] :
    (ModuleCat.extendScalars p.appTop.hom).map ((ModuleCat.restrictScalars p.appTop.hom).map
        (transportPull f F D ≫ (baseChangeIso hcart F hF).inv)) ≫ baseChange₂ hcart F =
      baseChange hcart F ≫ lPull hcart F D := by
  apply ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _).injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.ExtendScalars.map_tmul]
  erw [baseChange₂_one_tmul, baseChange_one_tmul]
  have key : baseChange hcart F ((transportPull f F D ≫ (baseChangeIso hcart F hF).inv) m) =
      transportPull f F D m := by
    rw [← baseChangeIso_hom p f hcart F hF, ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      Iso.inv_hom_id, ModuleCat.id_apply]
  refine (congrArg _ key).trans ?_
  exact (congrArg _ (transportPull_apply f F D m)).trans (lPull_gpull p f hcart F D m).symm

variable {p f} in
/-- The descent coalgebra on the sections of an equivariant line bundle. -/
def coalgebra [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules)
    (hF : IsLocallyFreeRankOne F) (D : EquivariantModule E F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] :
    (FaithfullyFlatCoalgebraDescent.descentComonad p.appTop.hom).Coalgebra where
  A := (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F
  a := transportPull f F D ≫ (baseChangeIso hcart F hF).inv
  counit := by
    change (transportPull f F D ≫ (baseChangeIso hcart F hF).inv) ≫
      (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).counit.app _ = 𝟙 _
    rw [Category.assoc, counit_eq p f hcart F, ← baseChangeIso_hom p f hcart F hF,
      Iso.inv_hom_id_assoc]
    ext m
    exact (congrArg _ (transportPull_apply f F D m)).trans (diagPull_tr f F D m)
  coassoc := by
    have := isIso_baseChange₂ p f hcart F hF
    change (transportPull f F D ≫ (baseChangeIso hcart F hF).inv) ≫
        (ModuleCat.extendScalars p.appTop.hom).map
          ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
            ((ModuleCat.restrictScalars p.appTop.hom).obj
              ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F))) =
      (transportPull f F D ≫ (baseChangeIso hcart F hF).inv) ≫
        (ModuleCat.extendScalars p.appTop.hom).map ((ModuleCat.restrictScalars p.appTop.hom).map
          (transportPull f F D ≫ (baseChangeIso hcart F hF).inv))
    rw [← cancel_mono (baseChange₂ hcart F)]
    simp only [Category.assoc]
    rw [delta_eq p f hcart F, map_eq p f hcart F hF D, ← baseChangeIso_hom p f hcart F hF,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    ext m
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    exact (congrArg _ (transportPull_apply f F D m)).trans
      ((kPull_tr_eq_lPull_tr p f hcart F D m).trans (congrArg _ (transportPull_apply f F D m)).symm)

lemma tr_eq_of_mem_coinvariants [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p)
    (F : E.U.Modules) (hF : IsLocallyFreeRankOne F) (D : EquivariantModule E F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] (c : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)
    (hc : c ∈ FaithfullyFlatCoalgebraDescent.coinvariants p.appTop.hom
      (coalgebra hcart F hF D)) :
    D.tr E.t E.s (related_t_s E) c = gpull E.s F c := by
  have h1 : (transportPull f F D ≫ (baseChangeIso hcart F hF).inv) c =
      (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
        ((ModuleCat.restrictScalars p.appTop.hom).obj
          ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)) c := hc
  have h2 : baseChange hcart F ((transportPull f F D ≫ (baseChangeIso hcart F hF).inv) c) =
      transportPull f F D c := by
    rw [← baseChangeIso_hom p f hcart F hF, ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      Iso.inv_hom_id, ModuleCat.id_apply]
  have h3 : baseChange hcart F ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
        ((ModuleCat.restrictScalars p.appTop.hom).obj
          ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)) c) =
      gpull E.s F c := by
    rw [← baseChange_homEquiv p f hcart F c, Adjunction.homEquiv_unit]
    rfl
  rw [← transportPull_apply f F D c, ← h2, h1, h3]

lemma invariant_of_mem_coinvariants [Flat p] (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p)
    (F : E.U.Modules) (hF : IsLocallyFreeRankOne F) (D : EquivariantModule E F) [CompactSpace E.U]
    [QuasiSeparatedSpace E.U] (c : (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F)
    (hc : c ∈ FaithfullyFlatCoalgebraDescent.coinvariants p.appTop.hom
      (coalgebra hcart F hF D)) :
    E.s ⁻¹ᵁ Langlands.SchemeModule.trivializationOpen F c =
      E.t ⁻¹ᵁ Langlands.SchemeModule.trivializationOpen F c := by
  let L : LineBundle E.U := ⟨F, hF⟩
  have ht := Langlands.SchemeModule.lineBundlePullbackSectionOpen E.U E.R E.t L c
  have hs := Langlands.SchemeModule.lineBundlePullbackSectionOpen E.U E.R E.s L c
  rw [Langlands.SchemeModule.pullbackSection_eq_sectionPullback] at ht hs
  change _ = E.s ⁻¹ᵁ _ at hs
  change _ = E.t ⁻¹ᵁ _ at ht
  rw [← hs, ← ht, ← Langlands.SchemeModule.trivializationOpen_mapIso
    (D.transport E.t E.s (related_t_s E))]
  have := tr_eq_of_mem_coinvariants p f hcart F hF D c hc
  exact congrArg _ this.symm


lemma faithfullyFlat_appTop [Flat p] [Surjective p] : p.appTop.hom.FaithfullyFlat := by
  have : Surjective (Spec.map p.appTop) := by
    have e : Spec.map p.appTop = U.isoSpec.inv ≫ p ≫ S.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨p.flat_appTop, (Spec.map p.appTop).surjective⟩

variable {p f} in
/-- The sections vanishing at a point, as a submodule over the cover ring. -/
def vanishingAt (F : E.U.Modules) (x : E.U) :
    Submodule Γ(U, ⊤) ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) where
  carrier := {m | Langlands.SchemeModule.residueSection F m x = 0}
  add_mem' {a b} ha hb := by
    change Langlands.SchemeModule.residueSection F (a + b) x = 0
    rw [FiniteSectionAvoidance.residueSection_add]
    change Langlands.SchemeModule.residueSection F a x = 0 at ha
    change Langlands.SchemeModule.residueSection F b x = 0 at hb
    rw [ha, hb, add_zero]
  zero_mem' := residueSection_zero F x
  smul_mem' b m hm := by
    change Langlands.SchemeModule.residueSection F
      (structureRingHom (f ≫ U.isoSpec.hom) b •
        (show Langlands.SchemeModule.GlobalSections F from m)) x = 0
    rw [residueSection_smul]
    change Langlands.SchemeModule.residueSection F m x = 0 at hm
    rw [hm, smul_zero]

/-- **Invariant sections.** Every point of a generation open of a section of an equivariant line
bundle lies in the generation open of a section whose generation open is invariant. -/
theorem exists_invariant_section [Flat p] [Surjective p]
    (hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p) (F : E.U.Modules) (hF : IsLocallyFreeRankOne F)
    (D : EquivariantModule E F) [CompactSpace E.U] [QuasiSeparatedSpace E.U]
    (σ : Langlands.SchemeModule.GlobalSections F) (x : E.U)
    (hx : x ∈ Langlands.SchemeModule.trivializationOpen F σ) :
    ∃ c : Langlands.SchemeModule.GlobalSections F,
      x ∈ Langlands.SchemeModule.trivializationOpen F c ∧
        E.s ⁻¹ᵁ Langlands.SchemeModule.trivializationOpen F c =
          E.t ⁻¹ᵁ Langlands.SchemeModule.trivializationOpen F c := by
  let L : LineBundle E.U := ⟨F, hF⟩
  have hres : ∀ c : Langlands.SchemeModule.GlobalSections F,
      x ∈ Langlands.SchemeModule.trivializationOpen F c ↔
        Langlands.SchemeModule.residueSection F c x ≠ 0 := by
    intro c
    rw [← SetLike.mem_coe, ← Langlands.SchemeModule.lineBundleResidueOpenComparison E.U L c]
    rfl
  by_contra hne
  push Not at hne
  let Z : Submodule Γ(U, ⊤) ((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) :=
    vanishingAt F x
  let π := ModuleCat.ofHom Z.mkQ
  have hcoinv : ∀ c ∈ FaithfullyFlatCoalgebraDescent.coinvariants p.appTop.hom
      (coalgebra hcart F hF D), c ∈ Z := by
    intro c hc
    have hinv := invariant_of_mem_coinvariants p f hcart F hF D c hc
    by_contra hcZ
    exact hne c ((hres c).mpr hcZ) hinv
  have hzero : FaithfullyFlatCoalgebraDescent.descentMap p.appTop.hom
      (coalgebra hcart F hF D) ≫ π = 0 := by
    apply ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _).injective
    have h0 : (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _
        (0 : (ModuleCat.extendScalars p.appTop.hom).obj (ModuleCat.of Γ(S, ⊤)
          (FaithfullyFlatCoalgebraDescent.coinvariants p.appTop.hom (coalgebra hcart F hF D))) ⟶
            ModuleCat.of Γ(U, ⊤) (((relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F) ⧸ Z)) =
          0 := by
      rw [Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
    rw [h0, Adjunction.homEquiv_naturality_right]
    unfold FaithfullyFlatCoalgebraDescent.descentMap
    rw [Equiv.apply_symm_apply]
    ext ⟨c, hc⟩
    show Z.mkQ c = 0
    exact (Submodule.Quotient.mk_eq_zero Z).mpr (hcoinv c hc)
  obtain ⟨y, hy⟩ := (FaithfullyFlatCoalgebraDescent.bijective_descentMap p.appTop.hom
    (faithfullyFlat_appTop p) (coalgebra hcart F hF D)).2 σ
  have hσ : σ ∈ Z := by
    have h1 := congrArg (fun g => g y) hzero
    simp only at h1
    rw [ModuleCat.comp_apply, hy] at h1
    change Z.mkQ σ = 0 at h1
    exact (Submodule.Quotient.mk_eq_zero Z).mp h1
  exact (hres σ).mp hx hσ


end Coalgebra

end EquivariantModule

end Langlands.AlgebraicGeometry.Picard
