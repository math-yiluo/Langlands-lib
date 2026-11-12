import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesFlatSeparated
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassDescentData
import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof

/-! # Separation and descent of line bundles rigidified along a morphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SubschemeRigidification

open Langlands.SchemeModule Langlands.SchemeModule.RigidifiedModule

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (z : Z ⟶ X) (hz : z ≫ f = g)

/-- Comparison of iterated relative pullback with pullback along an equal composite. -/
def relativePullbackCompTo {T U V : Over S} (h : U ⟶ T) (k : V ⟶ U) (m : V ⟶ T)
    (hk : k ≫ h = m) :
    relativePullback f g z hz h ⋙ relativePullback f g z hz k ≅
      relativePullback f g z hz m := by
  subst m
  exact relativePullbackComp f g z hz k h

/-- The comparison has the equal-composite module comparison underneath. -/
lemma relativePullbackCompTo_hom_val {T U V : Over S} (h : U ⟶ T) (k : V ⟶ U) (m : V ⟶ T)
    (hk : k ≫ h = m) (L : relative f g z hz T) :
    ((relativePullbackCompTo f g z hz h k m hk).hom.app L).hom.val =
      compHom ((relativeSpace f).map k) ((relativeSpace f).map h) ((relativeSpace f).map m)
        (((relativeSpace f).map_comp k h).symm.trans
          (congrArg (relativeSpace f).map hk)) L.obj.carrier := by
  subst m
  change _ ≫ ((RigidifiedLineBundle.pullbackCongr _ _ _ _).hom.app L).hom.val = _
  rw [pullbackCongr_hom_val]
  rfl

variable (unique : ∀ (T : Over S) (L M : relative f g z hz T), Subsingleton (L ≅ M))

include unique in
/-- Uniqueness identifies local isomorphisms after comparison with a common base pullback. -/
lemma rigidified_common_map {T U V W : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (a : W ⟶ U) (b : W ⟶ V) (w : W ⟶ T)
    (ha : a ≫ h = w) (hb : b ≫ k = w) (L M : relative f g z hz T)
    (ei : (relativePullback f g z hz h).obj L ≅ (relativePullback f g z hz h).obj M)
    (ej : (relativePullback f g z hz k).obj L ≅ (relativePullback f g z hz k).obj M) :
    ∃ r : (Scheme.Modules.pullback ((relativeSpace f).map w)).obj L.obj.carrier ⟶
        (Scheme.Modules.pullback ((relativeSpace f).map w)).obj M.obj.carrier,
      (Scheme.Modules.pullback ((relativeSpace f).map a)).map ei.hom.hom.val ≫
          compHom ((relativeSpace f).map a) ((relativeSpace f).map h)
            ((relativeSpace f).map w)
            (((relativeSpace f).map_comp a h).symm.trans
              (congrArg (relativeSpace f).map ha)) M.obj.carrier =
        compHom ((relativeSpace f).map a) ((relativeSpace f).map h)
          ((relativeSpace f).map w)
          (((relativeSpace f).map_comp a h).symm.trans
            (congrArg (relativeSpace f).map ha)) L.obj.carrier ≫ r ∧
      (Scheme.Modules.pullback ((relativeSpace f).map b)).map ej.hom.hom.val ≫
          compHom ((relativeSpace f).map b) ((relativeSpace f).map k)
            ((relativeSpace f).map w)
            (((relativeSpace f).map_comp b k).symm.trans
              (congrArg (relativeSpace f).map hb)) M.obj.carrier =
        compHom ((relativeSpace f).map b) ((relativeSpace f).map k)
          ((relativeSpace f).map w)
          (((relativeSpace f).map_comp b k).symm.trans
            (congrArg (relativeSpace f).map hb)) L.obj.carrier ≫ r := by
  let Ci := relativePullbackCompTo f g z hz h a w ha
  let Cj := relativePullbackCompTo f g z hz k b w hb
  let ri := (Ci.app L).symm ≪≫ (relativePullback f g z hz a).mapIso ei ≪≫ Ci.app M
  let rj := (Cj.app L).symm ≪≫ (relativePullback f g z hz b).mapIso ej ≪≫ Cj.app M
  have he : ri = rj := (unique W _ _).elim ri rj
  have hi : (relativePullback f g z hz a).map ei.hom ≫ Ci.hom.app M =
      Ci.hom.app L ≫ ri.hom := by
    simp [ri]
  have hj : (relativePullback f g z hz b).map ej.hom ≫ Cj.hom.app M =
      Cj.hom.app L ≫ ri.hom := by
    rw [he]
    simp [rj]
  refine ⟨ri.hom.hom.val, ?_, ?_⟩
  · have hh := congrArg (fun v ↦ v.hom.val) hi
    change (Scheme.Modules.pullback ((relativeSpace f).map a)).map ei.hom.hom.val ≫
      (Ci.hom.app M).hom.val = (Ci.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Ci, relativePullbackCompTo_hom_val] using hh
  · have hh := congrArg (fun v ↦ v.hom.val) hj
    change (Scheme.Modules.pullback ((relativeSpace f).map b)).map ej.hom.hom.val ≫
      (Cj.hom.app M).hom.val = (Cj.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Cj, relativePullbackCompTo_hom_val] using hh

include unique in
/-- Local rigidified isomorphisms agree on the total-space overlap. -/
lemma rigidified_overlap_compatible {T U V : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (L M : relative f g z hz T)
    (ei : (relativePullback f g z hz h).obj L ≅ (relativePullback f g z hz h).obj M)
    (ej : (relativePullback f g z hz k).obj L ≅ (relativePullback f g z hz k).obj M) :
    (Scheme.Modules.pullback (pullback.fst ((relativeSpace f).map h)
      ((relativeSpace f).map k))).map ei.hom.hom.val ≫
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace f).map k)
          (pullback.fst ((relativeSpace f).map h) ((relativeSpace f).map k))
          (pullback.snd ((relativeSpace f).map h) ((relativeSpace f).map k))
          ((relativeSpace f).map h) pullback.condition M.obj.carrier).hom =
      (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace f).map k)
        (pullback.fst ((relativeSpace f).map h) ((relativeSpace f).map k))
        (pullback.snd ((relativeSpace f).map h) ((relativeSpace f).map k))
        ((relativeSpace f).map h) pullback.condition L.obj.carrier).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeSpace f).map h)
            ((relativeSpace f).map k))).map ej.hom.hom.val := by
  obtain ⟨r, hi, hj⟩ := rigidified_common_map f g z hz unique h k (pullback.fst h k)
    (pullback.snd h k) (pullback.fst h k ≫ h) rfl pullback.condition.symm L M ei ej
  exact Langlands.Scheme.Modules.square_compatible_of_common_map _ _ _ _ pullback.condition
    (PreservesPullback.iso (relativeSpace f) h k) _ _ _
    (PreservesPullback.iso_hom_fst _ _ _) (PreservesPullback.iso_hom_snd _ _ _)
    _ _ L.obj.carrier M.obj.carrier ei.hom.hom.val ej.hom.hom.val r hi hj

include unique in
/-- Compatible local rigidified isomorphisms on an open cover glue. -/
lemma rigidified_iso_of_local_isos
    (glue : Langlands.Scheme.Modules.OpenCoverHomGluingStatement.{u})
    (T : Over S) (𝒰 : T.left.OpenCover.{u}) (L M : relative f g z hz T)
    (ei : ∀ i, (relativePullback f g z hz
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
        (relativePullback f g z hz
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :
    Nonempty (L ≅ M) := by
  let 𝒱 := RigidifiedLineBundle.relativeOpenCover f T 𝒰
  let e' : ∀ i, (Scheme.Modules.pullback (𝒱.f i)).obj L.obj.carrier ≅
      (Scheme.Modules.pullback (𝒱.f i)).obj M.obj.carrier := fun i ↦
    (RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso (ei i)
  obtain ⟨e, he, _⟩ := Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing glue _ 𝒱
    L.obj.carrier M.obj.carrier e' (fun i j ↦
      rigidified_overlap_compatible f g z hz unique _ _ L M (ei i) (ei j))
  refine ⟨RigidifiedLineBundle.isoMk e ?_⟩
  apply Langlands.Scheme.Modules.hom_ext_of_openCover glue
    (RigidifiedLineBundle.relativeOpenCover g T 𝒰)
  intro i
  apply RigidifiedModule.rigidification_compatibility_of_pullback
    ((relativeSpace f).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))
    ((relativeSpace g).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))
    ((zRel f g z hz).naturality
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).symm L.obj M.obj e.hom
  have hei : (Scheme.Modules.pullback ((relativeSpace f).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))).map e.hom =
        (ei i).hom.hom.val := he i
  rw [hei]
  exact (ei i).hom.hom.property

include unique in
/-- Rigidified classes are determined on any open cover. -/
lemma classes_zariskiSeparated (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (q r : Classes f g z hz T)
    (h : ∀ i, classesPullback f g z hz
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q =
      classesPullback f g z hz
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) r) :
    q = r := by
  classical
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      apply Quotient.sound
      have hi : ∀ i, Nonempty (
          (relativePullback f g z hz
            (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
          (relativePullback f g z hz
            (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :=
        fun i ↦ Quotient.exact (h i)
      exact rigidified_iso_of_local_isos f g z hz unique
        Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing T 𝒰 L M
        (fun i ↦ Classical.choice (hi i))

/-- Separation for open covers gives separation for the big Zariski slice topology. -/
lemma isSeparated_zariski_over_of_openCover (P : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hP : ∀ (T : Over S) (𝒰 : T.left.OpenCover.{u}) (x y : P.obj (op T)),
      (∀ i, P.map (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T).op x =
        P.map (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T).op y) → x = y) :
    Presieve.IsSeparated (Scheme.zariskiTopology.over S) P := by
  intro T R hR fam x y hx hy
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  apply hP T 𝒰 x y
  intro i
  have hi : R (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) :=
    (Sieve.overEquiv_iff R (𝒰.f i)).mp (h𝒰 _ _ ⟨i⟩)
  rw [hx _ hi, hy _ hi]

include unique in
/-- The presheaf of rigidified classes is separated for the big Zariski topology. -/
lemma classPresheaf_isSeparated_zariski :
    Presieve.IsSeparated (Scheme.zariskiTopology.over S) (classPresheaf f g z hz) :=
  isSeparated_zariski_over_of_openCover _ fun T 𝒰 x y h ↦
    classes_zariskiSeparated f g z hz unique T 𝒰 x y h

section Descent

open Langlands.Scheme.Modules

namespace ClassDescent

variable {T U : Over S} (h : U ⟶ T) (L : relative f g z hz U)
  (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
    Nonempty ((relativePullback f g z hz a).obj L ≅ (relativePullback f g z hz b).obj L))

/-- A chosen rigidified comparison supplied by compatibility of the local class. -/
def compatibleIso {W : Over S} (a b : W ⟶ U) (hab : a ≫ h = b ≫ h) :
    (relativePullback f g z hz a).obj L ≅
      (relativePullback f g z hz b).obj L :=
  Classical.choice (compat W a b hab)

/-- Uniqueness supplies the cocycle law before passing to ordinary modules. -/
lemma compatibleIso_comp
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    {W : Over S} (a b c : W ⟶ U)
    (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h) (hac : a ≫ h = c ≫ h) :
    (compatibleIso f g z hz h L compat a b hab).hom.hom.val ≫
        (compatibleIso f g z hz h L compat b c hbc).hom.hom.val =
      (compatibleIso f g z hz h L compat a c hac).hom.hom.val := by
  have he := (unique W _ _).elim
    (compatibleIso f g z hz h L compat a b hab ≪≫
      compatibleIso f g z hz h L compat b c hbc)
    (compatibleIso f g z hz h L compat a c hac)
  exact congrArg (fun e ↦ e.hom.hom.val) he

/-- Chosen comparisons commute with relative pullback, by uniqueness. -/
lemma compatibleIso_precomp
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    {W W' : Over S} (t : W' ⟶ W) (a b : W ⟶ U) (a' b' : W' ⟶ U)
    (ha : t ≫ a = a') (hb : t ≫ b = b')
    (hab : a ≫ h = b ≫ h) (hab' : a' ≫ h = b' ≫ h) :
    (compatibleIso f g z hz h L compat a' b' hab').hom.hom.val =
      Langlands.Scheme.Modules.transport (C := L.obj.carrier) (D := L.obj.carrier)
        ((relativeSpace f).map t)
        (((relativeSpace f).map_comp t a).symm.trans (congrArg (relativeSpace f).map ha))
        (((relativeSpace f).map_comp t b).symm.trans (congrArg (relativeSpace f).map hb))
        (compatibleIso f g z hz h L compat a b hab).hom.hom.val := by
  let Ca := relativePullbackCompTo f g z hz a t a' ha
  let Cb := relativePullbackCompTo f g z hz b t b' hb
  let e := (Ca.app L).symm ≪≫
    (relativePullback f g z hz t).mapIso
      (compatibleIso f g z hz h L compat a b hab) ≪≫ Cb.app L
  have he : e = compatibleIso f g z hz h L compat a' b' hab' :=
    (unique W' _ _).elim _ _
  have hi : (relativePullback f g z hz t).map
        (compatibleIso f g z hz h L compat a b hab).hom ≫ Cb.hom.app L =
      Ca.hom.app L ≫ (compatibleIso f g z hz h L compat a' b' hab').hom := by
    rw [← he]
    simp [e]
  have hv := congrArg (fun w ↦ w.hom.val) hi
  change (Scheme.Modules.pullback ((relativeSpace f).map t)).map
        (compatibleIso f g z hz h L compat a b hab).hom.hom.val ≫
      (Cb.hom.app L).hom.val =
    (Ca.hom.app L).hom.val ≫
      (compatibleIso f g z hz h L compat a' b' hab').hom.hom.val at hv
  have hCa : (Ca.hom.app L).hom.val =
      (compIso ((relativeSpace f).map t) ((relativeSpace f).map a)
        ((relativeSpace f).map a')
        (((relativeSpace f).map_comp t a).symm.trans (congrArg (relativeSpace f).map ha))
        L.obj.carrier).hom := by
    exact (relativePullbackCompTo_hom_val f g z hz a t a' ha L).trans
      (compIso_hom _ _ _ _ _).symm
  have hCb : (Cb.hom.app L).hom.val =
      (compIso ((relativeSpace f).map t) ((relativeSpace f).map b)
        ((relativeSpace f).map b')
        (((relativeSpace f).map_comp t b).symm.trans (congrArg (relativeSpace f).map hb))
        L.obj.carrier).hom := by
    exact (relativePullbackCompTo_hom_val f g z hz b t b' hb L).trans
      (compIso_hom _ _ _ _ _).symm
  rw [hCa, hCb] at hv
  rw [← cancel_epi (compIso ((relativeSpace f).map t) ((relativeSpace f).map a)
    ((relativeSpace f).map a')
    (((relativeSpace f).map_comp t a).symm.trans (congrArg (relativeSpace f).map ha))
    L.obj.carrier).hom]
  simp only [Langlands.Scheme.Modules.transport, Iso.hom_inv_id_assoc]
  exact hv.symm

/-- Comparison for two lifts of a common total-space map, obtained by pulling back
an actual rigidified isomorphism along the point section. -/
def thetaCommon {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r) :
    (Scheme.Modules.pullback a).obj L.obj.carrier ≅
      (Scheme.Modules.pullback b).obj L.obj.carrier :=
  (compIso (relativePointSection f r)
      ((relativeSpace f).map (pointLift f h r a ha)) a
      (pointLift_section f h r a ha) L.obj.carrier).symm ≪≫
    (Scheme.Modules.pullback (relativePointSection f r)).mapIso
      ((RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso
        (compatibleIso f g z hz h L compat
          (pointLift f h r a ha) (pointLift f h r b hb)
          (pointLift_comp f h r a b ha hb))) ≪≫
    compIso (relativePointSection f r)
      ((relativeSpace f).map (pointLift f h r b hb)) b
      (pointLift_section f h r b hb) L.obj.carrier

lemma thetaCommon_hom {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r) :
    (thetaCommon f g z hz h L compat r a b ha hb).hom =
      Langlands.Scheme.Modules.transport (relativePointSection f r) (pointLift_section f h r a ha)
        (pointLift_section f h r b hb)
        (compatibleIso f g z hz h L compat
          (pointLift f h r a ha) (pointLift f h r b hb)
          (pointLift_comp f h r a b ha hb)).hom.hom.val := rfl

/-- The common-point comparisons satisfy the cocycle law. -/
lemma thetaCommon_comp
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b c : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hc : c ≫ (relativeSpace f).map h = r) :
    (thetaCommon f g z hz h L compat r a b ha hb).hom ≫
        (thetaCommon f g z hz h L compat r b c hb hc).hom =
      (thetaCommon f g z hz h L compat r a c ha hc).hom := by
  simp only [thetaCommon_hom]
  rw [← Langlands.Scheme.Modules.transport_comp, compatibleIso_comp f g z hz h L compat unique]

/-- Common-point comparisons commute with arbitrary precomposition. -/
lemma thetaCommon_precomp
    (unique : ∀ (B : Over S) (M N : relative f g z hz B), Subsingleton (M ≅ N))
    {V W : Scheme.{u}} (k : W ⟶ V) (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hka : (k ≫ a) ≫ (relativeSpace f).map h = k ≫ r)
    (hkb : (k ≫ b) ≫ (relativeSpace f).map h = k ≫ r) :
    (thetaCommon f g z hz h L compat (k ≫ r) (k ≫ a) (k ≫ b) hka hkb).hom =
      Langlands.Scheme.Modules.transport k rfl rfl
        (thetaCommon f g z hz h L compat r a b ha hb).hom := by
  have he := compatibleIso_precomp f g z hz h L compat unique
    (pointBaseMap f k r) (pointLift f h r a ha) (pointLift f h r b hb)
    (pointLift f h (k ≫ r) (k ≫ a) hka) (pointLift f h (k ≫ r) (k ≫ b) hkb)
    (pointLift_precomp f h k r a ha hka) (pointLift_precomp f h k r b hb hkb)
    (pointLift_comp f h r a b ha hb)
    (pointLift_comp f h (k ≫ r) (k ≫ a) (k ≫ b) hka hkb)
  rw [thetaCommon_hom, he, thetaCommon_hom]
  rw [Langlands.Scheme.Modules.transport_transport_eq _ _ (pointSection_precomp f k r),
    Langlands.Scheme.Modules.transport_transport]
  all_goals simp only [Category.assoc, pointLift_section]

/-- Ordinary descent comparisons attached to a compatible rigidified class. -/
def theta (V : Scheme.{u}) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    (Scheme.Modules.pullback a).obj L.obj.carrier ≅
      (Scheme.Modules.pullback b).obj L.obj.carrier :=
  thetaCommon f g z hz h L compat (a ≫ (relativeSpace f).map h) a b rfl hab.symm

lemma theta_eq_common {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    theta f g z hz h L compat V a b hab =
      thetaCommon f g z hz h L compat r a b ha hb := by
  subst r
  rfl

/-- The ordinary comparisons satisfy the full module descent cocycle law. -/
lemma theta_comp
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    (V : Scheme.{u}) (a b c : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h)
    (hbc : b ≫ (relativeSpace f).map h = c ≫ (relativeSpace f).map h)
    (hac : a ≫ (relativeSpace f).map h = c ≫ (relativeSpace f).map h) :
    (theta f g z hz h L compat V a b hab).hom ≫
        (theta f g z hz h L compat V b c hbc).hom =
      (theta f g z hz h L compat V a c hac).hom := by
  rw [theta_eq_common f g z hz h L compat _ a b rfl hab.symm,
    theta_eq_common f g z hz h L compat _ b c hab.symm hac.symm,
    theta_eq_common f g z hz h L compat _ a c rfl hac.symm]
  exact thetaCommon_comp f g z hz h L compat unique _ a b c rfl hab.symm hac.symm

/-- The comparisons have exactly the naturality required by module descent. -/
lemma theta_precomp
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    (V W : Scheme.{u}) (k : W ⟶ V) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h)
    (hab' : (k ≫ a) ≫ (relativeSpace f).map h = (k ≫ b) ≫ (relativeSpace f).map h) :
    (theta f g z hz h L compat W (k ≫ a) (k ≫ b) hab').hom =
      (Scheme.Modules.pullbackComp k a).inv.app L.obj.carrier ≫
        (Scheme.Modules.pullback k).map (theta f g z hz h L compat V a b hab).hom ≫
          (Scheme.Modules.pullbackComp k b).hom.app L.obj.carrier := by
  have hka : (k ≫ a) ≫ (relativeSpace f).map h = k ≫ (a ≫ (relativeSpace f).map h) :=
    Category.assoc _ _ _
  have hkb : (k ≫ b) ≫ (relativeSpace f).map h = k ≫ (a ≫ (relativeSpace f).map h) := by
    rw [Category.assoc, hab]
  rw [theta_eq_common f g z hz h L compat _ (k ≫ a) (k ≫ b) hka hkb,
    theta_eq_common f g z hz h L compat _ a b rfl hab.symm,
    thetaCommon_precomp f g z hz h L compat unique k]
  rfl

include compat in
/-- Explicit module descent descends the ordinary carrier of the compatible class. -/
lemma exists_carrier
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (W : Over S) (M N : relative f g z hz W), Subsingleton (M ≅ N))
    [IsAffineHom h.left] [Flat h.left] [Surjective h.left] :
    ∃ M : LineBundle ((relativeSpace f).obj T),
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map h)).obj M.obj ≅
        L.obj.carrier) := by
  obtain ⟨M, hM, e⟩ := hD2 _ _ ((relativeSpace f).map h)
    (relativeSpace_map_isAffineHom f h) (relativeSpace_map_flat f h)
    (relativeSpace_map_surjective f h) L.obj.carrier L.property
    (theta f g z hz h L compat)
    (theta_precomp f g z hz h L compat unique)
    (theta_comp f g z hz h L compat unique)
  exact ⟨⟨M, hM⟩, e⟩


end ClassDescent

end Descent

section Flat

open Langlands.Scheme.Modules

include unique in
/-- A relative rigidified isomorphism satisfies the full module descent condition. -/
lemma relative_iso_descent_compatible {T U : Over S} (h : U ⟶ T) (L M : relative f g z hz T)
    (e : (relativePullback f g z hz h).obj L ≅ (relativePullback f g z hz h).obj M)
    (V : Scheme.{u}) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    (Scheme.Modules.pullback a).map e.hom.hom.val ≫
        (equalCompositeIso ((relativeSpace f).map h) a b hab M.obj.carrier).hom =
      (equalCompositeIso ((relativeSpace f).map h) a b hab L.obj.carrier).hom ≫
        (Scheme.Modules.pullback b).map e.hom.hom.val := by
  apply equalComposite_compatible_of_pullback
  exact rigidified_overlap_compatible f g z hz unique h h L M e e

/-- Pullback along a quasi-compact faithfully flat morphism is faithful on isomorphisms of line
bundles. -/
lemma iso_eq_of_pullback_map_eq {X' Y' : Scheme.{u}} (p : X' ⟶ Y') [QuasiCompact p] [Flat p]
    [Surjective p] {M N : Y'.Modules} (hM : IsLocallyFreeRankOne M)
    (hN : IsLocallyFreeRankOne N) (e₁ e₂ : M ≅ N)
    (h : (Scheme.Modules.pullback p).map e₁.hom = (Scheme.Modules.pullback p).map e₂.hom) :
    e₁ = e₂ := by
  obtain ⟨e₀, -, huniq⟩ := LineBundleIsoDescent.lineBundleIsoDescent X' Y' p inferInstance
    inferInstance inferInstance M N hM hN ((Scheme.Modules.pullback p).mapIso e₁)
    (fun U a b hab ↦ equalCompositeIso_hom_naturality p a b hab e₁.hom)
  have h₁ := huniq e₁ rfl
  have h₂ := huniq e₂ (Iso.ext h.symm)
  rw [h₁, h₂]

include unique in
/-- Rigidified classes are separated along quasi-compact faithfully flat maps. -/
lemma classes_flatSeparated {T U : Over S} (h : U ⟶ T) [QuasiCompact h.left] [Flat h.left]
    [Surjective h.left] (q r : Classes f g z hz T)
    (he : classesPullback f g z hz h q = classesPullback f g z hz h r) : q = r := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      obtain ⟨e⟩ := Quotient.exact he
      apply Quotient.sound
      have := relativeSpace_map_quasiCompact f h
      have := relativeSpace_map_flat f h
      have := relativeSpace_map_surjective f h
      have := relativeSpace_map_quasiCompact g h
      have := relativeSpace_map_flat g h
      have := relativeSpace_map_surjective g h
      obtain ⟨ψ, hψ, -⟩ := LineBundleIsoDescent.lineBundleIsoDescent _ _
        ((relativeSpace f).map h) inferInstance inferInstance inferInstance
        L.obj.carrier M.obj.carrier L.property M.property
        ((RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso e)
        (relative_iso_descent_compatible f g z hz unique h L M e)
      refine ⟨RigidifiedLineBundle.isoMk ψ ?_⟩
      have hψ' : (Scheme.Modules.pullback ((relativeSpace f).map h)).map ψ.hom =
          e.hom.hom.val := congrArg Iso.hom hψ
      have hcomp := RigidifiedModule.rigidification_compatibility_of_pullback
        ((relativeSpace f).map h) ((relativeSpace g).map h)
        ((zRel f g z hz).naturality h).symm L.obj M.obj ψ.hom (by
          rw [hψ']
          exact e.hom.hom.property)
      have hN : IsLocallyFreeRankOne
          ((Scheme.Modules.pullback ((zRel f g z hz).app T)).obj M.obj.carrier) :=
        M.property.pullback _
      have := iso_eq_of_pullback_map_eq ((relativeSpace g).map h)
        (LineBundle.trivial _).property hN
        (L.obj.rigidification ≪≫ (Scheme.Modules.pullback _).mapIso ψ)
        M.obj.rigidification hcomp
      exact congrArg Iso.hom this

include unique in
/-- Descent data of rigidified classes along affine faithfully flat maps descend to ordinary
line-bundle classes. -/
lemma exists_descended_class {U V : Over S} (m : U ⟶ V) [IsAffineHom m.left] [Flat m.left]
    [Surjective m.left] (p : (classPresheaf f g z hz).obj (op U))
    (hp : ∀ ⦃W : Over S⦄ (a b : W ⟶ U), a ≫ m = b ≫ m →
      (classPresheaf f g z hz).map a.op p = (classPresheaf f g z hz).map b.op p) :
    ∃ y : (RelativePicard.classPresheaf f).obj (op V),
      (RelativePicard.classPresheaf f).map m.op y = (forgetClassNatTrans f g z hz).app (op U) p := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep p
  have compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ m = b ≫ m →
      Nonempty ((relativePullback f g z hz a).obj L ≅ (relativePullback f g z hz b).obj L) :=
    fun W a b hab ↦ Quotient.exact (hp a b hab)
  obtain ⟨M, ⟨e⟩⟩ := ClassDescent.exists_carrier f g z hz m L compat lineBundleDescentEffective
    unique
  refine ⟨RelativePicard.classOf f V M, ?_⟩
  rw [RelativePicard.map_classOf]
  exact (RelativePicard.classOf_eq_iff_iso f U _ _).2 ⟨ObjectProperty.isoMk _ e⟩

end Flat

end Langlands.AlgebraicGeometry.Picard.SubschemeRigidification
