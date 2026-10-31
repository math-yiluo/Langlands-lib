import Langlands.AlgebraicGeometry.Picard.UniversalMumfordClassifierStatement
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackComparison
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # The Mumford classifier on a universal rigidified parameter -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.UniversalMumfordClassifier

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S) {P : Over S} (L : RigidifiedFamily A P)

/-- The unit section of `A_P`, read through the symmetry of the fibre product, is the canonical
section of the relative family over `P`. -/
lemma unitSection_comp_symmetry_inv :
    unitSection ((baseChange P.hom).obj A) ≫ (relativeSpaceSymmetry A.X.hom P).inv =
      𝟙 P.left ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app P := by
  dsimp only [relativeSpaceSymmetry]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst, Category.id_comp]
    exact (unitSection_comp ((baseChange P.hom).obj A)).trans
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) P).symm
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_snd, Category.id_comp,
      unitSection_baseChange_fst, relativeSection_snd]

/-- The universal family moved to the actual base change `A_P` over `P`. -/
def baseChangeBundle : RigidifiedLineBundle (unitSection ((baseChange P.hom).obj A)) :=
  (RigidifiedLineBundle.pullback (relativeSpaceSymmetry A.X.hom P).inv (𝟙 P.left)
    (unitSection_comp_symmetry_inv A)).obj L

section Point

variable {S' : Scheme.{u}} (B : AbelianScheme S') (Lb : RigidifiedLineBundle (unitSection B))
  (Mb : LineBundle B.X.left) (evb : tensorObj Lb.obj.carrier Mb.obj ≅ structureSheaf B.X.left)
  {K : Type u} [Field K] {b : Spec (CommRingCat.of K) ⟶ S'} (a : Over.mk b ⟶ B.X)
  (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange b).obj B).X)
  (hx : x.left ≫ pullback.fst B.X.hom b = a.left)

include hx in
/-- At a field-valued point `a` lying under the section `x` of the base change, the actual
Mumford family is trivial exactly when the translate of the restricted bundle by `x` is
isomorphic to the restricted bundle. -/
lemma nonempty_mumford_iso_trivial_iff :
    Nonempty ((RigidifiedLineBundle.relativePullback B.X.hom (unitSection B)
        (unitSection_comp B) a).obj (mumfordBundle B pullbackTensorComparisonIsIso Lb Mb evb) ≅
      RigidifiedLineBundle.relativeTrivial B.X.hom (unitSection B) (unitSection_comp B)
        (Over.mk b)) ↔
    Nonempty ((Scheme.Modules.pullback
        (GroupScheme.translation ((baseChange b).obj B).toGrp x).left).obj
          ((Scheme.Modules.pullback (pullback.fst B.X.hom b)).obj Lb.obj.carrier) ≅
      (Scheme.Modules.pullback (pullback.fst B.X.hom b)).obj Lb.obj.carrier) := by
  let σ := pullbackSymmetry b B.X.hom
  let i := pullback.fst B.X.hom b
  let t := (GroupScheme.translation ((baseChange b).obj B).toGrp x).left
  let evK : tensorObj ((Scheme.Modules.pullback i).obj Lb.obj.carrier)
      ((Scheme.Modules.pullback i).obj Mb.obj) ≅ structureSheaf _ :=
    pullbackTensorEvaluation pullbackTensorComparisonIsIso i _ _ evb
  let triv := (fieldLineBundleTriviality K ((LineBundle.pullback a.left).obj Mb)).some
  constructor
  · rintro ⟨r⟩
    let c := (LineBundle.forget _).mapIso ((RigidifiedLineBundle.forget _).mapIso r)
    let W := tensorObj ((Scheme.Modules.pullback t).obj
      ((Scheme.Modules.pullback i).obj Lb.obj.carrier)) ((Scheme.Modules.pullback i).obj Mb.obj)
    let Qc := (Scheme.Modules.pullback σ.hom).obj W
    let back : (Scheme.Modules.pullback σ.inv).obj Qc ≅ W :=
      (Scheme.Modules.pullbackComp σ.inv σ.hom).app W ≪≫
        (Scheme.Modules.pullbackCongr σ.inv_hom_id).app W ≪≫
          (Scheme.Modules.pullbackId _).app W
    let ci := FieldMumfordPoint.carrierIso B a pullbackTensorComparisonIsIso x hx
      Lb.obj.carrier Mb.obj Qc triv back.symm
    let hW : W ≅ structureSheaf _ :=
      back.symm ≪≫ (Scheme.Modules.pullback σ.inv).mapIso (ci.symm ≪≫ c) ≪≫
        pullbackUnitIso σ.inv
    exact ⟨tensorInverseComparisonIso _ _ _ (tensorComm _ _ ≪≫ hW)
      (tensorComm _ _ ≪≫ evK)⟩
  · rintro ⟨e⟩
    let premise : tensorObj ((Scheme.Modules.pullback t).obj
        ((Scheme.Modules.pullback i).obj Lb.obj.carrier))
          ((Scheme.Modules.pullback i).obj Mb.obj) ≅
        (Scheme.Modules.pullback σ.inv).obj (structureSheaf _) :=
      (tensorFunctor _).mapIso (e.prod (Iso.refl _)) ≪≫ evK ≪≫ (pullbackUnitIso σ.inv).symm
    exact ⟨RigidifiedLineBundle.trivialIsoOfCarrierIso ((relativeProjection B.X.hom).app _) _
      (relativeSection_projection _ _ _ _) _
      (FieldMumfordPoint.carrierIso B a pullbackTensorComparisonIsIso x hx
        Lb.obj.carrier Mb.obj _ triv premise)⟩

end Point

section Translation

variable {T : Scheme.{u}} {G H : GroupScheme T}

/-- Translates of a pulled-back module: if the translate by `x ≫ f` of `F` is isomorphic to
`F`, then the translate by `x` of `f^* F` is isomorphic to `f^* F`. -/
lemma nonempty_translate_pullback_iso (f : G ⟶ H) (x : Over.mk (𝟙 T) ⟶ G.X)
    (F : H.X.left.Modules)
    (h : Nonempty ((Scheme.Modules.pullback
      (GroupScheme.translation H (x ≫ f.hom.hom)).left).obj F ≅ F)) :
    Nonempty ((Scheme.Modules.pullback (GroupScheme.translation G x).left).obj
        ((Scheme.Modules.pullback f.hom.hom.left).obj F) ≅
      (Scheme.Modules.pullback f.hom.hom.left).obj F) := by
  obtain ⟨d⟩ := h
  have comm : (GroupScheme.translation G x).left ≫ f.hom.hom.left =
      f.hom.hom.left ≫ (GroupScheme.translation H (x ≫ f.hom.hom)).left :=
    congrArg (fun k ↦ k.left) (GroupScheme.translation_hom f x)
  exact ⟨(Scheme.Modules.pullbackComp _ _).app F ≪≫
    (Scheme.Modules.pullbackCongr comm).app F ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F).symm ≪≫
        (Scheme.Modules.pullback f.hom.hom.left).mapIso d⟩

/-- Along an isomorphism of group schemes, translation invariance at corresponding sections
is equivalent. -/
lemma nonempty_translate_pullback_iso_iff (f : G ≅ H) (x : Over.mk (𝟙 T) ⟶ G.X)
    (F : H.X.left.Modules) :
    Nonempty ((Scheme.Modules.pullback (GroupScheme.translation G x).left).obj
        ((Scheme.Modules.pullback f.hom.hom.hom.left).obj F) ≅
      (Scheme.Modules.pullback f.hom.hom.hom.left).obj F) ↔
    Nonempty ((Scheme.Modules.pullback
      (GroupScheme.translation H (x ≫ f.hom.hom.hom)).left).obj F ≅ F) := by
  refine ⟨fun h ↦ ?_, nonempty_translate_pullback_iso f.hom x F⟩
  have hcomp : f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun k : G ⟶ G ↦ k.hom.hom) f.hom_inv_id
  have hleft : f.inv.hom.hom.left ≫ f.hom.hom.hom.left = 𝟙 H.X.left :=
    congrArg (fun k : H ⟶ H ↦ k.hom.hom.left) f.inv_hom_id
  have hx : (x ≫ f.hom.hom.hom) ≫ f.inv.hom.hom = x := by
    rw [Category.assoc, hcomp, Category.comp_id]
  obtain ⟨d⟩ := nonempty_translate_pullback_iso f.inv (x ≫ f.hom.hom.hom)
    ((Scheme.Modules.pullback f.hom.hom.hom.left).obj F) (by rw [hx]; exact h)
  let c : (Scheme.Modules.pullback f.inv.hom.hom.left).obj
      ((Scheme.Modules.pullback f.hom.hom.hom.left).obj F) ≅ F :=
    (Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr hleft).app F ≪≫
      (Scheme.Modules.pullbackId _).app F
  exact ⟨(Scheme.Modules.pullback _).mapIso c.symm ≪≫ d ≪≫ c⟩

end Translation

variable (M : LineBundle ((baseChange P.hom).obj A).X.left)
  (ev : tensorObj (baseChangeBundle A L).obj.carrier M.obj ≅
    structureSheaf ((baseChange P.hom).obj A).X.left)

/-- The rigidified Mumford family of `A_P` for the moved universal family. -/
abbrev baseMumford :
    RigidifiedFamily ((baseChange P.hom).obj A) ((baseChange P.hom).obj A).X :=
  mumfordBundle ((baseChange P.hom).obj A) pullbackTensorComparisonIsIso
    (baseChangeBundle A L) M ev

/-- The Mumford family of `A_P`, viewed as a family of `A` over `A ×_S P`. -/
def mumfordFamily : RigidifiedFamily A ((Over.map P.hom).obj ((baseChange P.hom).obj A).X) :=
  (familyBaseChangeInverse P.hom A _).obj (baseMumford A L M ev)

/-- Pullbacks of the transported family along base-changed points are trivial exactly when the
corresponding pullbacks of the Mumford family of `A_P` are. -/
lemma nonempty_relativePullback_iso_trivial_iff {T : Over P.left}
    (a : T ⟶ ((baseChange P.hom).obj A).X) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) ((Over.map P.hom).map a)).obj (mumfordFamily A L M ev) ≅
      RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A)
        ((Over.map P.hom).obj T)) ↔
    Nonempty ((RigidifiedLineBundle.relativePullback ((baseChange P.hom).obj A).X.hom
        (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) a).obj
          (baseMumford A L M ev) ≅
      RigidifiedLineBundle.relativeTrivial ((baseChange P.hom).obj A).X.hom
        (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) T) := by
  let F := familyBaseChange P.hom A T
  have e1 : F.obj ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) ((Over.map P.hom).map a)).obj (mumfordFamily A L M ev)) ≅
      (RigidifiedLineBundle.relativePullback ((baseChange P.hom).obj A).X.hom
        (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) a).obj
          (baseMumford A L M ev) :=
    (familyBaseChangeNaturality P.hom A a).app _ ≪≫
      (RigidifiedLineBundle.relativePullback ((baseChange P.hom).obj A).X.hom
        (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) a).mapIso
          ((familyBaseChangeCounitIso P.hom A _).app _)
  have e2 : F.obj (RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A)
        (unitSection_comp A) ((Over.map P.hom).obj T)) ≅
      RigidifiedLineBundle.relativeTrivial ((baseChange P.hom).obj A).X.hom
        (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) T :=
    RigidifiedLineBundle.pullbackTrivialIso _ _ _
  constructor
  · rintro ⟨i⟩
    exact ⟨e1.symm ≪≫ F.mapIso i ≪≫ e2⟩
  · rintro ⟨i⟩
    exact ⟨(familyBaseChangeEquivalence P.hom A T).functor.preimageIso (e1 ≪≫ i ≪≫ e2.symm)⟩

variable (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)

/-- The classifying morphism of the transported Mumford family. -/
def classifierOver : (Over.map P.hom).obj ((baseChange P.hom).obj A).X ⟶ P :=
  RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) L hL
    (mumfordFamily A L M ev)

/-- A point of `A_P` over a `P.left`-scheme goes to the trivial parameter exactly when the
Mumford family of `A_P` is trivial there. -/
lemma comp_classifier_eq_iff {T : Over P.left} (a : T ⟶ ((baseChange P.hom).obj A).X) :
    a.left ≫ (classifierOver A L M ev hL).left =
        T.hom ≫ P.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
          (unitSection_comp A) L hL).left ↔
      Nonempty ((RigidifiedLineBundle.relativePullback ((baseChange P.hom).obj A).X.hom
          (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) a).obj
            (baseMumford A L M ev) ≅
        RigidifiedLineBundle.relativeTrivial ((baseChange P.hom).obj A).X.hom
          (unitSection ((baseChange P.hom).obj A)) (unitSection_comp _) T) := by
  rw [← nonempty_relativePullback_iso_trivial_iff]
  have h1 := (RigidifiedLineBundle.classifyFamily_pullback A.X.hom (unitSection A)
    (unitSection_comp A) L hL ((Over.map P.hom).map a) (mumfordFamily A L M ev)).symm
  have h2 := (RigidifiedLineBundle.classifyFamily_trivial A.X.hom (unitSection A)
    (unitSection_comp A) L hL ((Over.map P.hom).obj T)).symm
  constructor
  · intro h
    have h3 : (Over.map P.hom).map a ≫ classifierOver A L M ev hL =
        Over.mkIdTerminal.from _ ≫ RigidifiedLineBundle.trivialParameter A.X.hom
          (unitSection A) (unitSection_comp A) L hL := by
      apply Over.OverMorphism.ext
      simpa using h
    rw [classifierOver, h1, h2] at h3
    exact ⟨RigidifiedLineBundle.isoOfClassifyFamilyEq _ _ _ L hL _ _ h3⟩
  · rintro ⟨i⟩
    have h3 := RigidifiedLineBundle.classifyFamily_eq_of_iso A.X.hom (unitSection A)
      (unitSection_comp A) L hL i
    rw [← h1, ← h2] at h3
    simpa [classifierOver] using congrArg CommaMorphism.left h3

/-- The classifier sends the unit section of `A_P` to the trivial parameter. -/
lemma unitSection_comp_classifier :
    unitSection ((baseChange P.hom).obj A) ≫ (classifierOver A L M ev hL).left =
      P.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
        (unitSection_comp A) L hL).left := by
  have h := (comp_classifier_eq_iff A L M ev hL
    (1 : Over.mk (𝟙 P.left) ⟶ ((baseChange P.hom).obj A).X)).mpr
      ⟨mumfordZeroParameterIso _ pullbackTensorComparisonIsIso _ M ev _⟩
  rw [unitPoint_left] at h
  simpa using h

/-- Translation invariance at a single section is unchanged by isomorphism of modules. -/
lemma nonempty_pullback_iso_self_iff {X : Scheme.{u}} (τ : X ⟶ X) {F F' : X.Modules}
    (g : F ≅ F') :
    Nonempty ((Scheme.Modules.pullback τ).obj F ≅ F) ↔
      Nonempty ((Scheme.Modules.pullback τ).obj F' ≅ F') :=
  ⟨fun ⟨d⟩ ↦ ⟨(Scheme.Modules.pullback τ).mapIso g.symm ≪≫ d ≪≫ g⟩,
    fun ⟨d⟩ ↦ ⟨(Scheme.Modules.pullback τ).mapIso g ≪≫ d ≪≫ g.symm⟩⟩

/-- The pointwise criterion: a field-valued point of `A ×_S P` goes to the trivial parameter
exactly when the corresponding translate of the pulled-back universal bundle is isomorphic to
it. -/
lemma comp_classifier_eq_iff_translate {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ P.left)
    (y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left)
    (hy : y ≫ ((baseChange P.hom).obj A).X.hom = s)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange (s ≫ P.hom)).obj A).X)
    (hx : x.left ≫ pullback.fst A.X.hom (s ≫ P.hom) = y ≫ pullback.fst A.X.hom P.hom) :
    y ≫ (classifierOver A L M ev hL).left =
        s ≫ P.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
          (unitSection_comp A) L hL).left ↔
      Nonempty ((Scheme.Modules.pullback
          (GroupScheme.translation ((baseChange (s ≫ P.hom)).obj A).toGrp x).left).obj
            (familyLineBundle A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
              (unitSection_comp A) (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)).obj ≅
        (familyLineBundle A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)).obj) := by
  let A' := (baseChange P.hom).obj A
  let a' : Over.mk s ⟶ A'.X := Over.homMk y hy
  let x' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange s).obj A').X :=
    Over.homMk (pullback.lift y (𝟙 _) (by rw [Category.id_comp]; exact hy))
      (pullback.lift_snd _ _ _)
  have hx' : x'.left ≫ pullback.fst A'.X.hom s = a'.left := pullback.lift_fst _ _ _
  have h1 := comp_classifier_eq_iff A L M ev hL a'
  rw [nonempty_mumford_iso_trivial_iff A' (baseChangeBundle A L) M ev a' x' hx'] at h1
  let f := (GroupScheme.baseChangeCompIso P.hom s A.toGrp).symm
  let g := (LineBundle.forget _).mapIso (geometricPointPullbackLineBundleIso A P s L)
  have hsec : x' ≫ f.hom.hom.hom = x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (x'.left ≫ (GroupScheme.baseChangeCompIso P.hom s A.toGrp).inv.hom.hom.left) ≫
        pullback.fst A.X.hom (s ≫ P.hom) = x.left ≫ pullback.fst A.X.hom (s ≫ P.hom)
      have hx'' : x'.left ≫ pullback.fst (pullback.snd A.X.hom P.hom) s = y := hx'
      rw [Category.assoc, GroupScheme.baseChangeCompIso_inv_fst, hx, ← Category.assoc, hx'']
    · have e1 : (GroupScheme.baseChangeCompIso P.hom s A.toGrp).inv.hom.hom.left ≫
          pullback.snd A.X.hom (s ≫ P.hom) = pullback.snd A'.X.hom s :=
        Over.w (GroupScheme.baseChangeCompIso P.hom s A.toGrp).inv.hom.hom
      have e2 : x'.left ≫ pullback.snd A'.X.hom s = 𝟙 _ := pullback.lift_snd _ _ _
      have e3 : x.left ≫ pullback.snd A.X.hom (s ≫ P.hom) = 𝟙 _ := Over.w x
      change (x'.left ≫ (GroupScheme.baseChangeCompIso P.hom s A.toGrp).inv.hom.hom.left) ≫
        pullback.snd A.X.hom (s ≫ P.hom) = x.left ≫ pullback.snd A.X.hom (s ≫ P.hom)
      rw [Category.assoc, e1, e2, e3]
  refine h1.trans ((nonempty_pullback_iso_self_iff _ g.symm).trans
    ((nonempty_translate_pullback_iso_iff f x' _).trans ?_))
  rw [hsec]
  exact Iff.rfl

/-- Translation invariance of the pulled-back universal bundle at a field-valued point of `P`
is equivalent to the classifier sending every point of `A ×_S P` over it to the trivial
parameter. -/
lemma isTranslationInvariant_iff_classifier {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ P.left) :
    GroupScheme.IsTranslationInvariant ((baseChange (s ≫ P.hom)).obj A).toGrp
        (familyLineBundle A (T := Over.mk (s ≫ P.hom))
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)) ↔
      ∀ y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left,
        y ≫ ((baseChange P.hom).obj A).X.hom = s →
          y ≫ (classifierOver A L M ev hL).left =
            s ≫ P.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
              (unitSection_comp A) L hL).left := by
  constructor
  · intro hTI y hy
    let x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange (s ≫ P.hom)).obj A).X :=
      Over.homMk (pullback.lift (y ≫ pullback.fst A.X.hom P.hom) (𝟙 _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, Category.id_comp]
        exact congrArg (· ≫ P.hom) hy)) (pullback.lift_snd _ _ _)
    obtain ⟨d⟩ := hTI x
    exact (comp_classifier_eq_iff_translate A L M ev hL s y hy x
      (pullback.lift_fst _ _ _)).mpr ⟨(LineBundle.forget _).mapIso d⟩
  · intro H x
    let y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left :=
      pullback.lift (x.left ≫ pullback.fst A.X.hom (s ≫ P.hom)) s (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        have w : x.left ≫ pullback.snd A.X.hom (s ≫ P.hom) = 𝟙 _ := Over.w x
        rw [w]
        exact Category.id_comp _)
    obtain ⟨d⟩ := (comp_classifier_eq_iff_translate A L M ev hL s y (pullback.lift_snd _ _ _) x
      (pullback.lift_fst _ _ _).symm).mp (H y (pullback.lift_snd _ _ _))
    exact ⟨ObjectProperty.isoMk _ d⟩

/-- Version of `isTranslationInvariant_iff_classifier` for a structure morphism `c` equal to
`s ≫ P.hom`. -/
lemma isTranslationInvariant_iff_classifier_of_eq {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ P.left) (c : Spec (CommRingCat.of K) ⟶ S)
    (h : s ≫ P.hom = c) :
    GroupScheme.IsTranslationInvariant ((baseChange c).obj A).toGrp
        (familyLineBundle A (T := Over.mk c) ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) (Over.homMk s h : Over.mk c ⟶ P)).obj L)) ↔
      ∀ y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left,
        y ≫ ((baseChange P.hom).obj A).X.hom = s →
          y ≫ (classifierOver A L M ev hL).left =
            c ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
              (unitSection_comp A) L hL).left := by
  subst h
  simpa only [Category.assoc] using isTranslationInvariant_iff_classifier A L M ev hL s

/-- The same equivalence for a field-valued point of `P` presented over an arbitrary structure
morphism. -/
lemma isTranslationInvariant_iff_classifier' {K : Type u} [Field K]
    (c : Spec (CommRingCat.of K) ⟶ S) (q : Over.mk c ⟶ P) :
    GroupScheme.IsTranslationInvariant ((baseChange c).obj A).toGrp
        (familyLineBundle A (T := Over.mk c) ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) q).obj L)) ↔
      ∀ y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left,
        y ≫ ((baseChange P.hom).obj A).X.hom = q.left →
          y ≫ (classifierOver A L M ev hL).left =
            c ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
              (unitSection_comp A) L hL).left :=
  isTranslationInvariant_iff_classifier_of_eq A L M ev hL q.left c (Over.w q)

/-- The classifier is a morphism over `S`. -/
lemma classifier_comp_hom :
    (classifierOver A L M ev hL).left ≫ P.hom = ((baseChange P.hom).obj A).X.hom ≫ P.hom :=
  Over.w (classifierOver A L M ev hL)

/-- If the pullback along `p` is geometric Picard zero, the classifier sends every geometric
point of `A ×_S P` over a geometric point of `T` to the trivial parameter. -/
lemma classifier_forward (T : Over S) (p : T ⟶ P)
    (hp : IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) p).obj L))
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T.left)
    (y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left)
    (hy : y ≫ ((baseChange P.hom).obj A).X.hom = t ≫ p.left) :
    y ≫ (classifierOver A L M ev hL).left =
      t ≫ T.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
        (unitSection_comp A) L hL).left := by
  have h0 : IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T)).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) p).obj L)) :=
    picardZeroPullback S A (Over.mk (t ≫ T.hom)) T (Over.homMk t rfl)
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) p).obj L) hp
  have hq : IsPicardZeroFamily A (T := Over.mk (t ≫ T.hom))
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        ((Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) ≫ p)).obj L) :=
    (isPicardZeroFamily_iff_of_iso A ((RigidifiedLineBundle.relativePullbackComp
      RigidifiedModule.pullbackCoherence A.X.hom (unitSection A) (unitSection_comp A)
        (Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) p).app L)).mp h0
  have hTI := isTranslationInvariant_of_isGeometricallyPicardZero K
    ((baseChange (t ≫ T.hom)).obj A) hq
  have := (isTranslationInvariant_iff_classifier' A L M ev hL (t ≫ T.hom)
    ((Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) ≫ p)).mp hTI y hy
  simpa only [Category.assoc] using this

/-- Conversely, if the classifier sends all such geometric points to the trivial parameter, the
pullback along `p` is geometric Picard zero. -/
lemma classifier_backward (T : Over S) (p : T ⟶ P)
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T.left)
      (y : Spec (CommRingCat.of K) ⟶ ((baseChange P.hom).obj A).X.left),
      y ≫ ((baseChange P.hom).obj A).X.hom = t ≫ p.left →
        y ≫ (classifierOver A L M ev hL).left =
          t ≫ T.hom ≫ (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
            (unitSection_comp A) L hL).left) :
    IsPicardZeroFamily A ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) p).obj L) := by
  intro K _ _ t
  have hq : GroupScheme.IsTranslationInvariant ((baseChange (t ≫ T.hom)).obj A).toGrp
      (familyLineBundle A (T := Over.mk (t ≫ T.hom))
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) ≫ p)).obj L)) :=
    (isTranslationInvariant_iff_classifier' A L M ev hL (t ≫ T.hom)
      ((Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) ≫ p)).mpr
        (fun y hy ↦ by simpa only [Category.assoc] using H K t y hy)
  have hTI : GroupScheme.IsTranslationInvariant ((baseChange (t ≫ T.hom)).obj A).toGrp
      (familyLineBundle A (T := Over.mk (t ≫ T.hom))
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T)).obj
            ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
              (unitSection_comp A) p).obj L))) :=
    GroupScheme.isTranslationInvariant_of_iso _
      ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom (Over.mk (t ≫ T.hom))).inv).mapIso
        ((RigidifiedLineBundle.forget _).mapIso
          ((RigidifiedLineBundle.relativePullbackComp RigidifiedModule.pullbackCoherence
            A.X.hom (unitSection A) (unitSection_comp A)
              (Over.homMk t rfl : Over.mk (t ≫ T.hom) ⟶ T) p).app L).symm)) hq
  exact GroupScheme.isTranslationInvariant_of_iso _
    (geometricPointPullbackLineBundleIso A T t _)
    (GroupScheme.isTranslationInvariant_pullback
      (GroupScheme.baseChangeCompIso T.hom t A.toGrp).inv hTI)

end Langlands.AbelianScheme.UniversalMumfordClassifier

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
  UniversalMumfordClassifier

/-- The classifying morphism of the Mumford family of the base change `A ×_S P` of a universal
rigidified family is a morphism `Ψ : A ×_S P ⟶ P` over `S` that sends the unit section to the
trivial parameter and detects the geometric Picard-zero condition of every pullback of `L`. -/
theorem universalMumfordClassifier : UniversalMumfordClassifierStatement.{u} := by
  intro S A P L hL
  obtain ⟨N, ⟨e⟩⟩ := (locallyFreeRankOneIffTensorInvertible _
    (baseChangeBundle A L).obj.carrier).mpr (baseChangeBundle A L).property
  have hN : IsLocallyFreeRankOne N :=
    (locallyFreeRankOneIffTensorInvertible _ N).mp
      ⟨(baseChangeBundle A L).obj.carrier, ⟨(β_ N _) ≪≫ e⟩⟩
  let M : LineBundle ((baseChange P.hom).obj A).X.left := ⟨N, hN⟩
  let ev : tensorObj (baseChangeBundle A L).obj.carrier M.obj ≅
      structureSheaf ((baseChange P.hom).obj A).X.left :=
    (localizedTensorIso _ _ N).symm ≪≫ e
  exact ⟨(classifierOver A L M ev hL).left, classifier_comp_hom A L M ev hL,
    unitSection_comp_classifier A L M ev hL,
    fun T p ↦ ⟨classifier_forward A L M ev hL T p, classifier_backward A L M ev hL T p⟩⟩

end Langlands.AbelianScheme
