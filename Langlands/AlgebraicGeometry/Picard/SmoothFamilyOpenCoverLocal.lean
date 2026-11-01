import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedReductionProof

/-! # Universality of smooth families on tests over an open of the base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.SmoothFamilyOpenCover

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedReduction

set_option quotPrecheck false in
/-- Actual rigidified pullback of classes for the abelian scheme `A`. -/
scoped notation "cp[" A "]" =>
  RigidifiedLineBundle.classesPullback (A).X.hom (unitSection A) (unitSection_comp A)

set_option quotPrecheck false in
/-- The classifying map of an actual rigidified family for `A`. -/
scoped notation "cm[" A "]" =>
  RigidifiedLineBundle.classifyingMap (A).X.hom (unitSection A) (unitSection_comp A)

set_option quotPrecheck false in
/-- The class of an actual rigidified family for `A`. -/
scoped notation "cl[" A "]" =>
  RigidifiedLineBundle.classOf (A).X.hom (unitSection A) (unitSection_comp A)

set_option quotPrecheck false in
/-- Actual rigidified pullback of families for `A`. -/
scoped notation "rp[" A "]" =>
  RigidifiedLineBundle.relativePullback (A).X.hom (unitSection A) (unitSection_comp A)

variable {S : Scheme.{u}} (A : AbelianScheme S)

section Classes

lemma cp_id {T : Over S} (q : RigidifiedClasses A T) : cp[A] (𝟙 T) q = q := by
  refine Quotient.inductionOn q (fun F ↦ ?_)
  exact Quotient.sound ⟨(RigidifiedLineBundle.relativePullbackId
    RigidifiedModule.pullbackCoherence A.X.hom (unitSection A)
      (unitSection_comp A) T).app F⟩

lemma cm_comp {P T U : Over S} (L : RigidifiedFamily A P) (h : T ⟶ U) (k : U ⟶ P) :
    cm[A] L T (h ≫ k) = cp[A] h (cm[A] L U k) :=
  RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence L h k

lemma cm_id {P : Over S} (L : RigidifiedFamily A P) : cm[A] L P (𝟙 P) = cl[A] L :=
  RigidifiedLineBundle.classifyingMap_id _ _ _ RigidifiedModule.pullbackCoherence L

lemma cl_pullback {T U : Over S} (h : T ⟶ U) (L : RigidifiedFamily A U) :
    cl[A] ((rp[A] h).obj L) = cp[A] h (cl[A] L) := rfl

lemma cm_pullback {P P' T : Over S} (k : P' ⟶ P) (L : RigidifiedFamily A P) (h : T ⟶ P') :
    cm[A] ((rp[A] k).obj L) T h = cm[A] L T (h ≫ k) := by
  change cp[A] h (cp[A] k (cl[A] L)) = _
  rw [classesPullback_comp]; rfl

lemma cl_eq_of_iso {T : Over S} {L M : RigidifiedFamily A T} (e : L ≅ M) :
    cl[A] L = cl[A] M := Quotient.sound ⟨e⟩

/-- The smooth-family condition on classes is stable under actual pullback. -/
lemma isAlgTrivClass_pullback {T U : Over S} (h : T ⟶ U) {q : RigidifiedClasses A U}
    (hq : IsAlgebraicallyTrivialClassViaSmoothFamily A q) :
    IsAlgebraicallyTrivialClassViaSmoothFamily A (cp[A] h q) := by
  revert hq
  refine Quotient.inductionOn q (fun F hF ↦ ?_)
  exact smoothFamilyPullback S A T U h F hF

/-- Pullback of classes satisfying the smooth-family condition. -/
def atPullback {T U : Over S} (h : T ⟶ U) (q : AlgebraicallyTrivialClassesViaSmoothFamily A U) :
    AlgebraicallyTrivialClassesViaSmoothFamily A T :=
  ⟨cp[A] h q.1, isAlgTrivClass_pullback A h q.2⟩

@[simp] lemma atPullback_val {T U : Over S} (h : T ⟶ U)
    (q : AlgebraicallyTrivialClassesViaSmoothFamily A U) :
    (atPullback A h q).val = cp[A] h q.val := rfl

/-- The class of an actual family satisfying the smooth-family condition. -/
def atClass {T : Over S} (L : RigidifiedFamily A T)
    (hL : IsAlgebraicallyTrivialFamilyViaSmoothFamily A L) :
    AlgebraicallyTrivialClassesViaSmoothFamily A T :=
  ⟨cl[A] L, hL⟩

@[simp] lemma atClass_val {T : Over S} (L : RigidifiedFamily A T)
    (hL : IsAlgebraicallyTrivialFamilyViaSmoothFamily A L) :
    (atClass A L hL).val = cl[A] L := rfl

end Classes

section Universal

/-- Unique classification on the quasi-separated tests whose structure map lands in `V`. -/
def IsUniversalOn (V : S.Opens) {P : Over S} (L : RigidifiedFamily A P) : Prop :=
  ∀ (T : Over S) [QuasiSeparatedSpace T.left], Set.range T.hom ⊆ (V : Set S) →
    ∀ q : AlgebraicallyTrivialClassesViaSmoothFamily A T,
      ∃! h : T ⟶ P, cm[A] L T h = q.val

/-- Unique classification transports along an isomorphism of tests. -/
lemma existsUnique_of_iso {P T T' : Over S} (L : RigidifiedFamily A P) (e : T ≅ T')
    (H : ∀ q : AlgebraicallyTrivialClassesViaSmoothFamily A T',
      ∃! h : T' ⟶ P, cm[A] L T' h = q.val)
    (q : AlgebraicallyTrivialClassesViaSmoothFamily A T) :
    ∃! h : T ⟶ P, cm[A] L T h = q.val := by
  obtain ⟨h', hh', hu⟩ := H (atPullback A e.inv q)
  refine ⟨e.hom ≫ h', ?_, ?_⟩
  · show cm[A] L T (e.hom ≫ h') = q.val
    rw [cm_comp, hh', atPullback_val, classesPullback_comp, e.hom_inv_id, cp_id]
  · intro k hk
    have : e.inv ≫ k = h' := hu _ (by
      show cm[A] L T' (e.inv ≫ k) = _
      rw [cm_comp, hk]; rfl)
    rw [← this, e.hom_inv_id_assoc]

/-- Two maps into a family universal over `V` agree once they classify the same class. -/
lemma eq_of_cm_eq {V : S.Opens} {P : Over S} {L : RigidifiedFamily A P}
    (hL : IsUniversalOn A V L) {T : Over S} [QuasiSeparatedSpace T.left]
    (hT : Set.range T.hom ⊆ (V : Set S)) {h k : T ⟶ P}
    (hq : IsAlgebraicallyTrivialClassViaSmoothFamily A (cm[A] L T h))
    (hhk : cm[A] L T h = cm[A] L T k) : h = k :=
  (hL T hT ⟨_, hq⟩).unique rfl hhk.symm

/-- Universality on `W` restricts to universality on a smaller open `V` along
an actual preimage square of `V`. -/
lemma isUniversalOn_of_isPullback {V W : S.Opens} (hVW : V ≤ W) {X Y : Over S}
    {N : RigidifiedFamily A X} (hN : IsUniversalOn A W N) (f : Y ⟶ X) (g : Y.left ⟶ V)
    (hg : g ≫ V.ι = Y.hom) (hpb : IsPullback f.left g X.hom V.ι) :
    IsUniversalOn A V ((rp[A] f).obj N) := by
  intro T _ hT q
  obtain ⟨h, hh, hu⟩ := hN T (hT.trans hVW) q
  have hTV : Set.range T.hom ⊆ Set.range V.ι := by simpa using hT
  let l : T.left ⟶ V := IsOpenImmersion.lift V.ι T.hom hTV
  have hl : h.left ≫ X.hom = l ≫ V.ι := by simp [l]
  let k : T ⟶ Y := Over.homMk (hpb.lift h.left l hl)
    (by rw [← hg, hpb.lift_snd_assoc]; simp [l])
  have hk : k ≫ f = h := by ext; exact hpb.lift_fst _ _ _
  refine ⟨k, ?_, ?_⟩
  · show cm[A] ((rp[A] f).obj N) T k = q.val
    rw [cm_pullback, hk, hh]
  · intro k' hk'
    rw [cm_pullback] at hk'
    have h1 : k' ≫ f = h := hu _ hk'
    ext
    apply hpb.hom_ext
    · change k'.left ≫ f.left = hpb.lift h.left l hl ≫ f.left
      rw [hpb.lift_fst, ← h1]; rfl
    · change k'.left ≫ g = hpb.lift h.left l hl ≫ g
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hpb.lift_snd_assoc,
        IsOpenImmersion.lift_fac, hg]
      exact Over.w k'

/-- Two universal families over `V` on quasi-separated parameters over `V`
have isomorphic parameters, through any map classifying one by the other. -/
lemma isIso_of_isUniversalOn {V : S.Opens} {X Y : Over S} {N : RigidifiedFamily A X}
    {N' : RigidifiedFamily A Y} (hN : IsUniversalOn A V N) (hN' : IsUniversalOn A V N')
    (hNa : IsAlgebraicallyTrivialFamilyViaSmoothFamily A N)
    (hN'a : IsAlgebraicallyTrivialFamilyViaSmoothFamily A N')
    [QuasiSeparatedSpace X.left] [QuasiSeparatedSpace Y.left]
    (hX : Set.range X.hom ⊆ (V : Set S)) (hY : Set.range Y.hom ⊆ (V : Set S))
    (f : Y ⟶ X) (hf : cm[A] N Y f = cl[A] N') : IsIso f := by
  obtain ⟨g, hg, -⟩ := hN' X hX (atClass A N hNa)
  refine ⟨g, ?_, ?_⟩
  · refine (hN' Y hY (atClass A N' hN'a)).unique ?_ ?_
    · show cm[A] N' Y (f ≫ g) = cl[A] N'
      rw [cm_comp, hg, atClass_val, ← cm_id, ← hf, ← cm_comp, Category.comp_id]
    · exact cm_id A N'
  · refine (hN X hX (atClass A N hNa)).unique ?_ ?_
    · show cm[A] N X (g ≫ f) = cl[A] N
      rw [cm_comp, hf, ← cm_id A N', ← cm_comp, Category.comp_id, hg]; rfl
    · exact cm_id A N

end Universal

section BaseChange

variable {U : Scheme.{u}} (b : U ⟶ S) [IsOpenImmersion b]

/-- Lift a slice map over `S` between objects over the open `U`. -/
def overMapPreimage {T P : Over U} (k : (Over.map b).obj T ⟶ (Over.map b).obj P) :
    T ⟶ P :=
  Over.homMk k.left (by rw [← cancel_mono b]; simpa using Over.w k)

lemma overMap_map_overMapPreimage {T P : Over U}
    (k : (Over.map b).obj T ⟶ (Over.map b).obj P) :
    (Over.map b).map (overMapPreimage b k) = k := by
  ext; rfl

omit [IsOpenImmersion b] in
/-- Ground-base change of classifying maps of the inverse base-change family. -/
lemma classesBaseChange_classifyingMap {T P : Over U}
    (L : RigidifiedFamily ((baseChange b).obj A) P) (g : T ⟶ P) :
    classesBaseChange b A T (cm[A] ((familyBaseChangeInverse b A P).obj L)
        ((Over.map b).obj T) ((Over.map b).map g)) =
      cm[(baseChange b).obj A] L T g := by
  change classesBaseChange b A T (cp[A] ((Over.map b).map g) (cl[A] _)) =
    cp[(baseChange b).obj A] g (cl[(baseChange b).obj A] L)
  rw [classesBaseChange_pullback]
  congr 1
  exact Quotient.sound ⟨(familyBaseChangeCounitIso b A P).app L⟩

omit [IsOpenImmersion b] in
/-- The inverse ground-base change of a smooth-family family satisfies the
smooth-family condition. -/
lemma isAlgebraicallyTrivial_familyBaseChangeInverse {T : Over U}
    (L : RigidifiedFamily ((baseChange b).obj A) T)
    (hL : IsAlgebraicallyTrivialFamilyViaSmoothFamily ((baseChange b).obj A) L) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A ((familyBaseChangeInverse b A T).obj L) :=
  (isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff b A T _).mpr
    ((isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_iso _
      ((familyBaseChangeCounitIso b A T).app L)).mpr hL)

/-- A universal family for the restriction of `A` to the open `U` gives a family
for `A` which is universal on tests landing in `U`. -/
theorem isUniversalOn_familyBaseChangeInverse {P : Over U}
    (L : RigidifiedFamily ((baseChange b).obj A) P)
    (hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests ((baseChange b).obj A) L) :
    IsUniversalOn A b.opensRange ((familyBaseChangeInverse b A P).obj L) := by
  intro T _ hT q
  have hTb : Set.range T.hom ⊆ Set.range b := by simpa using hT
  let T' : Over U := Over.mk (IsOpenImmersion.lift b T.hom hTb)
  let e : T ≅ (Over.map b).obj T' := Over.isoMk (Iso.refl _) (by simp [T'])
  refine existsUnique_of_iso A _ e (fun q ↦ ?_) q
  have : QuasiSeparatedSpace T'.left := ‹QuasiSeparatedSpace T.left›
  have hx : ∀ y : RigidifiedClasses A ((Over.map b).obj T'),
      IsAlgebraicallyTrivialClassViaSmoothFamily A y →
        IsAlgebraicallyTrivialClassViaSmoothFamily ((baseChange b).obj A)
          (classesBaseChange b A T' y) := by
    intro y
    refine Quotient.inductionOn y (fun Q hQ ↦ ?_)
    exact (isAlgebraicallyTrivialFamilyViaSmoothFamily_familyBaseChange_iff b A T' Q).mp hQ
  obtain ⟨g, hg, hgu⟩ := hL.2 T' ⟨_, hx q.1 q.2⟩
  refine ⟨(Over.map b).map g, ?_, ?_⟩
  · apply classesBaseChange_injective b A T'
    rw [classesBaseChange_classifyingMap]
    exact hg
  · intro k hk
    rw [← overMap_map_overMapPreimage b k]
    congr 1
    apply hgu
    rw [← classesBaseChange_classifyingMap, overMap_map_overMapPreimage, hk]

end BaseChange

section Fibre

variable {T U : Over S} (h : T ⟶ U) {K : Type u} [Field K] [IsAlgClosed K]
  (s : Spec (CommRingCat.of K) ⟶ T.left)

omit [IsAlgClosed K] in
/-- The canonical comparison of iterated geometric fibres is an isomorphism of schemes. -/
lemma isIso_fibreComparison_left :
    IsIso (GroupScheme.fibreComparison A.toGrp h s).hom.hom.left := by
  have hT : IsPullback
      (pullback.fst (pullback.snd A.X.hom T.hom) s ≫ pullback.fst A.X.hom T.hom)
      (pullback.snd (pullback.snd A.X.hom T.hom) s) A.X.hom (s ≫ T.hom) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hU : IsPullback
      (pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left) ≫ pullback.fst A.X.hom U.hom)
      (pullback.snd (pullback.snd A.X.hom U.hom) (s ≫ h.left)) A.X.hom (s ≫ T.hom) := by
    have e : (s ≫ h.left) ≫ U.hom = s ≫ T.hom := by rw [Category.assoc, Over.w h]
    have H := (IsPullback.of_hasPullback (pullback.snd A.X.hom U.hom) (s ≫ h.left)).paste_horiz
      (IsPullback.of_hasPullback A.X.hom U.hom)
    rw [e] at H
    exact H
  have e : (GroupScheme.fibreComparison A.toGrp h s).hom.hom.left =
      (hT.isoIsPullback _ _ hU).hom := by
    apply hU.hom_ext
    · rw [IsPullback.isoIsPullback_hom_fst]
      exact GroupScheme.fibreComparison_fst A.toGrp h s
    · rw [IsPullback.isoIsPullback_hom_snd]
      exact GroupScheme.fibreComparison_snd A.toGrp h s
  rw [e]
  infer_instance

/-- The smooth-family condition on a geometric fibre of an actual pullback family
gives the condition on the corresponding geometric fibre of the original family. -/
lemma isAlgebraicallyTrivial_fibre_of_relativePullback (L : RigidifiedFamily A U)
    (hL : IsAlgebraicallyTrivialViaSmoothFamily ((baseChange s).obj ((baseChange T.hom).obj A))
      (fibreLineBundle ((baseChange T.hom).obj A) (familyLineBundle A ((rp[A] h).obj L)) s)) :
    IsAlgebraicallyTrivialViaSmoothFamily
      ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A))
      (fibreLineBundle ((baseChange U.hom).obj A) (familyLineBundle A L) (s ≫ h.left)) := by
  let m := GroupScheme.fibreComparison A.toGrp h s
  have h1 : IsIso ((Over.forget _).map m.hom.hom) := isIso_fibreComparison_left A h s
  have h2 : IsIso m.hom.hom := isIso_of_reflects_iso m.hom.hom (Over.forget _)
  have hp := isAlgebraicallyTrivialViaSmoothFamily_pullback_hom
    ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A))
    ((baseChange s).obj ((baseChange T.hom).obj A)) (inv m.hom.hom) hL
  have e : (inv m.hom.hom).left ≫ m.hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, IsIso.inv_hom_id]
    rfl
  refine isAlgebraicallyTrivialViaSmoothFamily_of_iso _ ?_ hp
  exact (LineBundle.pullback (inv m.hom.hom).left).mapIso
      (fibreComparison_lineBundleIso A h s m
        (GroupScheme.fibreComparison_fst A.toGrp h s) L).symm ≪≫
    (LineBundle.pullbackComp _ _).app _ ≪≫
    eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj _) e) ≪≫
    (LineBundle.pullbackId _).app _

omit h s in
/-- The smooth-family condition is local on an open cover of the parameter. -/
lemma isAlgebraicallyTrivialFamily_of_openCover (L : RigidifiedFamily A U)
    (𝒱 : U.left.OpenCover)
    (H : ∀ i, IsAlgebraicallyTrivialFamilyViaSmoothFamily A
      ((rp[A] (Over.homMk (𝒱.f i) : Over.mk (𝒱.f i ≫ U.hom) ⟶ U)).obj L)) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A L := by
  intro K _ _ s
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let x₀ : Spec (CommRingCat.of K) := (default : PrimeSpectrum K)
  obtain ⟨i, y, hy⟩ := 𝒱.exists_eq (s x₀)
  have hr : Set.range s ⊆ Set.range (𝒱.f i) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x₀]
    exact ⟨y, hy⟩
  have e : IsOpenImmersion.lift (𝒱.f i) s hr ≫
      (Over.homMk (𝒱.f i) : Over.mk (𝒱.f i ≫ U.hom) ⟶ U).left = s :=
    IsOpenImmersion.lift_fac _ _ _
  have := isAlgebraicallyTrivial_fibre_of_relativePullback A
    (Over.homMk (𝒱.f i) : Over.mk (𝒱.f i ≫ U.hom) ⟶ U) (IsOpenImmersion.lift (𝒱.f i) s hr) L
    (H i K _)
  rw [e] at this
  exact this

end Fibre

end Langlands.AbelianScheme.SmoothFamilyOpenCover
