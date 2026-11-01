import Langlands.AlgebraicGeometry.Picard.SmoothFamilyOpenCoverLocal
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Gluing the parameters of local universal smooth families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.SmoothFamilyOpenCover

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A : AbelianScheme S}

section Cover

variable {ι : Type u} (W : ι → S.Opens)

/-- The opens of `S` contained in some member of `W`. -/
def SubOpens : Set S.Opens := {V | ∃ i, V ≤ W i}

variable {W}

lemma isBasis_subOpens (hW : TopologicalSpace.IsOpenCover W) :
    TopologicalSpace.Opens.IsBasis (SubOpens W) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, hi⟩ := hW.exists_mem x
  exact ⟨U ⊓ W i, ⟨i, inf_le_right⟩, ⟨hx, hi⟩, inf_le_left⟩

variable (W) in
/-- The open cover of `S` by all opens contained in some member of `W`. -/
def basisCover (hW : TopologicalSpace.IsOpenCover W) : S.OpenCover.{u} :=
  S.openCoverOfIsOpenCover (fun V : SubOpens W ↦ V.1) (isBasis_subOpens hW).isOpenCover

variable (hW : TopologicalSpace.IsOpenCover W)

instance : Preorder (basisCover W hW).I₀ := inferInstanceAs (Preorder (SubOpens W))

instance : (basisCover W hW).LocallyDirected :=
  .ofIsBasisOpensRange (fun {V V'} ↦ by
      change V.1 ≤ V'.1 ↔ _
      simp [basisCover]) (by
    have : Set.range (fun V : (basisCover W hW).I₀ ↦ ((basisCover W hW).f V).opensRange) =
        SubOpens W := by
      ext U
      simp only [basisCover, Scheme.openCoverOfIsOpenCover_f, Scheme.Opens.opensRange_ι,
        Set.mem_range]
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun h ↦ ⟨⟨U, h⟩, rfl⟩⟩
    rw [this]
    exact isBasis_subOpens hW)

lemma basisCover_trans_ι {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    (basisCover W hW).trans f ≫ V'.1.ι = V.1.ι :=
  (basisCover W hW).trans_map f

lemma range_comp_ι_subset {X : Scheme.{u}} (V : S.Opens) (g : X ⟶ V.toScheme) :
    Set.range (g ≫ V.ι) ⊆ (V : Set S) := by
  rw [← Scheme.Opens.range_ι V]
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, (Scheme.Hom.comp_apply _ _ x).symm⟩

variable (T : Over S)

/-- The cover of a test by the preimages of the basis opens. -/
abbrev testCover : T.left.OpenCover.{u} := (basisCover W hW).pullback₁ T.hom

/-- A member of the test cover, as a test over `S`. -/
abbrev test (V : (basisCover W hW).I₀) : Over S := Over.mk ((testCover hW T).f V ≫ T.hom)

/-- The inclusion of a member of the test cover. -/
abbrev testIncl (V : (basisCover W hW).I₀) : test hW T V ⟶ T :=
  Over.homMk ((testCover hW T).f V)

lemma test_hom (V : (basisCover W hW).I₀) :
    (test hW T V).hom = pullback.snd T.hom V.1.ι ≫ V.1.ι :=
  pullback.condition

lemma range_test (V : (basisCover W hW).I₀) :
    Set.range (test hW T V).hom ⊆ (V.1 : Set S) := by
  rw [test_hom]
  exact range_comp_ι_subset _ _

instance [QuasiSeparatedSpace T.left] (V : (basisCover W hW).I₀) :
    QuasiSeparatedSpace (test hW T V).left :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst T.hom V.1.ι) _ inferInstance

/-- The transition between members of the test cover, over `S`. -/
def testTrans {V V' : (basisCover W hW).I₀} (f : V ⟶ V') : test hW T V ⟶ test hW T V' :=
  Over.homMk ((testCover hW T).trans f) (by
    change (testCover hW T).trans f ≫ (testCover hW T).f V' ≫ T.hom = _
    rw [← Category.assoc, Scheme.Cover.trans_map]
    rfl)

lemma testTrans_testIncl {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    testTrans hW T f ≫ testIncl hW T V' = testIncl hW T V := by
  ext
  change (testCover hW T).trans f ≫ (testCover hW T).f V' = _
  exact (testCover hW T).trans_map f

end Cover

section LocalData

variable {ι : Type u} (A) (W : ι → S.Opens)

/-- Local families for `A`, each universal on the tests landing in a member of `W`. -/
structure LocalData where
  /-- The local parameters. -/
  P : ι → Over S
  /-- The local families. -/
  M : ∀ i, RigidifiedFamily A (P i)
  quasiSeparated : ∀ i, QuasiSeparated (P i).hom
  universal : ∀ i, IsUniversalOn A (W i) (M i)
  algTriv : ∀ i, IsAlgebraicallyTrivialFamilyViaSmoothFamily A (M i)

variable {A W}

/-- A member of `W` containing `V`. -/
def idx (V : SubOpens W) : ι := V.2.choose

lemma le_idx (V : SubOpens W) : V.1 ≤ W (idx V) := V.2.choose_spec

namespace LocalData

variable (D : LocalData A W)

/-- The preimage of `V` in the chosen local parameter. -/
def param (V : SubOpens W) : Over S :=
  Over.mk (pullback.snd (D.P (idx V)).hom V.1.ι ≫ V.1.ι)

/-- The projection of the preimage of `V` to the chosen local parameter. -/
def paramFst (V : SubOpens W) : D.param V ⟶ D.P (idx V) :=
  Over.homMk (pullback.fst _ _) pullback.condition

/-- The restriction of the chosen local family to the preimage of `V`. -/
def family (V : SubOpens W) : RigidifiedFamily A (D.param V) :=
  (rp[A] (D.paramFst V)).obj (D.M (idx V))

lemma family_universal (V : SubOpens W) : IsUniversalOn A V.1 (D.family V) :=
  isUniversalOn_of_isPullback A (le_idx V) (D.universal _) (D.paramFst V) (pullback.snd _ _)
    rfl (IsPullback.of_hasPullback _ _)

lemma family_algTriv (V : SubOpens W) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A (D.family V) :=
  smoothFamilyPullback S A _ _ (D.paramFst V) _ (D.algTriv _)

instance (V : SubOpens W) : QuasiSeparated (D.param V).hom := by
  have := D.quasiSeparated (idx V)
  dsimp [param]
  infer_instance

instance [QuasiSeparatedSpace S] (V : SubOpens W) : QuasiSeparatedSpace (D.param V).left :=
  quasiSeparatedSpace_of_quasiSeparated (D.param V).hom

lemma range_param (V : SubOpens W) : Set.range (D.param V).hom ⊆ (V.1 : Set S) :=
  range_comp_ι_subset V.1 _

variable [QuasiSeparatedSpace S]

lemma existsUnique_transition {V V' : SubOpens W} (h : V.1 ≤ V'.1) :
    ∃! t : D.param V ⟶ D.param V', cm[A] (D.family V') (D.param V) t = cl[A] (D.family V) :=
  D.family_universal V' (D.param V) ((D.range_param V).trans h)
    (atClass A _ (D.family_algTriv V))

/-- The transition between the parameters of `V ≤ V'`, classifying the family of `V`. -/
def transition {V V' : SubOpens W} (h : V.1 ≤ V'.1) : D.param V ⟶ D.param V' :=
  (D.existsUnique_transition h).exists.choose

lemma transition_spec {V V' : SubOpens W} (h : V.1 ≤ V'.1) :
    cm[A] (D.family V') (D.param V) (D.transition h) = cl[A] (D.family V) :=
  (D.existsUnique_transition h).exists.choose_spec

lemma transition_unique {V V' : SubOpens W} (h : V.1 ≤ V'.1) (t : D.param V ⟶ D.param V')
    (ht : cm[A] (D.family V') (D.param V) t = cl[A] (D.family V)) : t = D.transition h :=
  (D.existsUnique_transition h).unique ht (D.transition_spec h)

lemma transition_id (V : SubOpens W) (h : V.1 ≤ V.1) : D.transition h = 𝟙 _ :=
  (D.transition_unique h _ (cm_id A _)).symm

lemma transition_comp {V V' V'' : SubOpens W} (h : V.1 ≤ V'.1) (h' : V'.1 ≤ V''.1)
    (h'' : V.1 ≤ V''.1) : D.transition h'' = D.transition h ≫ D.transition h' := by
  refine (D.transition_unique h'' _ ?_).symm
  rw [cm_comp, D.transition_spec, ← cm_id A (D.family V'), ← cm_comp, Category.comp_id,
    D.transition_spec]

/-- Pulling the family of `V` back along a transition gives the family of the smaller open. -/
lemma cp_transition {V V' : SubOpens W} (h : V.1 ≤ V'.1) {Y : Over S}
    (m : Y ⟶ D.param V) :
    cp[A] (m ≫ D.transition h) (cl[A] (D.family V')) = cp[A] m (cl[A] (D.family V)) := by
  rw [← classesPullback_comp]
  exact congrArg (cp[A] m) (D.transition_spec h)

variable (hW : TopologicalSpace.IsOpenCover W)

/-- The diagram of local parameters over the basis cover. -/
def functor : (basisCover W hW).I₀ ⥤ Scheme.{u} where
  obj V := (D.param V).left
  map f := (D.transition (leOfHom f)).left
  map_id V := by rw [D.transition_id]; rfl
  map_comp f g := by rw [D.transition_comp (leOfHom f) (leOfHom g)]; rfl

lemma functor_map {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    (D.functor hW).map f = (D.transition (leOfHom f)).left := rfl

/-- The structure maps of the local parameters to the members of the basis cover. -/
def natTrans : D.functor hW ⟶ (basisCover W hW).functorOfLocallyDirected where
  app V := pullback.snd (D.P (idx V)).hom V.1.ι
  naturality {V V'} f := by
    change (D.transition (leOfHom f)).left ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (basisCover W hW).trans f
    rw [← cancel_mono V'.1.ι, Category.assoc, Category.assoc, basisCover_trans_ι hW]
    exact Over.w (D.transition (leOfHom f))

lemma natTrans_app (V : (basisCover W hW).I₀) :
    (D.natTrans hW).app V = pullback.snd (D.P (idx V)).hom V.1.ι := rfl

lemma equifibered : (D.natTrans hW).Equifibered := by
  intro V V' f
  let a' := pullback.snd (D.P (idx V')).hom V'.1.ι
  let τ := (basisCover W hW).trans f
  have hτ : τ ≫ V'.1.ι = V.1.ι := basisCover_trans_ι hW f
  have := D.quasiSeparated (idx V')
  let Y : Over S := Over.mk (pullback.snd a' τ ≫ V.1.ι)
  let k : Y ⟶ D.param V' := Over.homMk (pullback.fst a' τ) (by
    change pullback.fst a' τ ≫ a' ≫ V'.1.ι = pullback.snd a' τ ≫ V.1.ι
    rw [← hτ, pullback.condition_assoc])
  have hpb : IsPullback k.left (pullback.snd a' τ) (D.param V').hom V.1.ι := by
    have h : IsPullback (pullback.fst a' τ) (pullback.snd a' τ) (a' ≫ V'.1.ι) (τ ≫ V'.1.ι) :=
      IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a' τ V'.1.ι)
    rw [hτ] at h
    exact h
  have hY : IsUniversalOn A V.1 ((rp[A] k).obj (D.family V')) :=
    isUniversalOn_of_isPullback A (leOfHom f) (D.family_universal V') k (pullback.snd a' τ)
      rfl hpb
  have hYa : IsAlgebraicallyTrivialFamilyViaSmoothFamily A ((rp[A] k).obj (D.family V')) :=
    smoothFamilyPullback S A _ _ k _ (D.family_algTriv V')
  have : QuasiSeparated Y.hom := by dsimp [Y]; infer_instance
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have hsq : (D.transition (leOfHom f)).left ≫ a' = pullback.snd _ _ ≫ τ :=
    (D.natTrans hW).naturality f
  let ℓ : D.param V ⟶ Y := Over.homMk (pullback.lift _ _ hsq) (by
    change pullback.lift _ _ hsq ≫ pullback.snd a' τ ≫ V.1.ι = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have hℓ : ℓ ≫ k = D.transition (leOfHom f) := by
    ext
    exact pullback.lift_fst _ _ _
  have hiso : IsIso ℓ :=
    isIso_of_isUniversalOn A hY (D.family_universal V) hYa (D.family_algTriv V)
      (range_comp_ι_subset V.1 _) (D.range_param V) ℓ
      (by rw [cm_pullback, hℓ, D.transition_spec])
  have : IsIso ℓ.left := (inferInstance : IsIso ((Over.forget S).map ℓ))
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso ℓ.left) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- The relative gluing datum of the local parameters. -/
def gluingData : (basisCover W hW).RelativeGluingData where
  functor := D.functor hW
  natTrans := D.natTrans hW
  equifibered := D.equifibered hW

/-- The glued parameter over `S`. -/
def glued : Over S := Over.mk (D.gluingData hW).toBase

/-- The inclusion of a local parameter into the glued parameter. -/
def glueι (V : (basisCover W hW).I₀) : D.param V ⟶ D.glued hW :=
  Over.homMk (colimit.ι (D.gluingData hW).functor V) (by
    change colimit.ι (D.gluingData hW).functor V ≫ (D.gluingData hW).toBase = _
    rw [Scheme.Cover.RelativeGluingData.ι_toBase]
    rfl)

section Classes

lemma cover_f_hom (V : (basisCover W hW).I₀) :
    (D.gluingData hW).cover.f V ≫ (D.glued hW).hom = (D.param V).hom :=
  Over.w (D.glueι hW V)

/-- A member of the glued cover, as an object over `S`, maps to the local parameter. -/
def toParam (V : (basisCover W hW).I₀) :
    Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom) ⟶ D.param V :=
  Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact (D.cover_f_hom hW V).symm)

/-- The local parameter maps to the corresponding member of the glued cover. -/
def ofParam (V : (basisCover W hW).I₀) :
    D.param V ⟶ Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom) :=
  Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact D.cover_f_hom hW V)

lemma ofParam_toParam (V : (basisCover W hW).I₀) : D.ofParam hW V ≫ D.toParam hW V = 𝟙 _ := by
  ext
  simp [ofParam, toParam]

lemma glueι_eq (V : (basisCover W hW).I₀) :
    D.glueι hW V = D.ofParam hW V ≫ (Over.homMk ((D.gluingData hW).cover.f V) :
      Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom) ⟶ D.glued hW) := by
  ext
  simp [ofParam]
  rfl

/-- The local class on a member of the glued cover. -/
def localClass (V : (basisCover W hW).I₀) :
    RigidifiedClasses A (Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom)) :=
  cp[A] (D.toParam hW V) (cl[A] (D.family V))

lemma transition_glueι {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    D.transition (leOfHom f) ≫ D.glueι hW V' = D.glueι hW V := by
  ext
  exact colimit.w (D.gluingData hW).functor f

lemma cp_toParam {Y : Over S} {k V : (basisCover W hW).I₀} (hkV : k ⟶ V)
    (g : Y ⟶ Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom)) (n : Y ⟶ D.param k)
    (hg : g.left = n.left ≫ (D.transition (leOfHom hkV)).left) :
    cp[A] (g ≫ D.toParam hW V) (cl[A] (D.family V)) = cp[A] n (cl[A] (D.family k)) := by
  have : g ≫ D.toParam hW V = n ≫ D.transition (leOfHom hkV) := by
    ext
    simp [toParam, hg]
  rw [this]
  exact D.cp_transition _ n

/-- The local classes glue to a class on the glued parameter. -/
theorem exists_gluedClass (glue : RigidifiedClassesZariskiGluingStatement.{u}) :
    ∃ q₀ : RigidifiedClasses A (D.glued hW),
      ∀ V, cp[A] (D.glueι hW V) q₀ = cl[A] (D.family V) := by
  refine Exists.elim (glue S A (D.glued hW) (D.gluingData hW).cover (D.localClass hW)
    (fun V V' ↦ ?_)) (fun q₀ hq₀ ↦ ⟨q₀, fun V ↦ ?_⟩)
  rotate_left
  · rw [D.glueι_eq hW V, ← classesPullback_comp, hq₀, localClass, classesPullback_comp, D.ofParam_toParam, cp_id]
  · apply rigidifiedClassesZariskiSeparated S A _
      ((D.gluingData hW).cover.intersectionOfLocallyDirected V V')
    rintro ⟨k, a, b⟩
    rw [classesPullback_comp, classesPullback_comp, localClass, localClass, classesPullback_comp, classesPullback_comp]
    have hn : 𝟙 _ ≫ (D.param k).hom =
        ((D.gluingData hW).cover.intersectionOfLocallyDirected V V').f ⟨k, a, b⟩ ≫
          pullback.fst ((D.gluingData hW).cover.f V) ((D.gluingData hW).cover.f V') ≫
            (D.gluingData hW).cover.f V ≫ (D.glued hW).hom := by
      rw [Category.id_comp, Scheme.Cover.intersectionOfLocallyDirected_f, pullback.lift_fst_assoc,
        D.cover_f_hom]
      exact (Over.w (D.transition (leOfHom a))).symm
    let n : Over.mk (((D.gluingData hW).cover.intersectionOfLocallyDirected V V').f ⟨k, a, b⟩ ≫
          pullback.fst ((D.gluingData hW).cover.f V) ((D.gluingData hW).cover.f V') ≫
            (D.gluingData hW).cover.f V ≫ (D.glued hW).hom) ⟶ D.param k :=
      Over.homMk (𝟙 (D.param k).left) hn
    refine (D.cp_toParam hW a _ n ?_).trans (D.cp_toParam hW b _ n ?_).symm
    · simp only [Over.comp_left, Over.homMk_left, Scheme.Cover.intersectionOfLocallyDirected_f,
        pullback.lift_fst]
      rfl
    · simp only [Over.comp_left, Over.homMk_left, Scheme.Cover.intersectionOfLocallyDirected_f,
        pullback.lift_snd]
      rfl

end Classes

section Universal

variable (T : Over S) [QuasiSeparatedSpace T.left] (q : AlgebraicallyTrivialClassesViaSmoothFamily A T)

omit [QuasiSeparatedSpace S] in
lemma existsUnique_testMap (V : (basisCover W hW).I₀) :
    ∃! h : test hW T V ⟶ D.param V,
      cm[A] (D.family V) (test hW T V) h = cp[A] (testIncl hW T V) q.val :=
  D.family_universal V (test hW T V) (range_test hW T V) (atPullback A (testIncl hW T V) q)

/-- The local classifying map on a member of the test cover. -/
def testMap (V : (basisCover W hW).I₀) : test hW T V ⟶ D.param V :=
  (D.existsUnique_testMap hW T q V).exists.choose

omit [QuasiSeparatedSpace S] in
lemma testMap_spec (V : (basisCover W hW).I₀) :
    cm[A] (D.family V) (test hW T V) (D.testMap hW T q V) = cp[A] (testIncl hW T V) q.val :=
  (D.existsUnique_testMap hW T q V).exists.choose_spec

lemma testTrans_testMap {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    testTrans hW T f ≫ D.testMap hW T q V' =
      D.testMap hW T q V ≫ D.transition (leOfHom f) := by
  have hle : V.1 ≤ V'.1 := leOfHom f
  refine eq_of_cm_eq A (D.family_universal V')
    ((range_test hW T V).trans (SetLike.coe_subset_coe.mpr hle)) ?_ ?_
  · rw [cm_comp, D.testMap_spec, classesPullback_comp, testTrans_testIncl]
    exact isAlgTrivClass_pullback A _ q.2
  · rw [cm_comp, D.testMap_spec, classesPullback_comp, testTrans_testIncl, cm_comp, D.transition_spec]
    exact (D.testMap_spec hW T q V).symm

lemma classify_compat {V V' : (testCover hW T).I₀} (f : V ⟶ V') :
    (testCover hW T).trans f ≫ (D.testMap hW T q V').left ≫ (D.glueι hW V').left =
      (D.testMap hW T q V).left ≫ (D.glueι hW V).left := by
  have h := congrArg (fun k ↦ k.left ≫ (D.glueι hW V').left) (D.testTrans_testMap hW T q f)
  have h3 := congrArg Over.Hom.left (D.transition_glueι hW f)
  simp only [Over.comp_left, Category.assoc] at h h3
  rw [h3] at h
  exact h

lemma classify_w (V : (testCover hW T).I₀) :
    ((D.testMap hW T q V).left ≫ (D.glueι hW V).left) ≫ (D.glued hW).hom =
      (testCover hW T).f V ≫ T.hom := by
  rw [Category.assoc, Over.w (D.glueι hW V)]
  exact Over.w (D.testMap hW T q V)

/-- The glued classifying map of a test. -/
def classify : T ⟶ D.glued hW :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (testCover hW T)
    (fun V ↦ (D.testMap hW T q V).left ≫ (D.glueι hW V).left)
    (fun f ↦ D.classify_compat hW T q f) (D.classify_w hW T q)

lemma testIncl_classify (V : (basisCover W hW).I₀) :
    testIncl hW T V ≫ D.classify hW T q = D.testMap hW T q V ≫ D.glueι hW V := by
  ext
  change (testCover hW T).f V ≫ (D.classify hW T q).left =
    (D.testMap hW T q V).left ≫ (D.glueι hW V).left
  unfold classify
  exact Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left (testCover hW T) _
    (fun f ↦ D.classify_compat hW T q f) (D.classify_w hW T q) V

variable (q₀ : RigidifiedClasses A (D.glued hW))
  (hq₀ : ∀ V, cp[A] (D.glueι hW V) q₀ = cl[A] (D.family V))

include hq₀ in
lemma cp_classify : cp[A] (D.classify hW T q) q₀ = q.val := by
  apply rigidifiedClassesZariskiSeparated S A T (testCover hW T)
  intro V
  change cp[A] (testIncl hW T V) _ = cp[A] (testIncl hW T V) _
  rw [classesPullback_comp, D.testIncl_classify, ← classesPullback_comp, hq₀]
  exact D.testMap_spec hW T q V

include hq₀ in
lemma classify_unique (k : T ⟶ D.glued hW) (hk : cp[A] k q₀ = q.val) :
    k = D.classify hW T q := by
  ext1
  apply (testCover hW T).hom_ext
  intro (V : (basisCover W hW).I₀)
  have hpb := (D.gluingData hW).isPullback_natTrans_ι_toBase V
  have w : pullback.snd T.hom V.1.ι ≫ (basisCover W hW).f V =
      ((testCover hW T).f V ≫ k.left) ≫ (D.gluingData hW).toBase := by
    rw [Category.assoc]
    change _ = _ ≫ k.left ≫ (D.glued hW).hom
    rw [Over.w k]
    exact pullback.condition.symm
  let m : test hW T V ⟶ D.param V := Over.homMk (hpb.lift _ _ w) (by
    change hpb.lift _ _ w ≫ (D.gluingData hW).natTrans.app V ≫ V.1.ι = _
    rw [hpb.lift_fst_assoc]
    exact (test_hom hW T V).symm)
  have hm : m ≫ D.glueι hW V = testIncl hW T V ≫ k := by
    ext
    exact hpb.lift_snd _ _ w
  have hmV : m = D.testMap hW T q V := by
    refine (D.existsUnique_testMap hW T q V).unique ?_ (D.testMap_spec hW T q V)
    change cp[A] m (cl[A] (D.family V)) = _
    rw [← hq₀, classesPullback_comp, hm, ← classesPullback_comp, hk]
  have h1 := congrArg Over.Hom.left hm
  have h2 := congrArg Over.Hom.left (D.testIncl_classify hW T q V)
  simp only [Over.comp_left, Over.homMk_left] at h1 h2
  rw [← h1, hmV, ← h2]

include hq₀ in
theorem existsUnique_classify :
    ∃! h : T ⟶ D.glued hW, cp[A] h q₀ = q.val :=
  ⟨D.classify hW T q, D.cp_classify hW T q q₀ hq₀,
    fun k hk ↦ D.classify_unique hW T q q₀ hq₀ k hk⟩

end Universal

/-- A representative of the glued class is a universal family on the glued parameter. -/
theorem exists_universal (glue : RigidifiedClassesZariskiGluingStatement.{u}) :
    ∃ L : RigidifiedFamily A (D.glued hW), IsUniversalSmoothFamilyOnQuasiSeparatedTests A L := by
  obtain ⟨q₀, hq₀⟩ := D.exists_gluedClass hW glue
  let L₀ : RigidifiedFamily A (D.glued hW) := q₀.out
  have hL₀ : cl[A] L₀ = q₀ := Quotient.out_eq q₀
  have hcm : ∀ (T : Over S) (h : T ⟶ D.glued hW), cm[A] L₀ T h = cp[A] h q₀ := by
    intro T h
    rw [← hL₀]
    rfl
  refine ⟨L₀, ?_, fun T _ q ↦ ?_⟩
  · apply isAlgebraicallyTrivialFamily_of_openCover A L₀ (D.gluingData hW).cover
    intro V
    have e : (Over.homMk ((D.gluingData hW).cover.f V) :
        Over.mk ((D.gluingData hW).cover.f V ≫ (D.glued hW).hom) ⟶ D.glued hW) =
          D.toParam hW V ≫ D.glueι hW V := by
      ext
      simp [toParam]
      rfl
    change IsAlgebraicallyTrivialClassViaSmoothFamily A (cl[A] ((rp[A] _).obj L₀))
    rw [cl_pullback, hL₀, e, ← classesPullback_comp, hq₀]
    exact isAlgTrivClass_pullback A _ (D.family_algTriv V)
  · simp_rw [hcm]
    exact D.existsUnique_classify hW T q q₀ hq₀

end LocalData

end LocalData

end Langlands.AbelianScheme.SmoothFamilyOpenCover
