import Langlands.GroupScheme.RelativeUnipotent.LiftedPointCharts

/-! # The actual linear descent datum of original lifted point charts -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts

open NaturalModuleTransformations

variable {S X : Scheme.{u}} {p : X ⟶ S} {V : GroupScheme S} {F : X.Modules}
  (C : LiftedModuleCharts p V F)

/-- The inverse section comparison is the actual inverse module isomorphism. -/
lemma sectionComposition_symm {Y : Scheme.{u}} (a : Y ⟶ X) (T : Over Y)
    (x : GlobalSections ((Scheme.Modules.pullback (T.hom ≫ a)).obj F)) :
    (baseChangeSectionEquiv a F T).symm x =
      ((Scheme.Modules.pullbackComp T.hom a).inv.app F).app ⊤ x := by
  rw [← baseChangeLinearEquiv_symm_apply]
  rfl

/-- A fixed-lift point chart uses the actual inverse module comparison. -/
lemma atLift_toAdd {Y : Scheme.{u}} (f : Y ⟶ S) (a : Y ⟶ X) (ha : a ≫ p = f)
    (T : Over Y) (x : T ⟶ ((GroupScheme.baseChange f).obj V).X) :
    ((C.atLift f a ha).equiv T x).toAdd =
      ((Scheme.Modules.pullbackComp T.hom a).inv.app F).app ⊤
        (C.equiv ((Over.map f).obj T) (T.hom ≫ a)
          (by rw [Category.assoc, ha]; rfl) (baseChangePointsEquiv f V T x)).toAdd := by
  change (baseChangeSectionEquiv a F T).symm _ = _
  exact sectionComposition_symm a T _

/-- Compatibility of an actual overlap module map with the original point
charts, after every actual pullback and every specified composite comparison. -/
def MapCompatible {Y : Scheme.{u}} (a c : Y ⟶ X)
    (φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F) : Prop :=
  ∀ (T : Over S) (k : T.left ⟶ Y) (a' c' : T.left ⟶ X)
    (hka : k ≫ a = a') (hkc : k ≫ c = c')
    (ha' : a' ≫ p = T.hom) (hc' : c' ≫ p = T.hom) (x : T ⟶ V.X),
    (tr k hka hkc φ).app ⊤ (C.equiv T a' ha' x).toAdd =
      (C.equiv T c' hc' x).toAdd

lemma mapCompatible_atLift {Y : Scheme.{u}} (f : Y ⟶ S) (a c : Y ⟶ X)
    (ha : a ≫ p = f) (hc : c ≫ p = f)
    (φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F)
    (hφ : C.MapCompatible a c φ) (T : Over Y)
    (x : T ⟶ ((GroupScheme.baseChange f).obj V).X) :
    ((Scheme.Modules.pullback T.hom).map φ).app ⊤ ((C.atLift f a ha).equiv T x).toAdd =
      ((C.atLift f c hc).equiv T x).toAdd := by
  apply (baseChangeSectionEquiv c F T).injective
  rw [C.atLift_apply]
  rw [C.atLift_toAdd]
  change (tr T.hom rfl rfl φ).app ⊤
      (C.equiv ((Over.map f).obj T) (T.hom ≫ a) _
        (baseChangePointsEquiv f V T x)).toAdd = _
  exact hφ ((Over.map f).obj T) T.hom (T.hom ≫ a) (T.hom ≫ c) rfl rfl
    (by rw [Category.assoc, ha]; rfl) (by rw [Category.assoc, hc]; rfl)
    (baseChangePointsEquiv f V T x)

/-- The normalized fixed-lift action recovers compatibility on every original
test and every prescribed composite lift. -/
lemma mapCompatible_of_atLift {Y : Scheme.{u}} (f : Y ⟶ S) (a c : Y ⟶ X)
    (ha : a ≫ p = f) (hc : c ≫ p = f)
    (φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F)
    (hφ : ∀ (T : Over Y) (x : T ⟶ ((GroupScheme.baseChange f).obj V).X),
      ((Scheme.Modules.pullback T.hom).map φ).app ⊤ ((C.atLift f a ha).equiv T x).toAdd =
        ((C.atLift f c hc).equiv T x).toAdd) :
    C.MapCompatible a c φ := by
  intro T k a' c' hka hkc ha' hc' x
  subst a'
  subst c'
  have hbase : k ≫ f = T.hom := by rw [← ha, ← Category.assoc, ha']
  have H : ∀ (q : T.left ⟶ S) (hq : k ≫ f = q)
      (haq : (k ≫ a) ≫ p = q) (hcq : (k ≫ c) ≫ p = q)
      (z : Over.mk q ⟶ V.X),
      (tr k rfl rfl φ).app ⊤ (C.equiv (Over.mk q) (k ≫ a) haq z).toAdd =
        (C.equiv (Over.mk q) (k ≫ c) hcq z).toAdd := by
    intro q hq haq hcq z
    subst q
    let A : Over Y := Over.mk k
    let zz := (baseChangePointsEquiv f V A).symm z
    have H0 := congrArg (baseChangeSectionEquiv c F A) (hφ A zz)
    rw [C.atLift_apply, C.atLift_toAdd] at H0
    change (tr k rfl rfl φ).app ⊤
        (C.equiv (Over.mk (k ≫ f)) (k ≫ a) haq
          (baseChangePointsEquiv f V A zz)).toAdd =
      (C.equiv (Over.mk (k ≫ f)) (k ≫ c) hcq
        (baseChangePointsEquiv f V A zz)).toAdd at H0
    rw [MulEquiv.apply_symm_apply] at H0
    exact H0
  exact H T.hom hbase ha' hc' x

/-- The all-test original point compatibility detects an actual module map. -/
lemma mapCompatible_hom_ext (Q : DisjointFreePresentation F)
    {Y : Scheme.{u}} (a c : Y ⟶ X) (h : a ≫ p = c ≫ p)
    (φ ψ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F)
    (hφ : C.MapCompatible a c φ) (hψ : C.MapCompatible a c ψ) : φ = ψ :=
  (C.atLift (a ≫ p) a rfl).compatible_hom_ext (C.atLift (a ≫ p) c h.symm)
    (Q.baseChange a) φ ψ
    (C.mapCompatible_atLift (a ≫ p) a c rfl h.symm φ hφ)
    (C.mapCompatible_atLift (a ≫ p) a c rfl h.symm ψ hψ)

/-- Actual compatibility is preserved by arbitrary pullback transport. -/
lemma MapCompatible.tr {Y Z : Scheme.{u}} {a c : Y ⟶ X}
    {φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F}
    (hφ : C.MapCompatible a c φ) (k : Z ⟶ Y) (a' c' : Z ⟶ X)
    (ha : k ≫ a = a') (hc : k ≫ c = c') :
    C.MapCompatible a' c' (tr k ha hc φ) := by
  intro T l a'' c'' hla hlc ha'' hc'' x
  rw [tr_tr k l ha hc hla hlc
    (by rw [Category.assoc, ha, hla]) (by rw [Category.assoc, hc, hlc])]
  exact hφ T (l ≫ k) a'' c'' _ _ ha'' hc'' x

/-- Original point compatibility is preserved by actual composition. -/
lemma MapCompatible.comp {Y : Scheme.{u}} {a b c : Y ⟶ X}
    (hab : a ≫ p = b ≫ p)
    {φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback b).obj F}
    {ψ : (Scheme.Modules.pullback b).obj F ⟶ (Scheme.Modules.pullback c).obj F}
    (hφ : C.MapCompatible a b φ) (hψ : C.MapCompatible b c ψ) :
    C.MapCompatible a c (φ ≫ ψ) := by
  intro T k a' c' hka hkc ha' hc' x
  have hb' : (k ≫ b) ≫ p = T.hom := by
    rw [Category.assoc, ← hab, ← Category.assoc, hka, ha']
  rw [tr_comp k hka rfl hkc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    hφ T k a' (k ≫ b) hka rfl ha' hb' x, hψ T k (k ≫ b) c' rfl hkc hb' hc' x]

/-- The original fixed-lift point transitions preserve scalars on every test. -/
def HasLinearTransitions : Prop :=
  ∀ (Y : Scheme.{u}) (f : Y ⟶ S) (a c : Y ⟶ X)
    (ha : a ≫ p = f) (hc : c ≫ p = f),
    (C.atLift f a ha).IsLinear (C.atLift f c hc)

variable (Q : DisjointFreePresentation F) (hLin : C.HasLinearTransitions)

/-- The actual module overlap isomorphism, reconstructed from the original
scalar-linear point transition. -/
def overlapIso {Y : Scheme.{u}} (a c : Y ⟶ X) (h : a ≫ p = c ≫ p) :
    (Scheme.Modules.pullback a).obj F ≅ (Scheme.Modules.pullback c).obj F :=
  (C.atLift (a ≫ p) a rfl).moduleIso (C.atLift (a ≫ p) c h.symm)
    (Q.baseChange a) (Q.baseChange c) (hLin Y (a ≫ p) a c rfl h.symm)

/-- The reconstructed original overlap isomorphism retains the original point
identity after every pullback and prescribed comparison. -/
lemma overlapIso_compatible {Y : Scheme.{u}} (a c : Y ⟶ X) (h : a ≫ p = c ≫ p) :
    C.MapCompatible a c (C.overlapIso Q hLin a c h).hom :=
  C.mapCompatible_of_atLift (a ≫ p) a c rfl h.symm _
    ((C.atLift (a ≫ p) a rfl).moduleIso_point (C.atLift (a ≫ p) c h.symm)
      (Q.baseChange a) (Q.baseChange c) (hLin Y (a ≫ p) a c rfl h.symm))

/-- Arbitrary base change of the original overlap isomorphism, with its
prescribed actual module comparisons. -/
lemma overlapIso_nat {Y Z : Scheme.{u}} (k : Z ⟶ Y) (a c : Y ⟶ X)
    (h : a ≫ p = c ≫ p) (h' : (k ≫ a) ≫ p = (k ≫ c) ≫ p) :
    (C.overlapIso Q hLin (k ≫ a) (k ≫ c) h').hom =
      tr k rfl rfl (C.overlapIso Q hLin a c h).hom := by
  apply C.mapCompatible_hom_ext Q (k ≫ a) (k ≫ c) h'
  · exact C.overlapIso_compatible Q hLin _ _ _
  · exact MapCompatible.tr C (C.overlapIso_compatible Q hLin a c h) k _ _ rfl rfl

/-- The cocycle follows from identity of the original point in all three
charts and faithfulness of actual module maps. -/
lemma overlapIso_coc {Y : Scheme.{u}} (a b c : Y ⟶ X)
    (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p) (h'' : a ≫ p = c ≫ p) :
    (C.overlapIso Q hLin a b h).hom ≫ (C.overlapIso Q hLin b c h').hom =
      (C.overlapIso Q hLin a c h'').hom := by
  apply C.mapCompatible_hom_ext Q a c h''
  · exact MapCompatible.comp C h (C.overlapIso_compatible Q hLin a b h)
      (C.overlapIso_compatible Q hLin b c h')
  · exact C.overlapIso_compatible Q hLin a c h''

/-- Actual scalar-linear original point charts construct an actual module
descent datum, without a supplied cocycle or effectivity premise. -/
def linearDatum : Datum p F where
  θ _ a c h := C.overlapIso Q hLin a c h
  nat _ _ k a c h h' := by
    simpa only [tr, compIso_rfl, Iso.app_inv, Iso.app_hom] using
      C.overlapIso_nat Q hLin k a c h h'
  coc _ a b c h h' h'' := C.overlapIso_coc Q hLin a b c h h' h''

/-- Transport along the identity, with its prescribed module comparisons, is
the original actual module morphism. -/
lemma tr_identity {Y : Scheme.{u}} (a c : Y ⟶ X)
    (φ : (Scheme.Modules.pullback a).obj F ⟶ (Scheme.Modules.pullback c).obj F) :
    tr (𝟙 Y) (Category.id_comp a) (Category.id_comp c) φ = φ := by
  have ha : (compIso (𝟙 Y) a a (Category.id_comp a) F).hom =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback a).obj F) := by
    rw [compIso_hom, Langlands.SchemeModule.RigidifiedModule.compHom_id_left]
    simp
  have hc : (compIso (𝟙 Y) c c (Category.id_comp c) F).hom =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback c).obj F) := by
    rw [compIso_hom, Langlands.SchemeModule.RigidifiedModule.compHom_id_left]
    simp
  apply (cancel_epi (compIso (𝟙 Y) a a (Category.id_comp a) F).hom).mp
  simp only [tr, Iso.hom_inv_id_assoc]
  rw [ha, hc]
  exact (Scheme.Modules.pullbackId Y).hom.naturality φ

/-- The actual datum preserves the original unnormalized charts on every
lifted original scheme test. -/
lemma linearDatum_compatible (T : Over S) (a c : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom) (x : T ⟶ V.X) :
    ((C.linearDatum Q hLin).θ T.left a c (ha.trans hc.symm)).hom.app ⊤
        (C.equiv T a ha x).toAdd = (C.equiv T c hc x).toAdd := by
  have H := C.overlapIso_compatible Q hLin a c (ha.trans hc.symm)
    T (𝟙 T.left) a c (Category.id_comp a) (Category.id_comp c) ha hc x
  rwa [tr_identity] at H

include C Q hLin in
/-- Effective actual module descent turns the original scalar-linear lifted
charts into the exact vector-bundle additive predicate. -/
lemma isVectorBundleAdditive_of_linearTransitions
    [IsAffineHom p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    [IsAffineHom V.X.hom] [Smooth V.X.hom] (hF : IsFiniteLocallyFree F) :
    IsVectorBundleAdditive V :=
  (C.withDatum (C.linearDatum Q hLin) (C.linearDatum_compatible Q hLin)).isVectorBundleAdditive hF

end Langlands.GroupScheme.RelativeUnipotent.LiftedModuleCharts
