import Langlands.AlgebraicGeometry.Units.FiniteAlgebraDeterminant
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Group.Units.Equiv

/-! # Global units and the actual global-functions algebra over a field -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.FieldGlobalUnits

section General

variable {R : CommRingCat.{u}} {X Z Y W T : Scheme.{u}}
  (a : Z ⟶ Spec R) (f : X ⟶ Spec R) (j : X ⟶ Z) (wj : j ≫ a = f)

/-- The actual pullback on global functions as a map of base modules. -/
def sectionsMap :
    (relativeGlobalSections a).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (relativeGlobalSections a).map (Langlands.Scheme.Modules.unitToPushforwardUnit j) ≫
    (relativeGlobalSectionsCompIso j a).hom.app _ ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforwardCongr wj).hom.app _)

lemma sectionsMap_apply (x : Γ(Z, ⊤)) : sectionsMap a f j wj x = j.appTop x := by
  change X.presheaf.map (𝟙 (op ⊤)) (j.appTop x) = _
  simp

variable (r : W ⟶ T) (p : Y ⟶ T) (q : Y ⟶ W) (wq : q ≫ r = p)

/-- The actual pullback on structure-sheaf direct images. -/
def directImageMap :
    (Scheme.Modules.pushforward r).obj (SheafOfModules.unit W.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (Scheme.Modules.pushforward r).map (Langlands.Scheme.Modules.unitToPushforwardUnit q) ≫
    (Scheme.Modules.pushforwardComp q r).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr wq).hom.app _

lemma directImageMap_top (x : Γ(W, ⊤)) :
    (directImageMap r p q wq).app ⊤ x = q.appTop x := by
  change Y.presheaf.map (𝟙 (op ⊤)) (q.appTop x) = _
  simp

variable (t : T ⟶ Spec R) (g : Y ⟶ X) (v : W ⟶ Z)
  (hf : g ≫ f = p ≫ t) (ha : v ≫ a = r ≫ t) (hv : q ≫ v = g ≫ j)

include hv in
/-- The canonical global-functions sheaf comparison respects an actual map
of the original schemes and its actual map after base change. -/
lemma directImageSheafMap_naturality :
    (Scheme.Modules.pullback t).map ((tilde.functor R).map (sectionsMap a f j wj)) ≫
        FieldGlobalFunctions.directImageSheafMap f t g p hf =
      FieldGlobalFunctions.directImageSheafMap a t v r ha ≫ directImageMap r p q wq := by
  apply ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _).injective
  change ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _)
    ((tilde.functor R ⋙ Scheme.Modules.pullback t).map (sectionsMap a f j wj) ≫
      FieldGlobalFunctions.directImageSheafMap f t g p hf) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [FieldGlobalFunctions.directImageSheafMap_homEquiv,
    FieldGlobalFunctions.directImageSheafMap_homEquiv]
  ext x
  change FieldGlobalFunctions.directImageGlobalSectionsMap f t g p hf
      (sectionsMap a f j wj x) =
    (directImageMap r p q wq).app ⊤
      (FieldGlobalFunctions.directImageGlobalSectionsMap a t v r ha x)
  rw [sectionsMap_apply, directImageMap_top,
    FieldGlobalFunctions.directImageGlobalSectionsMap_apply,
    FieldGlobalFunctions.directImageGlobalSectionsMap_apply]
  have he := congrArg (fun b : Y ⟶ Z => b.appTop) hv
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at he
  exact (ConcreteCategory.congr_hom he x).symm

variable [IsProper a] [IsProper f]
  (hfa : IsPullback v r a t) (hff : IsPullback g p f t)
  [IsIso (sectionsMap a f j wj)]

include wj hv hfa hff in
/-- Proper-field comparison reduces invertibility of this actual direct-image
map to invertibility of the original global-function map. -/
lemma isIso_directImageMap_of_sectionsMap
    {k : Type u} [Field k] (eR : R = CommRingCat.of k) :
    IsIso (directImageMap r p q wq) := by
  subst R
  have := FieldGlobalFunctions.isIso_directImageSheafMap a t v r hfa
  have := FieldGlobalFunctions.isIso_directImageSheafMap f t g p hff
  have hi : IsIso (FieldGlobalFunctions.directImageSheafMap a t v r hfa.w ≫
      directImageMap r p q wq) := by
    rw [← directImageSheafMap_naturality a f j wj r p q wq t g v hff.w hfa.w hv]
    infer_instance
  rwa [isIso_comp_left_iff] at hi

end General

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual global-functions spectrum with its given field map. -/
abbrev algebraSchemeMap : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (structureRingHom f)

/-- The canonical map to the spectrum of actual global functions is over k. -/
lemma toSpecΓ_over : X.toSpecΓ ≫ algebraSchemeMap f = f := by
  simp only [algebraSchemeMap, structureRingHom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality]
  simp

/-- Its map on global functions is invertible. -/
lemma isIso_sectionsMap_toSpecΓ :
    IsIso (sectionsMap (algebraSchemeMap f) f X.toSpecΓ (toSpecΓ_over f)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun x => sectionsMap (algebraSchemeMap f) f X.toSpecΓ (toSpecΓ_over f) x)
  have he : (fun x => sectionsMap (algebraSchemeMap f) f X.toSpecΓ (toSpecΓ_over f) x) =
      (fun x => X.toSpecΓ.appTop x) := funext (sectionsMap_apply _ _ _ _)
  rw [he, Scheme.toSpecΓ_appTop]
  exact ConcreteCategory.bijective_of_isIso _

/-- The actual global-functions spectrum is finite over k. -/
lemma finite_algebraSchemeMap [IsProper f] : IsFinite (algebraSchemeMap f) := by
  let := GlobalFunctionsAlgebra.algebra f
  have := FieldGlobalFunctions.finite_algebra f
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- On any test scheme, the actual base change of the canonical map
X to Spec Gamma(X,O_X). -/
def schemeMap (T : Over (Spec (CommRingCat.of k))) :
    (Picard.relativeSpace f).obj T ⟶ (Picard.relativeSpace (algebraSchemeMap f)).obj T :=
  pullback.lift (pullback.fst T.hom f) (pullback.snd T.hom f ≫ X.toSpecΓ)
    (by rw [Category.assoc, toSpecΓ_over, pullback.condition])

@[reassoc (attr := simp)]
lemma schemeMap_fst (T : Over (Spec (CommRingCat.of k))) :
    schemeMap f T ≫ pullback.fst T.hom (algebraSchemeMap f) = pullback.fst T.hom f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma schemeMap_snd (T : Over (Spec (CommRingCat.of k))) :
    schemeMap f T ≫ pullback.snd T.hom (algebraSchemeMap f) =
      pullback.snd T.hom f ≫ X.toSpecΓ :=
  pullback.lift_snd _ _ _

/-- The comparison uses the actual functorial fibre-product maps. -/
lemma schemeMap_naturality {T U : Over (Spec (CommRingCat.of k))} (h : T ⟶ U) :
    (Picard.relativeSpace f).map h ≫ schemeMap f U =
      schemeMap f T ≫ (Picard.relativeSpace (algebraSchemeMap f)).map h := by
  apply pullback.hom_ext
  · simp [Picard.relativeSpace, Over.pullback, schemeMap, Category.assoc]
  · simp [Picard.relativeSpace, Over.pullback, schemeMap, Category.assoc]

/-- Actual pullback on unit groups along the base-changed canonical map. -/
def unitsMap (T : Over (Spec (CommRingCat.of k))) :
    RelativeGlobalUnits.sections (algebraSchemeMap f) T →*
      RelativeGlobalUnits.sections f T :=
  _root_.Units.map (schemeMap f T).appTop.hom.toMonoidHom

@[simp]
lemma unitsMap_val (T : Over (Spec (CommRingCat.of k)))
    (a : RelativeGlobalUnits.sections (algebraSchemeMap f) T) :
    ↑(unitsMap f T a) = (schemeMap f T).appTop a.val := rfl

/-- Naturality is ordinary pullback of the same global unit. -/
lemma unitsMap_restriction {T U : Over (Spec (CommRingCat.of k))} (h : T ⟶ U)
    (a : RelativeGlobalUnits.sections (algebraSchemeMap f) U) :
    RelativeGlobalUnits.restriction f h (unitsMap f U a) =
      unitsMap f T (RelativeGlobalUnits.restriction (algebraSchemeMap f) h a) := by
  apply _root_.Units.ext
  change ((Picard.relativeSpace f).map h).appTop ((schemeMap f U).appTop _) =
    (schemeMap f T).appTop (((Picard.relativeSpace (algebraSchemeMap f)).map h).appTop _)
  have he := congrArg (fun b => b.appTop) (schemeMap_naturality f h)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at he
  exact ConcreteCategory.congr_hom he a.val

/-- The natural comparison in the group-valued convention. -/
def groupComparison : RelativeGlobalUnits.groupPresheaf (algebraSchemeMap f) ⟶
    RelativeGlobalUnits.groupPresheaf f where
  app T := CommGrpCat.ofHom (unitsMap f T.unop)
  naturality {T U} h := by
    apply CommGrpCat.hom_ext
    exact MonoidHom.ext (fun a => (unitsMap_restriction f h.unop a).symm)

/-- The natural comparison on every test scheme, in the lifted convention. -/
def presheafComparison : RelativeGlobalUnits.presheaf (algebraSchemeMap f) ⟶
    RelativeGlobalUnits.presheaf f where
  app T := ↾fun a => ⟨unitsMap f T.unop a.down⟩
  naturality {T U} h := by
    ext a
    apply ULift.ext
    exact (unitsMap_restriction f h.unop a.down).symm

@[simp]
lemma presheafComparison_app (T : Over (Spec (CommRingCat.of k)))
    (a : (RelativeGlobalUnits.presheaf (algebraSchemeMap f)).obj (op T)) :
    ((presheafComparison f).app (op T) a).down = unitsMap f T a.down := rfl

variable [IsProper f]

/-- The map induced by the actual canonical scheme map is invertible on
structure-sheaf direct images over every test scheme. -/
lemma isIso_directImageMap_schemeMap (T : Over (Spec (CommRingCat.of k))) :
    IsIso (directImageMap (pullback.fst T.hom (algebraSchemeMap f))
      (pullback.fst T.hom f) (schemeMap f T) (schemeMap_fst f T)) := by
  have := finite_algebraSchemeMap f
  have := isIso_sectionsMap_toSpecΓ f
  exact isIso_directImageMap_of_sectionsMap (algebraSchemeMap f) f X.toSpecΓ
    (toSpecΓ_over f) (pullback.fst T.hom (algebraSchemeMap f))
    (pullback.fst T.hom f) (schemeMap f T) (schemeMap_fst f T) T.hom
    (pullback.snd T.hom f) (pullback.snd T.hom (algebraSchemeMap f))
    (schemeMap_snd f T) (IsPullback.of_hasPullback T.hom (algebraSchemeMap f)).flip
    (IsPullback.of_hasPullback T.hom f).flip rfl

/-- Canonical pullback of global functions along this actual map is invertible
on every test scheme, with no quasi-compactness hypothesis on the test. -/
lemma isIso_schemeMap_appTop (T : Over (Spec (CommRingCat.of k))) :
    IsIso (schemeMap f T).appTop := by
  have := isIso_directImageMap_schemeMap f T
  have hi : IsIso ((directImageMap (pullback.fst T.hom (algebraSchemeMap f))
      (pullback.fst T.hom f) (schemeMap f T) (schemeMap_fst f T)).app ⊤) := by
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have he : (fun x => (directImageMap (pullback.fst T.hom (algebraSchemeMap f))
      (pullback.fst T.hom f) (schemeMap f T) (schemeMap_fst f T)).app ⊤ x) =
      (fun x => (schemeMap f T).appTop x) := funext (directImageMap_top _ _ _ _)
  have hb := ConcreteCategory.bijective_of_isIso
    ((directImageMap (pullback.fst T.hom (algebraSchemeMap f))
      (pullback.fst T.hom f) (schemeMap f T) (schemeMap_fst f T)).app ⊤)
  change Function.Bijective (fun x => _) at hb
  rw [he] at hb
  exact hb

/-- The equivalence of actual unit groups induced by the canonical scheme map. -/
def unitsEquiv (T : Over (Spec (CommRingCat.of k))) :
    RelativeGlobalUnits.sections (algebraSchemeMap f) T ≃*
      RelativeGlobalUnits.sections f T := by
  have := isIso_schemeMap_appTop f T
  exact _root_.Units.mapEquiv
    (asIso (schemeMap f T).appTop).commRingCatIsoToRingEquiv.toMulEquiv

@[simp]
lemma unitsEquiv_apply (T : Over (Spec (CommRingCat.of k)))
    (a : RelativeGlobalUnits.sections (algebraSchemeMap f) T) :
    unitsEquiv f T a = unitsMap f T a := rfl

/-- The canonical comparison is a natural isomorphism of group-valued presheaves. -/
def groupComparisonIso : RelativeGlobalUnits.groupPresheaf (algebraSchemeMap f) ≅
    RelativeGlobalUnits.groupPresheaf f :=
  NatIso.ofComponents (fun T => MulEquiv.toCommGrpIso
    (X := (RelativeGlobalUnits.groupPresheaf (algebraSchemeMap f)).obj T)
    (Y := (RelativeGlobalUnits.groupPresheaf f).obj T) (unitsEquiv f T.unop))
    (fun h => (groupComparison f).naturality h)

/-- The canonical comparison is a natural isomorphism on all test schemes. -/
def presheafComparisonIso : RelativeGlobalUnits.presheaf (algebraSchemeMap f) ≅
    RelativeGlobalUnits.presheaf f :=
  NatIso.ofComponents (fun T =>
    (Equiv.ulift.trans ((unitsEquiv f T.unop).toEquiv.trans Equiv.ulift.symm)).toIso)
    (fun h => (presheafComparison f).naturality h)

@[simp]
lemma presheafComparisonIso_hom : (presheafComparisonIso f).hom = presheafComparison f := rfl

/-- Relative global units of a proper field scheme are the units of its actual
finite global-functions algebra, naturally on the entire slice category. -/
def finiteAlgebraPresheafIso :
    letI := GlobalFunctionsAlgebra.algebra f
    RelativeGlobalUnits.presheaf f ≅ FiniteAlgebraUnits.presheaf k Γ(X, ⊤) :=
  (presheafComparisonIso f).symm

/-- The inverse comparison is precisely pullback along the actual canonical
map after each test-scheme base change. -/
lemma finiteAlgebraPresheafIso_inv :
    letI := GlobalFunctionsAlgebra.algebra f
    (finiteAlgebraPresheafIso f).inv = presheafComparison f := rfl

end Field

end Langlands.AlgebraicGeometry.FieldGlobalUnits
