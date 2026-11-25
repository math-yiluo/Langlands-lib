/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationCoefficientActions
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact

/-! # Continuous coefficient scalar localization

Source: Bhatt–Scholze, Proposition 6.8.14(2); Stacks Tags 015F, 010N and 05R6.
(blueprint: lem-per-rational-continuous-coefficient-derived-localization)

The independent-universe section and coefficient-action helpers are owned by this
item. The landed coefficient-action module and its DAG record are retained intact.

The assertion below spells out both the universal derived comparison and its raw
fraction descent. All coefficient actions are the specified global-section actions.
The raw coefficient ring is `Localization.Away t`; its canonical algebra isomorphism
with E transports both the raw source action and the localized section action.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC u v w wR wS r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace CategoryTheory

section CoefficientActions

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option linter.unusedSectionVars false in
/-- Image of a compatible coefficient family is again compatible.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization).
Proof: commute each restriction with the ring-sheaf morphism, and then use the
restriction compatibility of the original family. -/
theorem scalarLocalizationSectionsMap_memOfUniverses {R S : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (a : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (fun U ↦ f.hom.app U (a.val U)) ∈
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) := by
  intro U V g
  change S.obj.map g (f.hom.app U (a.val U)) = f.hom.app V (a.val V)
  have h := ConcreteCategory.congr_hom (f.hom.naturality g) (a.val U)
  change f.hom.app V (R.obj.map g (a.val U)) =
    S.obj.map g (f.hom.app U (a.val U)) at h
  rw [← h]
  exact congrArg (f.hom.app V) (a.property g)

/-- The map of global coefficient rings induced by a ring-sheaf morphism.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization). -/
def scalarLocalizationSectionsMapOfUniverses {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat) →+*
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun U ↦ (f.hom.app U).hom.comp
    ((Pi.evalRingHom (fun V ↦ R.obj.obj V) U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype))).codRestrict
    (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (scalarLocalizationSectionsMap_memOfUniverses f)

/-- The usual coefficient action on module-sheaf Homs, by restriction from global sections.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization). -/
@[instance_reducible]
def scalarLocalizationCoefficientLinearOfUniverses (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear A (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (a r) f g
    comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (a r) g }

/-- The induced coefficient action on the ordinary derived category.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization). -/
@[instance_reducible]
def scalarLocalizationDerivedLinearOfUniverses (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
  letI := scalarLocalizationCoefficientLinearOfUniverses A R a
  DerivedCategory.instLinear A _

/-- The localized coefficient is a unit in the ring of sections of R[1/t].
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization).
Proof: the sectionwise image of t is a unit by localization. Its inverses commute
with restriction by uniqueness of inverses. Apply sheafification to this section
and its inverse; their products remain one, also for the zero ring and empty site. -/
theorem scalarLocalizationSections_isUnitOfUniverses (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    IsUnit ((scalarLocalizationSectionsMapOfUniverses
      (ringedLocalizationRingUnitOfUniverses R (a t))).comp a t) := by
  classical
  let b := (scalarLocalizationSectionsMapOfUniverses
    (ringedLocalizationRingUnitOfUniverses R (a t))).comp a t
  have hu (U : Cᵒᵖ) : IsUnit (b.val U) := by
    change IsUnit ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R (a t))).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrierOfUniverses R (a t) U)
        ((a t).val U)))
    exact (IsLocalization.Away.algebraMap_isUnit (R := R.obj.obj U)
      (S := ringedSectionLocalizationCarrierOfUniverses R (a t) U) ((a t).val U)).map
        ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R (a t))).app U).hom
  choose c hc using fun U ↦ (hu U).exists_right_inv
  let d : RingCat.sectionsSubring
      ((ringedLocalizationRingOfUniverses R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
    ⟨c, by
      intro U V g
      let ρ := (((ringedLocalizationRingOfUniverses R (a t)).obj ⋙
        forget₂ CommRingCat RingCat).map g).hom
      change ρ (c U) = c V
      apply (hu V).mul_left_cancel
      have hb : ρ (b.val U) = b.val V := b.property g
      calc
        b.val V * ρ (c U) = ρ (b.val U * c U) := by rw [← hb, map_mul]
        _ = 1 := by rw [hc, map_one]
        _ = b.val V * c V := (hc V).symm⟩
  exact IsUnit.of_mul_eq_one d (by ext U; exact hc U)

/-- The canonical A[1/t]-algebra structure of the localized ring sheaf.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization). -/
def scalarLocalizationCoefficientMapOfUniverses (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Localization.Away t →+* RingCat.sectionsSubring
      ((ringedLocalizationRingOfUniverses R (a t)).obj ⋙
        forget₂ CommRingCat RingCat) :=
  IsLocalization.Away.lift t
    (g := (scalarLocalizationSectionsMapOfUniverses
      (ringedLocalizationRingUnitOfUniverses R (a t))).comp a)
    (scalarLocalizationSections_isUnitOfUniverses A R a t)

end CoefficientActions

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Restrict a linear category along the canonical inverse coefficient-ring isomorphism.
This is used solely to write the raw localization as an E-linear category.
Source: Bhatt–Scholze 6.8.14(2)
(blueprint: lem-per-rational-continuous-coefficient-derived-localization). -/
@[instance_reducible]
def continuousCoefficientRestrictLinear
    {B : Type v} [CommRing B] {L : Type v} [CommRing L]
    (b : B →+* L) (D : Type uC) [Category.{vC} D] [Preadditive D] [Linear L D] :
    Linear B D :=
  { homModule := fun X Y ↦ Module.compHom (X ⟶ Y) b
    smul_comp := fun X Y Z c f g ↦ Linear.smul_comp X Y Z (b c) f g
    comp_smul := fun X Y Z f c g ↦ Linear.comp_smul X Y Z f (b c) g }

namespace ScalarLocalization

private noncomputable def continuousRationalComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem continuousRawIsLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (localization R C p).IsLocalization (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := continuousRationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, localization, continuousRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

set_option linter.unusedVariables false in
private theorem continuousRawTriangulation
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ∃ z : HasZeroObject (ScalarLocalization R C p),
      (fun [zeroInst : HasZeroObject (ScalarLocalization R C p)] ↦
        ∃ s : HasShift (ScalarLocalization R C p) ℤ,
          (fun [shiftInst : HasShift (ScalarLocalization R C p) ℤ] ↦
            (∀ n : ℤ, shiftFunctor (ScalarLocalization R C p) n =
                map R C p (shiftFunctor C n)) ∧
            ∃ a : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive,
              (fun [addInst : ∀ n : ℤ,
                  (shiftFunctor (ScalarLocalization R C p) n).Additive] ↦
                ∃ q : (localization R C p).CommShift ℤ,
                  (fun [commInst : (localization R C p).CommShift ℤ] ↦
                    (∀ X : C,
                      HEq (((localization R C p).commShiftIso (1 : ℤ)).hom.app X)
                        (𝟙 ((localization R C p).obj ((shiftFunctor C (1 : ℤ)).obj X)))) ∧
                    ∃ t : Pretriangulated (ScalarLocalization R C p),
                      (fun [triInst : Pretriangulated (ScalarLocalization R C p)] ↦
                        IsTriangulated (ScalarLocalization R C p) ∧
                        (localization R C p).IsTriangulated ∧
                        ∀ T : Triangle (ScalarLocalization R C p),
                          T ∈ distTriang (ScalarLocalization R C p) ↔
                            ∃ T' : Triangle C, T' ∈ distTriang C ∧
                              Nonempty (T ≅ (localization R C p).mapTriangle.obj T'))
                        (triInst := t)) (commInst := q)) (addInst := a)) (shiftInst := s))
        (zeroInst := z) := by
  classical
  let M := Submonoid.powers p
  let Q := localization R C p
  have : Q.IsLocalization (Rationalization.W M C) := continuousRawIsLocalization R C p
  let z : HasZeroObject (ScalarLocalization R C p) := Q.hasZeroObject_of_additive
  refine ⟨z, ?_⟩
  have : ((Functor.whiskeringLeft C (ScalarLocalization R C p)
      (ScalarLocalization R C p)).obj Q).Full :=
    Localization.full_whiskeringLeft Q (Rationalization.W M C) _
  have : ((Functor.whiskeringLeft C (ScalarLocalization R C p)
      (ScalarLocalization R C p)).obj Q).Faithful :=
    Localization.faithful_whiskeringLeft Q (Rationalization.W M C) _
  let s' : ℤ → ScalarLocalization R C p ⥤ ScalarLocalization R C p :=
    fun n ↦ map R C p (shiftFunctor C n)
  let i : ∀ n : ℤ, Q ⋙ s' n ≅ shiftFunctor C n ⋙ Q :=
    fun n ↦ NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, s', localization, map, mapHom]
      simp)
  let s : HasShift (ScalarLocalization R C p) ℤ := HasShift.induced Q ℤ s' i
  refine ⟨s, ?_⟩
  refine ⟨fun _ ↦ rfl, ?_⟩
  let a : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive :=
    fun n ↦ inferInstanceAs ((map R C p (shiftFunctor C n)).Additive)
  refine ⟨a, ?_⟩
  let q : Q.CommShift ℤ := Functor.CommShift.ofInduced Q ℤ s' i
  refine ⟨q, ?_⟩
  refine ⟨fun X ↦ HEq.rfl, ?_⟩
  let t := Triangulated.Localization.pretriangulated Q (Rationalization.W M C)
  refine ⟨t, ?_⟩
  have : Q.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor Q (Rationalization.W M C)
  refine ⟨Triangulated.Localization.isTriangulated Q (Rationalization.W M C),
    inferInstance, ?_⟩
  intro T
  change (∃ T', ∃ _ : T ≅ Q.mapTriangle.obj T', T' ∈ distTriang C) ↔ _
  constructor
  · rintro ⟨T', e, hT'⟩
    exact ⟨T', hT', ⟨e⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    exact ⟨T', e, hT'⟩

end ScalarLocalization

section FractionFunctor

variable {A B : Type v} [CommRing A] [CommRing B]
  {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
  [Linear A D] [Linear B D'] (t : A) (φ : Localization.Away t →+* B)
  (F : D ⥤ D') [F.Additive]
  (hF : ∀ (X Y : D) (r : A) (f : X ⟶ Y),
    F.map (r • f) = φ (algebraMap A (Localization.Away t) r) • F.map f)

private def continuousFractionHom (X Y : D) :
    (Localization.Away t ⊗[A] (X ⟶ Y)) →+ (F.obj X ⟶ F.obj Y) := by
  let β : Localization.Away t →+ (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
    { toFun := fun b ↦
        { toFun := fun f ↦ φ b • F.map f
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [add_smul] }
  apply TensorProduct.liftAddHom β
  intro r b f
  dsimp [β]
  rw [Algebra.smul_def, map_mul, hF, smul_smul, mul_comm]

private theorem continuousFractionHom_tmul (X Y : D)
    (b : Localization.Away t) (f : X ⟶ Y) :
    continuousFractionHom t φ F hF X Y (b ⊗ₜ[A] f) = φ b • F.map f := by
  rfl

private def continuousFractionFunctor : ScalarLocalization A D t ⥤ D' where
  obj X := F.obj X.obj
  map {X Y} f := continuousFractionHom t φ F hF X.obj Y.obj f
  map_id X := by
    change continuousFractionHom t φ F hF _ _ (1 ⊗ₜ[A] 𝟙 X.obj) = _
    rw [continuousFractionHom_tmul, map_one, one_smul, F.map_id]
  map_comp {X Y Z} f g := by
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        change continuousFractionHom t φ F hF _ _
          (ScalarLocalization.composition A D t _ _ _ (b ⊗ₜ[A] g) (a ⊗ₜ[A] f)) = _
        simp only [ScalarLocalization.composition_tmul, continuousFractionHom_tmul,
          F.map_comp, map_mul, Linear.smul_comp, Linear.comp_smul, smul_smul]
      | add f f' hf hf' =>
        rw [Preadditive.add_comp X Y Z f f' (b ⊗ₜ[A] g)]
        simp only [map_add, hf, hf', Preadditive.add_comp]
    | add g g' hg hg' =>
      rw [Preadditive.comp_add X Y Z f g g']
      simp only [map_add, hg, hg', Preadditive.comp_add]

private theorem continuousFractionFunctor_additive :
    (continuousFractionFunctor t φ F hF).Additive where
  map_add := (continuousFractionHom t φ F hF _ _).map_add _ _

private def continuousFractionFactors :
    ScalarLocalization.localization A D t ⋙ continuousFractionFunctor t φ F hF ≅ F :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (by
    intro X Y f
    change continuousFractionHom t φ F hF X Y (1 ⊗ₜ[A] f) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp only [continuousFractionHom_tmul, map_one, one_smul, Category.comp_id,
      Category.id_comp])

private theorem continuousFractionFunctor_linear
    (e : Localization.Away t ≃+* B)
    (hF : ∀ (X Y : D) (r : A) (f : X ⟶ Y),
      F.map (r • f) = e (algebraMap A (Localization.Away t) r) • F.map f) :
    letI := continuousCoefficientRestrictLinear e.symm.toRingHom (ScalarLocalization A D t)
    (continuousFractionFunctor t e.toRingHom F hF).Linear B := by
  let := continuousCoefficientRestrictLinear e.symm.toRingHom (ScalarLocalization A D t)
  constructor
  intro X Y f b
  change continuousFractionHom t e.toRingHom F hF X.obj Y.obj (e.symm b • f) =
    b • continuousFractionHom t e.toRingHom F hF X.obj Y.obj f
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    change continuousFractionHom t e.toRingHom F hF _ _ ((e.symm b * a) ⊗ₜ[A] f) = _
    simp only [continuousFractionHom_tmul, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, map_mul, e.apply_symm_apply, mul_smul]
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]

include hF in
private theorem continuousFractionRelation
    (X Y : D) (f g : X ⟶ Y) (n m k : ℕ)
    (h : t ^ k • (t ^ m • f - t ^ n • g) = 0) :
    φ ((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • F.map f =
      φ ((IsLocalization.Away.invSelf t : Localization.Away t) ^ m) • F.map g := by
  let c := φ (algebraMap A (Localization.Away t) t)
  let i := φ (IsLocalization.Away.invSelf t : Localization.Away t)
  have hi : c * i = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hci : IsUnit c := IsUnit.of_mul_eq_one i hi
  have hh := congrArg (fun f : X ⟶ Y ↦ F.map f) h
  simp only [hF, F.map_sub, F.map_zero, map_pow] at hh
  have hcross : c ^ m • F.map f = c ^ n • F.map g := by
    apply sub_eq_zero.mp
    apply (hci.pow k).smul_eq_zero.mp
    simpa only [smul_zero] using hh
  have hh' := congrArg (fun z : F.obj X ⟶ F.obj Y ↦ i ^ (n + m) • z) hcross
  have hn : i ^ (n + m) * c ^ m = i ^ n := by
    rw [pow_add, mul_assoc, ← mul_pow, mul_comm i c, hi, one_pow, mul_one]
  have hm : i ^ (n + m) * c ^ n = i ^ m := by
    rw [add_comm n m, pow_add, mul_assoc, ← mul_pow, mul_comm i c, hi, one_pow, mul_one]
  simpa only [smul_smul, hn, hm, map_pow] using hh'

end FractionFunctor

private theorem continuousIsoInvHEq {D : Type*} [Category D] {X Y : D}
    (e : X ≅ Y) (h : Y = X) (he : HEq e.hom (𝟙 X)) : HEq e.inv (𝟙 X) := by
  subst Y
  apply heq_of_eq
  have hh := eq_of_heq he
  calc
    e.inv = e.inv ≫ e.hom := by rw [hh, Category.comp_id]
    _ = 𝟙 X := e.inv_hom_id

private theorem continuousMapHEq {D D' : Type*} [Category D] [Category D']
    (F : D ⥤ D') {X Y X' Y' : D} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

private theorem continuousIdentityChain {D : Type*} [Category D]
    {X Y : D} (f : X ⟶ Y) : 𝟙 X ≫ 𝟙 X ≫ f ≫ 𝟙 Y = f := by simp

private theorem continuousTensorBalance
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (N : ModuleCat A) (a : A) (m : N) :
    (1 : S) ⊗ₜ[A] (a • m) = (algebraMap A S a * 1) ⊗ₜ[A] m := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]

private theorem continuousScalarConjugate {A : Type*} [CommRing A]
    {D : Type*} [Category D] [Preadditive D] [Linear A D]
    {X Y : D} (e : X ≅ Y) (r : A) :
    e.hom ≫ (r • 𝟙 Y) ≫ e.inv = r • 𝟙 X := by simp

set_option linter.unusedSectionVars false in
private theorem continuousSheafificationScalar
    (S : Sheaf J CommRingCat.{u})
    (Q : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat))
    (s : RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)) :
    let L := PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
    letI : Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
      SheafOfModules.homLinear S.obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).property
    L.map (PresheafOfModules.sectionsSMul Q s) = s • 𝟙 (L.obj Q) := by
  dsimp only
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  apply (adj.homEquiv Q (L.obj Q)).injective
  simp only [Adjunction.homEquiv_unit]
  erw [← adj.unit.naturality]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro z
  change (adj.unit.app Q).app U (s.val U • z) =
    s.val U • (adj.unit.app Q).app U z
  exact ((adj.unit.app Q).app U).hom.map_smul _ _

set_option linter.unusedSectionVars false in
private theorem continuousCoefficientRestriction
    (A B : Type v) [CommRing A] [CommRing B] (t : A)
    (eB : Localization.Away t ≃+* B) (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    ((scalarLocalizationCoefficientMapOfUniverses A R a t).comp eB.symm.toRingHom).comp
      (eB.toRingHom.comp (algebraMap A (Localization.Away t))) =
        (scalarLocalizationSectionsMapOfUniverses
          (ringedLocalizationRingUnitOfUniverses R (a t))).comp a := by
  apply RingHom.ext
  intro r
  change scalarLocalizationCoefficientMapOfUniverses A R a t
    (eB.symm (eB (algebraMap A (Localization.Away t) r))) = _
  exact (congrArg (scalarLocalizationCoefficientMapOfUniverses A R a t)
    (eB.symm_apply_apply (algebraMap A (Localization.Away t) r))).trans
      (IsLocalization.Away.lift_eq t _ r)

attribute [local irreducible] scalarLocalizationCoefficientMapOfUniverses

set_option linter.unusedSectionVars false in
private theorem continuousDerivedScalars
    (A B : Type v) [CommRing A] [CommRing B] (S : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (b : B →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (c : A →+* B) (hc : b.comp c = a)
    [HasDerivedCategory.{wS}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))] :
    letI := scalarLocalizationDerivedLinearOfUniverses A S a
    letI := scalarLocalizationDerivedLinearOfUniverses B S b
    ∀ (X Y : DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
      (f : X ⟶ Y) (r : A), r • f = c r • f := by
  let := scalarLocalizationCoefficientLinearOfUniverses A S a
  let := scalarLocalizationCoefficientLinearOfUniverses B S b
  let := scalarLocalizationDerivedLinearOfUniverses A S a
  let := scalarLocalizationDerivedLinearOfUniverses B S b
  intro X Y f r
  let D := DerivedCategory
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  have h : Linear.toCatCenter A D r = Linear.toCatCenter B D (c r) := by
    apply End.ext
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    intro K
    have hK : (r • 𝟙 K : K ⟶ K) = c r • 𝟙 K := by
      ext n U z
      change (a r).val U • z = (b (c r)).val U • z
      rw [← RingHom.comp_apply, hc]
    change r • 𝟙 (DerivedCategory.Q.obj K) = c r • 𝟙 (DerivedCategory.Q.obj K)
    simpa only [Functor.map_smul, Functor.map_id] using
      congrArg (fun g : K ⟶ K ↦ DerivedCategory.Q.map g) hK
  have hX := congrArg (fun z ↦ z.asHom.app X) h
  change r • 𝟙 X = c r • 𝟙 X at hX
  calc
    r • f = (r • 𝟙 X) ≫ f := by simp
    _ = (c r • 𝟙 X) ≫ f := congrArg (fun g ↦ g ≫ f) hX
    _ = c r • f := by simp

set_option maxHeartbeats 15000 in
-- Keep accidental unfolding out of the abstract localization proof.
/-- The balanced tensor extension of a semilinear exact functor is exact for the
induced raw shifts and the image-triangle triangulation. The shift comparison on
integral objects is the original one. This is the fraction-descent part of
Bhatt–Scholze 6.8.14(2), using Stacks 05R6. -/
private theorem continuousFractionTriangulated
    {A B : Type v} [CommRing A] [CommRing B] (t : A)
    (eB : Localization.Away t ≃+* B)
    {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [Linear A D] [Linear B D']
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor D n).Linear A]
    [HasZeroObject D'] [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [IsTriangulated D']
    (H : D ⥤ D') [H.Additive] [H.CommShift ℤ] [H.IsTriangulated]
    (hH : ∀ (X Y : D) (r : A) (f : X ⟶ Y),
      H.map (r • f) = eB (algebraMap A (Localization.Away t) r) • H.map f) :
  letI := continuousCoefficientRestrictLinear eB.symm.toRingHom
    (ScalarLocalization A D t)
  ∃ z : HasZeroObject (ScalarLocalization A D t),
    (fun [_zeroInst : HasZeroObject (ScalarLocalization A D t)] ↦
      ∃ s : HasShift (ScalarLocalization A D t) ℤ,
        (fun [_shiftInst : HasShift (ScalarLocalization A D t) ℤ] ↦
          (∀ n : ℤ, shiftFunctor (ScalarLocalization A D t) n =
            ScalarLocalization.map A D t
              (shiftFunctor D n)) ∧
          ∃ ad : ∀ n : ℤ,
              (shiftFunctor (ScalarLocalization A D t) n).Additive,
            (fun [_addInst : ∀ n : ℤ,
                (shiftFunctor (ScalarLocalization A D t) n).Additive] ↦
              ∃ q : (ScalarLocalization.localization A D t).CommShift ℤ,
                (fun [_commQ :
                    (ScalarLocalization.localization A
                      D t).CommShift ℤ] ↦
                  (∀ K : D, HEq
                    ((Functor.commShiftIso
                      (ScalarLocalization.localization A D t)
                      (1 : ℤ)).hom.app K)
                    (𝟙 ((ScalarLocalization.localization A D t).obj
                      ((shiftFunctor D (1 : ℤ)).obj K)))) ∧
                  ∃ tr : Pretriangulated (ScalarLocalization A D t),
                    (fun [_triInst :
                        Pretriangulated (ScalarLocalization A D t)] ↦
                      IsTriangulated (ScalarLocalization A D t) ∧
                      Functor.IsTriangulated
                        (ScalarLocalization.localization A D t) ∧
                      (∀ U : Triangle (ScalarLocalization A D t),
                        U ∈ distTriang _ ↔ ∃ V : Triangle D,
                          V ∈ distTriang _ ∧ Nonempty (U ≅
                            (Functor.mapTriangle
                              (ScalarLocalization.localization A
                                D t)).obj V)) ∧
                      ∃ G : ScalarLocalization A D t ⥤
                          D',
                        ∃ hobj : ∀ K, G.obj K = H.obj K.obj,
                          G.Additive ∧ G.Linear B ∧
                          (∀ (K L : D) (f : K ⟶ L)
                              (b : Localization.Away t),
                            G.map (b ⊗ₜ[A] f) = eqToHom (hobj ⟨K⟩) ≫
                              (eB b • H.map f) ≫ eqToHom (hobj ⟨L⟩).symm) ∧
                          (∀ (K L : D) (f g : K ⟶ L) (n m k : ℕ),
                            t ^ k • (t ^ m • f - t ^ n • g) = 0 →
                            eB ((IsLocalization.Away.invSelf t :
                                Localization.Away t) ^ n) •
                                H.map f =
                              eB ((IsLocalization.Away.invSelf t :
                                Localization.Away t) ^ m) •
                                H.map g) ∧
                          Nonempty (ScalarLocalization.localization A
                            D t
                            ⋙ G ≅ H) ∧
                          ∃ sG : G.CommShift ℤ,
                            (fun [_commG : G.CommShift ℤ] ↦ G.IsTriangulated ∧
                              (∀ K : D, HEq
                                ((G.commShiftIso (1 : ℤ)).hom.app
                                  ((ScalarLocalization.localization A
                                    D t).obj K))
                                (((H).commShiftIso (1 : ℤ)).hom.app K)))
                              (_commG := sG)) (_triInst := tr)) (_commQ := q))
              (_addInst := ad)) (_shiftInst := s)) (_zeroInst := z) := by
  classical
  dsimp only
  let := continuousCoefficientRestrictLinear eB.symm.toRingHom
    (ScalarLocalization A D t)
  obtain ⟨z, s, hs, ad, q, hq, tr, htri, hQtri, hdist⟩ :=
    ScalarLocalization.continuousRawTriangulation A D t
  let := z
  let := s
  let := ad
  let := q
  let := tr
  have := htri
  have := hQtri
  let Q := ScalarLocalization.localization A D t
  let G := continuousFractionFunctor t eB.toRingHom H hH
  have : G.Additive := continuousFractionFunctor_additive t eB.toRingHom H hH
  have : G.Linear B := continuousFractionFunctor_linear t H eB hH
  let fac : Q ⋙ G ≅ H := continuousFractionFactors t eB.toRingHom H hH
  have : Q.IsLocalization (Rationalization.W (Submonoid.powers t) D) :=
    ScalarLocalization.continuousRawIsLocalization A D t
  let : Localization.Lifting Q (Rationalization.W (Submonoid.powers t) D)
      H G := ⟨fac⟩
  let cs : G.CommShift ℤ := Functor.commShiftOfLocalization Q
    (Rationalization.W (Submonoid.powers t) D) ℤ H G
  let := cs
  have : NatTrans.CommShift fac.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q
      (Rationalization.W (Submonoid.powers t) D) ℤ H G
  have : G.IsTriangulated := by
    constructor
    intro Δ hΔ
    obtain ⟨Δ₀, hΔ₀, ⟨i⟩⟩ := (hdist Δ).1 hΔ
    have : (Q ⋙ G).IsTriangulated := (Functor.isTriangulated_iff_of_iso fac).2 inferInstance
    exact isomorphic_distinguished _ ((Q ⋙ G).map_distinguished Δ₀ hΔ₀) _
      (G.mapTriangle.mapIso i ≪≫ (Functor.mapTriangleCompIso Q G).symm.app Δ₀)
  refine ⟨z, s, hs, ad, q, hq, tr, htri, hQtri, hdist, G,
    (fun _ ↦ rfl), inferInstance, inferInstance, ?_, ?_, ⟨fac⟩, cs, inferInstance, ?_⟩
  · intro K L f b
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact continuousFractionHom_tmul t eB.toRingHom H hH K L b f
  · intro K L f g n m k h
    exact continuousFractionRelation t eB.toRingHom H hH K L f g n m k h
  · intro K
    change HEq ((G.commShiftIso (1 : ℤ)).hom.app (Q.obj K)) _
    rw [Functor.commShiftOfLocalization_iso_hom_app Q
      (Rationalization.W (Submonoid.powers t) D) H G]
    have eh (X : D) :
        (Localization.Lifting.iso Q
          (Rationalization.W (Submonoid.powers t) D) H G).hom.app X =
            𝟙 (H.obj X) := rfl
    have ei (X : D) :
        (Localization.Lifting.iso Q
          (Rationalization.W (Submonoid.powers t) D) H G).inv.app X =
            𝟙 (H.obj X) := rfl
    rw [eh, ei]
    simp only [Functor.map_id]
    have hc : (shiftFunctor (ScalarLocalization A D t) (1 : ℤ)).obj
        (Q.obj K) = Q.obj ((shiftFunctor D (1 : ℤ)).obj K) :=
      Functor.congr_obj (hs 1) (Q.obj K)
    have hi := continuousIsoInvHEq ((Q.commShiftIso (1 : ℤ)).app K) hc (hq K)
    have him := (continuousMapHEq G hc rfl hi).trans (heq_of_eq (G.map_id _))
    exact (heq_comp (congrArg G.obj hc) rfl rfl him (HEq.rfl)).trans
      (heq_of_eq (continuousIdentityChain ((H.commShiftIso (1 : ℤ)).hom.app K)))

/-- The complete assertion of exact continuous scalar localization, including the
canonical derived comparison, all cohomology degrees, and raw fraction descent.
Source: Bhatt–Scholze 6.8.14(2), Stacks 015F, 010N and 05R6
(blueprint: lem-per-rational-continuous-coefficient-derived-localization)
The instance bindings in this definition install only the specified section actions;
they impose no additional linearity hypothesis. -/
def ContinuousScalarLocalizationAssertions
    (A : Type v) [CommRing A] (t : A) (B : Type v) [CommRing B]
    (eB : Localization.Away t ≃+* B) (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))]
    (d : SheafOfModules.DerivedChangeOfRingsCochainModel
      (ringedLocalizationRingUnitOfUniverses R (a t))) : Prop :=
  let S := ringedLocalizationRingOfUniverses R (a t)
  let aS := (scalarLocalizationSectionsMapOfUniverses
    (ringedLocalizationRingUnitOfUniverses R (a t))).comp a
  let MR := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let MS := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  letI := scalarLocalizationCoefficientLinearOfUniverses A R a
  letI := scalarLocalizationCoefficientLinearOfUniverses A S aS
  letI := scalarLocalizationDerivedLinearOfUniverses A R a
  letI := scalarLocalizationDerivedLinearOfUniverses A S aS
  letI := scalarLocalizationDerivedLinearOfUniverses B S
    ((scalarLocalizationCoefficientMapOfUniverses A R a t).comp eB.symm.toRingHom)
  ∃ hl : PreservesFiniteLimits d.E, ∃ hc : PreservesFiniteColimits d.E,
    (fun [_limInst : PreservesFiniteLimits d.E] [_colimInst : PreservesFiniteColimits d.E] ↦
      d.E.Linear A ∧
      ∃ sF : d.T.CommShift ℤ,
        (fun [_shiftF : d.T.CommShift ℤ] ↦
          d.T.IsTriangulated ∧ d.T.Linear A ∧
          ∃ e : d.T ≅ d.E.mapDerivedCategory,
            NatTrans.CommShift e.hom ℤ ∧
            (∀ K : CochainComplex MR ℤ,
              e.hom.app (DerivedCategory.Q.obj K) ≫
                d.E.mapDerivedCategoryFactors.hom.app K = d.ε.app K) ∧
            (∀ (P K : CochainComplex MR ℤ) (p : P ⟶ K),
              CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso p →
              d.T.map (DerivedCategory.Q.map p) ≫
                e.hom.app (DerivedCategory.Q.obj K) ≫
                  d.E.mapDerivedCategoryFactors.hom.app K =
                d.ε.app P ≫ DerivedCategory.Q.map
                  ((d.E.mapHomologicalComplex (.up ℤ)).map p)) ∧
            (∃ e0 : DerivedCategory.singleFunctor MR 0 ⋙ d.T ≅
                d.E ⋙ DerivedCategory.singleFunctor MS 0,
              e0 = Functor.isoWhiskerLeft (DerivedCategory.singleFunctor MR 0) e ≪≫
                d.E.mapDerivedCategorySingleFunctor 0) ∧
            (∃ h : ∀ r : ℤ, d.T ⋙ DerivedCategory.homologyFunctor MS r ≅
                DerivedCategory.homologyFunctor MR r ⋙ d.E,
              ∀ r : ℤ, h r =
                Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor MS r) ≪≫
                  (d.E.mapDerivedCategoryHomologyFunctorIso r).symm) ∧
            (∀ (K : DerivedCategory MR) (I : Set ℤ),
              (∀ r ∈ I, IsZero ((DerivedCategory.homologyFunctor MR r).obj K)) →
              ∀ r ∈ I, IsZero ((DerivedCategory.homologyFunctor MS r).obj (d.T.obj K))) ∧
            (∀ (P : ObjectProperty (DerivedCategory MR)) [P.IsTriangulated],
              letI := continuousCoefficientRestrictLinear eB.symm.toRingHom
                (ScalarLocalization A P.FullSubcategory t)
              ∃ z : HasZeroObject (ScalarLocalization A P.FullSubcategory t),
                (fun [_zeroInst : HasZeroObject (ScalarLocalization A P.FullSubcategory t)] ↦
                  ∃ s : HasShift (ScalarLocalization A P.FullSubcategory t) ℤ,
                    (fun [_shiftInst : HasShift (ScalarLocalization A P.FullSubcategory t) ℤ] ↦
                      (∀ n : ℤ, shiftFunctor (ScalarLocalization A P.FullSubcategory t) n =
                        ScalarLocalization.map A P.FullSubcategory t
                          (shiftFunctor P.FullSubcategory n)) ∧
                      ∃ ad : ∀ n : ℤ,
                          (shiftFunctor (ScalarLocalization A P.FullSubcategory t) n).Additive,
                        (fun [_addInst : ∀ n : ℤ,
                            (shiftFunctor (ScalarLocalization A P.FullSubcategory t) n).Additive] ↦
                          ∃ q : (ScalarLocalization.localization A P.FullSubcategory t).CommShift ℤ,
                            (fun [_commQ :
                                (ScalarLocalization.localization A
                                  P.FullSubcategory t).CommShift ℤ] ↦
                              (∀ K : P.FullSubcategory, HEq
                                ((Functor.commShiftIso
                                  (ScalarLocalization.localization A P.FullSubcategory t)
                                  (1 : ℤ)).hom.app K)
                                (𝟙 ((ScalarLocalization.localization A P.FullSubcategory t).obj
                                  ((shiftFunctor P.FullSubcategory (1 : ℤ)).obj K)))) ∧
                              ∃ tr : Pretriangulated (ScalarLocalization A P.FullSubcategory t),
                                (fun [_triInst :
                                    Pretriangulated (ScalarLocalization A P.FullSubcategory t)] ↦
                                  IsTriangulated (ScalarLocalization A P.FullSubcategory t) ∧
                                  Functor.IsTriangulated
                                    (ScalarLocalization.localization A P.FullSubcategory t) ∧
                                  (∀ U : Triangle (ScalarLocalization A P.FullSubcategory t),
                                    U ∈ distTriang _ ↔ ∃ V : Triangle P.FullSubcategory,
                                      V ∈ distTriang _ ∧ Nonempty (U ≅
                                        (Functor.mapTriangle
                                          (ScalarLocalization.localization A
                                            P.FullSubcategory t)).obj V)) ∧
                                  ∃ G : ScalarLocalization A P.FullSubcategory t ⥤
                                      DerivedCategory MS,
                                    ∃ hobj : ∀ K, G.obj K = d.T.obj (P.ι.obj K.obj),
                                      G.Additive ∧ G.Linear B ∧
                                      (∀ (K L : P.FullSubcategory) (f : K ⟶ L)
                                          (b : Localization.Away t),
                                        G.map (b ⊗ₜ[A] f) = eqToHom (hobj ⟨K⟩) ≫
                                          (eB b • d.T.map (P.ι.map f)) ≫ eqToHom (hobj ⟨L⟩).symm) ∧
                                      (∀ (K L : P.FullSubcategory) (f g : K ⟶ L) (n m k : ℕ),
                                        t ^ k • (t ^ m • f - t ^ n • g) = 0 →
                                        eB ((IsLocalization.Away.invSelf t :
                                            Localization.Away t) ^ n) •
                                            d.T.map (P.ι.map f) =
                                          eB ((IsLocalization.Away.invSelf t :
                                            Localization.Away t) ^ m) •
                                            d.T.map (P.ι.map g)) ∧
                                      Nonempty (ScalarLocalization.localization A
                                        P.FullSubcategory t
                                        ⋙ G ≅ P.ι ⋙ d.T) ∧
                                      ∃ sG : G.CommShift ℤ,
                                        (fun [_commG : G.CommShift ℤ] ↦ G.IsTriangulated ∧
                                          (∀ K : P.FullSubcategory, HEq
                                            ((G.commShiftIso (1 : ℤ)).hom.app
                                              ((ScalarLocalization.localization A
                                                P.FullSubcategory t).obj K))
                                            (((P.ι ⋙ d.T).commShiftIso (1 : ℤ)).hom.app K)))
                                          (_commG := sG)) (_triInst := tr)) (_commQ := q))
                          (_addInst := ad)) (_shiftInst := s)) (_zeroInst := z))) (_shiftF := sF))
      (_limInst := hl) (_colimInst := hc)

private theorem continuousCoefficientLocalization
    (A B : Type v) [CommRing A] [CommRing B] (t : A)
    (eB : Localization.Away t ≃+* B) (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))]
    (d : SheafOfModules.DerivedChangeOfRingsCochainModel
      (ringedLocalizationRingUnitOfUniverses R (a t))) :
    ContinuousScalarLocalizationAssertions A t B eB R a d := by
  classical
  let S := ringedLocalizationRingOfUniverses R (a t)
  let α := ringedLocalizationRingUnitOfUniverses R (a t)
  let aS := (scalarLocalizationSectionsMapOfUniverses α).comp a
  let MR := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let MS := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  let := scalarLocalizationCoefficientLinearOfUniverses A R a
  let := scalarLocalizationCoefficientLinearOfUniverses A S aS
  let := scalarLocalizationDerivedLinearOfUniverses A R a
  let := scalarLocalizationDerivedLinearOfUniverses A S aS
  let := scalarLocalizationDerivedLinearOfUniverses B S
    ((scalarLocalizationCoefficientMapOfUniverses A R a t).comp eB.symm.toRingHom)
  obtain ⟨F, hobj, hmap, _, _, _, hF⟩ := scalarLocalization_sheaf_exact J R (a t)
  have hdF : d.E = F := by
    refine Functor.ext (fun M ↦ (d.obj_eq M).trans (hobj M).symm) ?_
    intro M N f
    simp only [d.map_eq, hmap, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl
  obtain ⟨_, hl, hc⟩ := hF d.E ⟨eqToIso hdF⟩
  let := hl
  let := hc
  have hlin : d.E.Linear A := by
    rw [Functor.linear_iff]
    intro M r
    rw [d.map_eq]
    have hs : SheafOfModules.changeOfRingsHom α M (r • 𝟙 M) =
        r • 𝟙 (SheafOfModules.changeOfRings α M) := by
      let Q := SheafOfModules.changeOfRingsPresheaf α M
      have hraw : (show Q ⟶ Q from
          { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map
              ((r • 𝟙 M).val.app U)
            naturality := SheafOfModules.changeOfRingsHom_naturality α M (r • 𝟙 M) }) =
          PresheafOfModules.sectionsSMul Q (aS r) := by
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        let := (α.hom.app U).hom.toAlgebra
        change (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U] ((a r).val U • m) =
          ((α.hom.app U).hom ((a r).val U) * 1) ⊗ₜ[R.obj.obj U] m
        exact continuousTensorBalance (A := R.obj.obj U) (S := S.obj.obj U)
          (M.val.obj U) ((a r).val U) m
      exact (congrArg (fun f : Q ⟶ Q ↦
        (PresheafOfModules.sheafification (R :=
          (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).map f) hraw).trans
        (continuousSheafificationScalar S Q (aS r))
    exact (congrArg (fun f ↦ eqToHom (d.obj_eq M) ≫ f ≫
      eqToHom (d.obj_eq M).symm) hs).trans
        (continuousScalarConjugate (eqToIso (d.obj_eq M)) r)
  let := hlin
  have : d.T.IsLeftDerivedFunctor d.ε (HomologicalComplex.quasiIso MR (.up ℤ)) :=
    d.universal
  have : d.E.mapDerivedCategory.IsLeftDerivedFunctor d.E.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso MR (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  let e : d.T ≅ d.E.mapDerivedCategory :=
    Functor.leftDerivedUnique d.E.mapDerivedCategory d.T d.ε
      d.E.mapDerivedCategoryFactors.hom (HomologicalComplex.quasiIso MR (.up ℤ))
  let : d.T.CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  have : NatTrans.CommShift e.hom ℤ := by
    have : NatTrans.CommShift e.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility e.symm ℤ
    exact NatTrans.CommShift.of_iso_inv e.symm ℤ
  have : d.T.IsTriangulated := Functor.isTriangulated_of_iso e.symm
  have : d.T.Linear A := Functor.linear_of_iso A e.symm
  have he (K : CochainComplex MR ℤ) :
      e.hom.app (DerivedCategory.Q.obj K) ≫ d.E.mapDerivedCategoryFactors.hom.app K =
        d.ε.app K := by
    simp [e, Functor.leftDerivedNatIso]
  dsimp only [ContinuousScalarLocalizationAssertions]
  refine ⟨hl, hc, hlin, inferInstance, inferInstance, inferInstance, e,
    inferInstance, he, ?_, ?_, ?_, ?_, ?_⟩
  · intro P K p _ _
    exact (congrArg (fun f ↦ d.T.map (DerivedCategory.Q.map p) ≫ f) (he K)).trans
      (d.ε.naturality p)
  · exact ⟨Functor.isoWhiskerLeft (DerivedCategory.singleFunctor MR 0) e ≪≫
      d.E.mapDerivedCategorySingleFunctor 0, rfl⟩
  · exact ⟨fun r ↦ Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor MS r) ≪≫
      (d.E.mapDerivedCategoryHomologyFunctorIso r).symm, fun _ ↦ rfl⟩
  · intro K I hK r hr
    let h := Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor MS r) ≪≫
      (d.E.mapDerivedCategoryHomologyFunctorIso r).symm
    exact (d.E.map_isZero (hK r hr)).of_iso (h.app K)
  · intro P hP
    let b := (scalarLocalizationCoefficientMapOfUniverses A R a t).comp eB.symm.toRingHom
    have hb : b.comp (eB.toRingHom.comp (algebraMap A (Localization.Away t))) = aS :=
      continuousCoefficientRestriction A B t eB R a
    have hscalar := continuousDerivedScalars A B S aS b
      (eB.toRingHom.comp (algebraMap A (Localization.Away t))) hb
    let H := P.ι ⋙ d.T
    have hH : ∀ (X Y : P.FullSubcategory) (r : A) (f : X ⟶ Y),
        H.map (r • f) = eB (algebraMap A (Localization.Away t) r) • H.map f := by
      intro X Y r f
      change d.T.map (r • f.hom) = _
      exact (d.T.map_smul r f.hom).trans (hscalar _ _ (H.map f) r)
    exact continuousFractionTriangulated t eB H hH

end CategoryTheory
