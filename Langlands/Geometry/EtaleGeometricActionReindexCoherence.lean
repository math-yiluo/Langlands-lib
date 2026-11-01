import Langlands.Geometry.EtaleGeometricActionReindex

/-! # Coherence of geometric action reindexing with coefficient-natural recovery -/

noncomputable section

universe u v w v' w' t t' uC vC uA vA uA' vA' uB vB wS wR

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Categorical

variable {J : Type v} [Category.{w} J] {K : Type v'} [Category.{w'} K]
variable {G : Type t} [Monoid G] {H : Type t'} [Monoid H]
variable (F : K ⥤ J) (φ : H →* G)
variable {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
variable {A : Type uA} [Category.{vA} A]
variable {A' : Type uA'} [Category.{vA'} A']

/-- Apply a functor to the underlying objects, actions and equivariant maps
of an action-valued diagram. -/
def actionDiagramMapFunctor (J : Type v) [Category.{w} J]
    (G : Type t) [Monoid G] (L : C ⥤ B) :
    (J ⥤ Action C G) ⥤ (J ⥤ Action B G) :=
  (Functor.whiskeringRight J (Action C G) (Action B G)).obj (L.mapAction G)

/-- Applying a functor to algebraic actions commutes canonically with
level selection and group restriction. -/
def actionDiagramReindexMapIso (L : C ⥤ B) :
    actionDiagramReindexFunctor F φ C ⋙ actionDiagramMapFunctor K H L ≅
      actionDiagramMapFunctor J G L ⋙ actionDiagramReindexFunctor F φ B :=
  Iso.refl _

/-- The functor and reindex interchange has identity components. -/
@[simp] theorem actionDiagramReindexMapIso_app (L : C ⥤ B)
    (E : J ⥤ Action C G) :
    (actionDiagramReindexMapIso F φ L).app E =
      Iso.refl ((actionDiagramMapFunctor K H L).obj
        ((actionDiagramReindexFunctor F φ C).obj E)) := rfl

/-- Equality of natural isomorphisms is determined by all isomorphism components. -/
theorem naturalIso_ext_app {E E' : A ⥤ B} (α β : E ≅ E')
    (h : ∀ a, α.app a = β.app a) : α = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext a
  exact congrArg Iso.hom (h a)

/-- Postcomposition acts on the individual components of an isomorphism. -/
theorem isoWhiskerRight_app {E E' : A ⥤ B} (α : E ≅ E') (L : B ⥤ C) (a : A) :
    (Functor.isoWhiskerRight α L).app a = L.mapIso (α.app a) := rfl

/-- Precomposition selects the component at the chosen object. -/
theorem isoWhiskerLeft_app (L : A ⥤ B) {E E' : B ⥤ C} (α : E ≅ E') (a : A) :
    (Functor.isoWhiskerLeft L α).app a = α.app (L.obj a) := rfl

/-- Mapping an action-diagram isomorphism is postcomposition by the action functor. -/
theorem actionDiagramMapFunctor_mapIso (L : C ⥤ B)
    {E E' : J ⥤ Action C G} (α : E ≅ E') :
    (actionDiagramMapFunctor J G L).mapIso α =
      Functor.isoWhiskerRight α (L.mapAction G) := rfl

/-- Reindexing an isomorphism selects its levels and restricts its actions. -/
theorem actionDiagramReindexFunctor_mapIso {E E' : J ⥤ Action C G} (α : E ≅ E') :
    (actionDiagramReindexFunctor F φ C).mapIso α =
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight α (Action.res C φ)) := rfl

/-- Paste action reindexing, its canonical interchange with a functor,
and a coefficient-natural recovery comparison in abstract categories. -/
def actionDiagramReindexRecoveryIso (L : C ⥤ B) (r : A ⥤ A')
    (E : A ⥤ (J ⥤ Action C G)) (E' : A' ⥤ (K ⥤ Action C H))
    (E₀ : A ⥤ (J ⥤ Action B G))
    (η : r ⋙ E' ≅ E ⋙ actionDiagramReindexFunctor F φ C)
    (χ : E ⋙ actionDiagramMapFunctor J G L ≅ E₀) :
    r ⋙ (E' ⋙ actionDiagramMapFunctor K H L) ≅
      E₀ ⋙ actionDiagramReindexFunctor F φ B :=
  Functor.isoWhiskerRight η (actionDiagramMapFunctor K H L) ≪≫
    Functor.isoWhiskerLeft E (actionDiagramReindexMapIso F φ L) ≪≫
    Functor.isoWhiskerRight χ (actionDiagramReindexFunctor F φ B)

/-- The pasted comparison has the expected level-selected component. -/
theorem actionDiagramReindexRecoveryIso_app (L : C ⥤ B) (r : A ⥤ A')
    (E : A ⥤ (J ⥤ Action C G)) (E' : A' ⥤ (K ⥤ Action C H))
    (E₀ : A ⥤ (J ⥤ Action B G))
    (η : r ⋙ E' ≅ E ⋙ actionDiagramReindexFunctor F φ C)
    (χ : E ⋙ actionDiagramMapFunctor J G L ≅ E₀) (a : A) :
    (actionDiagramReindexRecoveryIso F φ L r E E' E₀ η χ).app a =
      Functor.isoWhiskerRight (η.app a) (L.mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight (χ.app a) (Action.res B φ)) := by
  simp only [actionDiagramReindexRecoveryIso, NatIso.trans_app,
    isoWhiskerRight_app, isoWhiskerLeft_app, actionDiagramReindexMapIso_app,
    actionDiagramMapFunctor_mapIso, actionDiagramReindexFunctor_mapIso]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.refl_hom]
  apply NatTrans.ext
  funext i
  apply Action.Hom.ext
  dsimp [actionDiagramMapFunctor, actionDiagramReindexFunctor]
  simp only [Category.id_comp]

end Categorical

namespace CoefficientDiagram

open EtaleDerivedSections

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] {K : Type v'} [Category.{w'} K]
variable {G : Type t} [Group G] {H : Type t'} [Group H]
variable {S : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ}
variable (F : K ⥤ J) (φ : H →* G)
variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf (S.obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance : ∀ x : K × SingleObj H, HasDerivedCategory.{wS}
    (ModuleSheaf (((F.prod (SingleObj.mapHom H G φ)) ⋙ S).obj x).unop R) :=
  fun x => inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf (S.obj ((F.prod (SingleObj.mapHom H G φ)).obj x)).unop R))

/-- The action-valued homology of reindexed actual derived sections. -/
def reindexedDerivedActionHomologyFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  reindexFunctor (F.prod (SingleObj.mapHom H G φ)) ⋙
    (derivedActionFunctor ⋙ actionDiagramMapFunctor K H
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q))

/-- The level-selected and group-restricted actual cohomology action functor. -/
def restrictedCohomologyActionFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  cohomologyActionFunctor q ⋙ actionDiagramReindexFunctor F φ (ModuleCat.{u} R)

/-- Reindex derived sections first, then recover their actual cohomology. -/
def reindexDerivedActionHomologyFirstIso (q : ℕ) :
    reindexedDerivedActionHomologyFunctor (R := R) (S := S) F φ q ≅
      restrictedCohomologyActionFunctor F φ q :=
  actionDiagramReindexRecoveryIso F φ
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q)
    (reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
    derivedActionFunctor derivedActionFunctor (cohomologyActionFunctor q)
    (reindexDerivedActionFunctorIso F φ) (derivedActionHomologyFunctorIso q)

/-- Recover cohomology at the reindexed coefficients, then compare its action diagram. -/
def reindexDerivedActionHomologyRecoveryIso (q : ℕ) :
    reindexedDerivedActionHomologyFunctor (R := R) (S := S) F φ q ≅
      restrictedCohomologyActionFunctor F φ q :=
  Functor.isoWhiskerLeft (reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      (derivedActionHomologyFunctorIso q) ≪≫
    reindexCohomologyActionFunctorIso F φ q

/-- The first coefficient-natural route recovers the specified object route. -/
theorem reindexDerivedActionHomologyFirstIso_app
    (D : CoefficientDiagram R S) (q : ℕ) :
    (reindexDerivedActionHomologyFirstIso F φ q).app D =
      Functor.isoWhiskerRight (reindexDerivedActionIso F φ D)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight (D.derivedActionHomologyIso q)
            (Action.res (ModuleCat.{u} R) φ)) := by
  unfold reindexDerivedActionHomologyFirstIso
  rw [actionDiagramReindexRecoveryIso_app, reindexDerivedActionFunctorIso_app]
  rfl

/-- The recovery-first coefficient route recovers its specified object route. -/
theorem reindexDerivedActionHomologyRecoveryIso_app
    (D : CoefficientDiagram R S) (q : ℕ) :
    (reindexDerivedActionHomologyRecoveryIso F φ q).app D =
      (reindex (F.prod (SingleObj.mapHom H G φ)) D).derivedActionHomologyIso q ≪≫
        reindexCohomologyActionIso F φ D q := by
  unfold reindexDerivedActionHomologyRecoveryIso
  rw [NatIso.trans_app, isoWhiskerLeft_app, reindexCohomologyActionFunctorIso_app]
  rfl

/-- Geometric level and group reindexing commutes with equivariant homology
recovery as an equality of natural isomorphisms on the coefficient category. -/
theorem reindexDerivedActionFunctorIso_homology (q : ℕ) :
    reindexDerivedActionHomologyFirstIso (R := R) (S := S) F φ q =
      reindexDerivedActionHomologyRecoveryIso F φ q := by
  apply naturalIso_ext_app
  intro D
  rw [reindexDerivedActionHomologyFirstIso_app, reindexDerivedActionHomologyRecoveryIso_app]
  exact reindexDerivedActionIso_homology F φ D q

/-- Level selection and group restriction of the actual section action functor. -/
def restrictedSectionsActionFunctor :
    CoefficientDiagram R S ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  sectionsActionFunctor ⋙ actionDiagramReindexFunctor F φ (ModuleCat.{u} R)

/-- Reindex derived sections before applying canonical degree-zero recovery. -/
def reindexDerivedActionZeroFirstIso :
    reindexedDerivedActionHomologyFunctor (R := R) (S := S) F φ 0 ≅
      restrictedSectionsActionFunctor F φ :=
  actionDiagramReindexRecoveryIso F φ
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0)
    (reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
    derivedActionFunctor derivedActionFunctor sectionsActionFunctor
    (reindexDerivedActionFunctorIso F φ) derivedActionZeroFunctorIso

/-- Recover actual sections at the reindexed coefficients before comparing actions. -/
def reindexDerivedActionZeroRecoveryIso :
    reindexedDerivedActionHomologyFunctor (R := R) (S := S) F φ 0 ≅
      restrictedSectionsActionFunctor F φ :=
  Functor.isoWhiskerLeft (reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      derivedActionZeroFunctorIso ≪≫
    reindexSectionsActionFunctorIso F φ

/-- The derived degree-zero first route has its specified canonical components. -/
theorem reindexDerivedActionZeroFirstIso_app (D : CoefficientDiagram R S) :
    (reindexDerivedActionZeroFirstIso F φ).app D =
      Functor.isoWhiskerRight (reindexDerivedActionIso F φ D)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction H) ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight D.derivedActionZeroIso
            (Action.res (ModuleCat.{u} R) φ)) := by
  unfold reindexDerivedActionZeroFirstIso
  rw [actionDiagramReindexRecoveryIso_app, reindexDerivedActionFunctorIso_app]
  rfl

/-- The derived degree-zero recovery route has its specified canonical components. -/
theorem reindexDerivedActionZeroRecoveryIso_app (D : CoefficientDiagram R S) :
    (reindexDerivedActionZeroRecoveryIso F φ).app D =
      (reindex (F.prod (SingleObj.mapHom H G φ)) D).derivedActionZeroIso ≪≫
        reindexSectionsActionIso F φ D := by
  unfold reindexDerivedActionZeroRecoveryIso
  rw [NatIso.trans_app, isoWhiskerLeft_app, reindexSectionsActionFunctorIso_app]
  rfl

/-- Canonical derived degree-zero recovery commutes with level and group
reindexing on the full coefficient category. -/
theorem reindexDerivedActionFunctorIso_zero :
    reindexDerivedActionZeroFirstIso (R := R) (S := S) F φ =
      reindexDerivedActionZeroRecoveryIso F φ := by
  apply naturalIso_ext_app
  intro D
  rw [reindexDerivedActionZeroFirstIso_app, reindexDerivedActionZeroRecoveryIso_app]
  exact reindexDerivedActionIso_zero F φ D

/-- Ordinary cohomology action diagrams of reindexed actual coefficients. -/
def reindexedCohomologyActionFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (K ⥤ Action (ModuleCat.{u} R) H) :=
  reindexFunctor (F.prod (SingleObj.mapHom H G φ)) ⋙ cohomologyActionFunctor q

/-- Compare reindexed ordinary degree-zero actions before recovering sections. -/
def reindexCohomologyActionZeroFirstIso :
    reindexedCohomologyActionFunctor (R := R) (S := S) F φ 0 ≅
      restrictedSectionsActionFunctor F φ :=
  reindexCohomologyActionFunctorIso F φ 0 ≪≫
    Functor.isoWhiskerRight cohomologyActionZeroFunctorIso
      (actionDiagramReindexFunctor F φ (ModuleCat.{u} R))

/-- Recover sections at reindexed coefficients before comparing section actions. -/
def reindexCohomologyActionZeroRecoveryIso :
    reindexedCohomologyActionFunctor (R := R) (S := S) F φ 0 ≅
      restrictedSectionsActionFunctor F φ :=
  Functor.isoWhiskerLeft (reindexFunctor (F.prod (SingleObj.mapHom H G φ)))
      cohomologyActionZeroFunctorIso ≪≫
    reindexSectionsActionFunctorIso F φ

/-- The ordinary degree-zero first route has its specified canonical components. -/
theorem reindexCohomologyActionZeroFirstIso_app (D : CoefficientDiagram R S) :
    (reindexCohomologyActionZeroFirstIso F φ).app D =
      reindexCohomologyActionIso F φ D 0 ≪≫
        Functor.isoWhiskerLeft F
          (Functor.isoWhiskerRight (cohomologyActionZeroFunctorIso.app D)
            (Action.res (ModuleCat.{u} R) φ)) := by
  unfold reindexCohomologyActionZeroFirstIso
  rw [NatIso.trans_app, reindexCohomologyActionFunctorIso_app,
    isoWhiskerRight_app, actionDiagramReindexFunctor_mapIso]

/-- The ordinary degree-zero recovery route has its specified canonical components. -/
theorem reindexCohomologyActionZeroRecoveryIso_app (D : CoefficientDiagram R S) :
    (reindexCohomologyActionZeroRecoveryIso F φ).app D =
      cohomologyActionZeroFunctorIso.app
        (reindex (F.prod (SingleObj.mapHom H G φ)) D) ≪≫
        reindexSectionsActionIso F φ D := by
  unfold reindexCohomologyActionZeroRecoveryIso
  rw [NatIso.trans_app, isoWhiskerLeft_app, reindexSectionsActionFunctorIso_app]
  rfl

/-- Ordinary degree-zero recovery commutes with simultaneous level and group
reindexing as an equality of coefficient-natural isomorphisms. -/
theorem reindexCohomologyActionFunctorIso_zero :
    reindexCohomologyActionZeroFirstIso (R := R) (S := S) F φ =
      reindexCohomologyActionZeroRecoveryIso F φ := by
  apply naturalIso_ext_app
  intro D
  rw [reindexCohomologyActionZeroFirstIso_app, reindexCohomologyActionZeroRecoveryIso_app]
  exact reindexCohomologyActionIso_zero F φ D

end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram
