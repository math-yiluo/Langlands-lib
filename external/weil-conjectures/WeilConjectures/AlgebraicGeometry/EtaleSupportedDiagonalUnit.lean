/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
public import WeilConjectures.CategoryTheory.AdjunctionUnitTransport
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The supported diagonal unit -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteTwistedPullback derivedTensorRight
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
/-- The right unitor on the constant complex. -/
def singleUnitor (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (ordinaryFiniteTensor A X).flip.obj (ordinaryFiniteUnit A X) ≅
      𝟭 (DerivedCategoryModule A X) :=
  derivedSingleUnitorNatIso (ModuleCat.{u + 1} A) X
/-- The constant-complex transport cancels before the right unitor. -/
theorem singleUnitor_cancel (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M V : DerivedCategoryModule A X) (t : V ⟶ constantComplex A X) :
    ((ordinaryFiniteTensor A X).obj M).map
        (t ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv) ≫
        (singleUnitor A X).hom.app M =
      ((ordinaryFiniteTensor A X).obj M).map t ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom := by
  exact derivedSingleUnitorNatIso_cancel (ModuleCat.{u + 1} A) X M V t

/-- Projection along the diagonal, using its first section identity. -/
def diagonalTensorMap (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFinitePullback A (pullback.fst f f) ⋙
        (ordinaryFiniteTensor A (pullback f f)).flip.obj
          ((ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X)) ⟶
      ordinaryFinitePushforward A (pullback.diagonal f) :=
  Functor.whiskerLeft (ordinaryFinitePullback A (pullback.fst f f))
      (ordinaryFiniteProjectionNatTrans A (pullback.diagonal f) (ordinaryFiniteUnit A X)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
          (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
            (pullback.diagonal f) (pullback.fst f f) (pullback.diagonal_fst f)).hom
          ((ordinaryFiniteTensor A X).flip.obj (ordinaryFiniteUnit A X)) ≫
        (singleUnitor A X).hom)
      (ordinaryFinitePushforward A (pullback.diagonal f))
theorem diagonalTensorMap_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] :
    IsIso (diagonalTensorMap A f) := by
  let i : X ⟶ pullback f f := pullback.diagonal f
  have : IsProper i := by dsimp [i]; infer_instance
  have h (M : DerivedCategoryModule A X) :
      IsIso ((ordinaryFiniteProjectionNatTrans A i (ordinaryFiniteUnit A X)).app
        ((ordinaryFinitePullback A (pullback.fst f f)).obj M)) := by
    change IsIso (CoordinateTrace.orderedProjectionIso A i
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)
      (ordinaryFiniteUnit A X)).hom
    infer_instance
  apply NatTrans.isIso_iff_isIso_app _ |>.2
  intro M
  change IsIso ((ordinaryFiniteProjectionNatTrans A i (ordinaryFiniteUnit A X)).app _ ≫ _)
  dsimp only [Functor.whiskerRight, NatTrans.comp_app]
  let := h M
  infer_instance
/-- The inverse projection along the diagonal. -/
def diagonalTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] :
    ordinaryFinitePullback A (pullback.fst f f) ⋙
        (ordinaryFiniteTensor A (pullback f f)).flip.obj
          ((ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X)) ≅
      ordinaryFinitePushforward A (pullback.diagonal f) :=
  have := diagonalTensorMap_isIso A f
  asIso (diagonalTensorMap A f)
/-- The diagonal tensor isomorphism is the explicit first-section projection composite. -/
theorem diagonalTensorIso_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (M : DerivedCategoryModule A X) :
    (diagonalTensorIso A f).app M =
      CoordinateTrace.orderedProjectionIso A (pullback.diagonal f)
        ((ordinaryFinitePullback A (pullback.fst f f)).obj M) (ordinaryFiniteUnit A X) ≪≫
      (ordinaryFinitePushforward A (pullback.diagonal f)).mapIso
        (((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
          ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
            (pullback.diagonal f) (pullback.fst f f) (pullback.diagonal_fst f)).app M)).app
          (ordinaryFiniteUnit A X) ≪≫ (singleUnitor A X).app M) := by
  apply Iso.ext
  rfl
/-- The second projection after diagonal pushforward is identity. -/
def diagonalPushSection (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (DerivedCategoryModule A X) ≅ ordinaryFinitePushforward A (pullback.diagonal f) ⋙
      ordinaryFinitePushforward A (pullback.snd f f) :=
  derivedSectionPushIso (ModuleCat.{u + 1} A) (pullback.diagonal f) (pullback.snd f f)
    (pullback.diagonal_snd f)
/-- The first projection after diagonal pushforward is identity. -/
def diagonalFirstPushSection (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (DerivedCategoryModule A X) ≅ ordinaryFinitePushforward A (pullback.diagonal f) ⋙
      ordinaryFinitePushforward A (pullback.fst f f) :=
  derivedSectionPushIso (ModuleCat.{u + 1} A) (pullback.diagonal f) (pullback.fst f f)
    (pullback.diagonal_fst f)
/-- Projection in the second coordinate. -/
def coordinateProjection (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X) :
    ordinaryFinitePullback A (pullback.fst f f) ⋙
        ordinaryFinitePushforward A (pullback.snd f f) ⋙
          (ordinaryFiniteTensor A X).flip.obj L ⟶
      ordinaryFinitePullback A (pullback.fst f f) ⋙
        (ordinaryFiniteTensor A (pullback f f)).flip.obj
          ((ordinaryFinitePullback A (pullback.snd f f)).obj L) ⋙
            ordinaryFinitePushforward A (pullback.snd f f) where
  app M := ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
    (pullback.snd f f)).app
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).app L
  naturality _M _M' g := NatTrans.congr_app
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (pullback.snd f f)).naturality
        ((ordinaryFinitePullback A (pullback.fst f f)).map g)) L
/-- Inverse second-coordinate projection and inverse proper exchange. -/
def diagonalComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A (pullback.fst f f) ⋙
        (ordinaryFiniteTensor A (pullback f f)).flip.obj
          ((ordinaryFinitePullback A (pullback.snd f f)).obj
            ((ordinaryFinitePullback A f).obj L))) ⋙
              ordinaryFinitePushforward A (pullback.snd f f) ≅
      ordinaryFinitePushforward A f ⋙ CoordinateTrace.H A f L := by
  have : IsIso (coordinateProjection A f ((ordinaryFinitePullback A f).obj L)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro M
    exact isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      A isAddTorsion_of_finite (pullback.snd f f)
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)
      ((ordinaryFinitePullback A f).obj L)
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f)
  exact (asIso (coordinateProjection A f ((ordinaryFinitePullback A f).obj L))).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f f).toCommSq)).symm
      ((ordinaryFiniteTensor A X).flip.obj ((ordinaryFinitePullback A f).obj L))
/-- The functor comparison has the prescribed coordinate-comparison components. -/
theorem diagonalComparison_hom_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (M : DerivedCategoryModule A X) :
    (diagonalComparison A f L).hom.app M = (CoordinateTrace.comparison A f L M).hom := by
  let : IsIso (coordinateProjection A f ((ordinaryFinitePullback A f).obj L)) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun N ↦
      isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
        A isAddTorsion_of_finite (pullback.snd f f)
        ((ordinaryFinitePullback A (pullback.fst f f)).obj N)
        ((ordinaryFinitePullback A f).obj L))
  change (inv (coordinateProjection A f ((ordinaryFinitePullback A f).obj L))).app M ≫
    _ = _
  rw [NatIso.isIso_inv_app]
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f)
  change _ ≫ ((ordinaryFiniteTensor A X).flip.obj
    ((ordinaryFinitePullback A f).obj L)).map
      ((inv (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f f).toCommSq)).app M) = _
  rw [NatIso.isIso_inv_app]
  rfl

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction

attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance] DerivedCategory.symmetricCategory'
attribute [local instance 20000] derivedBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory

/-- Form the unit composite in arbitrary categories, caching all whiskering structure. -/
def sectionTensorUnitComposite
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S T T' : C ⥤ E) (R : E ⥤ C) (H : C ⥤ D) (F : D ⥤ C)
    (a : 𝟭 C ≅ S ⋙ R) (q : T ≅ S) (d : T ⟶ T')
    (c : T' ⋙ R ≅ H ⋙ F) : 𝟭 C ⟶ H ⋙ F :=
  a.hom ≫ Functor.whiskerRight q.inv R ≫ Functor.whiskerRight d R ≫ c.hom

/-- Components of the abstract unit construction are its four indicated maps. -/
theorem sectionTensorUnitComposite_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S T T' : C ⥤ E) (R : E ⥤ C) (H : C ⥤ D) (F : D ⥤ C)
    (a : 𝟭 C ≅ S ⋙ R) (q : T ≅ S) (d : T ⟶ T')
    (c : T' ⋙ R ≅ H ⋙ F) (M : C) :
    (sectionTensorUnitComposite S T T' R H F a q d c).app M =
      a.hom.app M ≫ R.map (q.inv.app M) ≫ R.map (d.app M) ≫ c.hom.app M := by
  rfl

/-- Applying a functor and then a morphism to the abstract unit component. -/
theorem sectionTensorUnitComposite_map_post_app
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    (S T T' : C ⥤ E) (R : E ⥤ C) (H : C ⥤ D) (F : D ⥤ C)
    (a : 𝟭 C ≅ S ⋙ R) (q : T ≅ S) (d : T ⟶ T')
    (c : T' ⋙ R ≅ H ⋙ F) (P : C ⥤ V) (M : C) {Z : V}
    (ε : P.obj ((H ⋙ F).obj M) ⟶ Z) :
    P.map (Adjunction.unitComponent H F
      (sectionTensorUnitComposite S T T' R H F a q d c) M) ≫ ε =
      P.map (Adjunction.unitComponent S R a.hom M ≫ R.map (q.inv.app M) ≫
        R.map (d.app M) ≫ c.hom.app M) ≫ ε := by
  simp only [Adjunction.unitComponent_eq, sectionTensorUnitComposite_app]

/-- Composing the abstract unit component with an arbitrary morphism. -/
theorem sectionTensorUnitComposite_post_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S T T' : C ⥤ E) (R : E ⥤ C) (H : C ⥤ D) (F : D ⥤ C)
    (a : 𝟭 C ≅ S ⋙ R) (q : T ≅ S) (d : T ⟶ T')
    (c : T' ⋙ R ≅ H ⋙ F) (M : C) {Z : C} (ε : (H ⋙ F).obj M ⟶ Z) :
    (sectionTensorUnitComposite S T T' R H F a q d c).app M ≫ ε =
      (a.hom.app M ≫ R.map (q.inv.app M) ≫
        R.map (d.app M) ≫ c.hom.app M) ≫ ε := by
  rw [sectionTensorUnitComposite_app]

/-- Tensor the supported diagonal class and push along the second projection. -/
def supportedDiagonalUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L)) :
    𝟭 (DerivedCategoryModule A X) ⟶ ordinaryFinitePushforward A f ⋙ CoordinateTrace.H A f L :=
  sectionTensorUnitComposite
    (ordinaryFinitePushforward A (pullback.diagonal f)) _ _
    (ordinaryFinitePushforward A (pullback.snd f f))
    (ordinaryFinitePushforward A f) (CoordinateTrace.H A f L)
    (diagonalPushSection A f) (diagonalTensorIso A f)
    (Functor.whiskerLeft (ordinaryFinitePullback A (pullback.fst f f))
      (((flipFunctor _ _ _).obj (ordinaryFiniteTensor A (pullback f f))).map δ))
    (diagonalComparison A f L)
/-- Functorial form of the supported unit component equation. -/
theorem supportedDiagonalUnit_map_post_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L)) (M : DerivedCategoryModule A X)
    (P : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y)
    {Z : DerivedCategoryModule A Y}
    (ε : P.obj ((ordinaryFinitePushforward A f ⋙ CoordinateTrace.H A f L).obj M) ⟶ Z) :
    P.map (Adjunction.unitComponent (ordinaryFinitePushforward A f)
      (CoordinateTrace.H A f L) (supportedDiagonalUnit A f L δ) M) ≫ ε =
      P.map (Adjunction.unitComponent
        (ordinaryFinitePushforward A (pullback.diagonal f))
        (ordinaryFinitePushforward A (pullback.snd f f))
        (diagonalPushSection A f).hom M ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          ((diagonalTensorIso A f).inv.app M) ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          (((ordinaryFiniteTensor A (pullback f f)).obj
            ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ) ≫
        (diagonalComparison A f L).hom.app M) ≫ ε := by
  exact sectionTensorUnitComposite_map_post_app _ _ _ _ _ _ _ _ _ _ P M ε

/-- Postcomposition form of the supported unit component equation. -/
theorem supportedDiagonalUnit_post_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L)) (M : DerivedCategoryModule A X)
    {Z : DerivedCategoryModule A X}
    (ε : (ordinaryFinitePushforward A f ⋙ CoordinateTrace.H A f L).obj M ⟶ Z) :
    (supportedDiagonalUnit A f L δ).app M ≫ ε =
      ((diagonalPushSection A f).hom.app M ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          ((diagonalTensorIso A f).inv.app M) ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          (((ordinaryFiniteTensor A (pullback f f)).obj
            ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ) ≫
        (diagonalComparison A f L).hom.app M) ≫ ε := by
  exact sectionTensorUnitComposite_post_app _ _ _ _ _ _ _ _ _ _ M ε

end AlgebraicGeometry.Etale
