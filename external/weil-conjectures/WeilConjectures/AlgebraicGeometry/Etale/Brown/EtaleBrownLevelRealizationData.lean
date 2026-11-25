/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Data for a normalized Brown level realization

This module isolates the construction of the realization functors and their
factorization, restriction, and scalar comparison data. The coherence equations
are stated separately so that the categorical construction and its normalization
can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem brownRingUnit (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    realizationRingUnit W.smallEtaleTopology A ≫
      (realizationRingIso W.smallEtaleTopology A).hom.hom =
    toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj (RingCat.of A)) := by
  dsimp only [realizationRingIso, Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold realizationRingUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality W.smallEtaleTopology
    (Functor.constComp W.Etaleᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)

private def brownConstantComparison (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    ConstantScalarRestriction.restriction W.smallEtaleTopology A ≅
      Etale.SystemProjection.constantModule W (CommRingCat.of A) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)) ?_)) ?_
  · ext x
    have h := congrArg (fun f ↦ f.app U a) (brownRingUnit W A)
    have hi := congrArg (fun f ↦ f.hom.app U)
      (realizationRingIso W.smallEtaleTopology A).hom_inv_id
    change (realizationRingUnit W.smallEtaleTopology A).app U a •
      (show M.val.obj U from x) =
      (realizationRingIso W.smallEtaleTopology A).inv.hom.app U
      ((toSheafify W.smallEtaleTopology
        ((Functor.const W.Etaleᵒᵖ).obj (RingCat.of A))).app U a) •
        (show M.val.obj U from x)
    erw [← h]
    exact congrArg (fun b ↦ b • (show M.val.obj U from x))
      (ConcreteCategory.congr_hom hi _).symm
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem brownConstantEquivalence (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Etale.SystemProjection.constantModule W (CommRingCat.of A)).IsEquivalence := by
  let := ConstantScalarRestriction.isEquivalence W.smallEtaleTopology A
  exact Functor.isEquivalence_of_iso (brownConstantComparison W A)

private theorem brownConstantAdditive (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Etale.SystemProjection.constantModule W (CommRingCat.of A)).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

private local instance brownLevelAdditive
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u}) (n : ℕ) :
    Functor.Additive (C := strictEtaleLevel W O t n) (strictEtaleBrownConstant O t W n) := by
  constructor
  intro M N f g
  ext U x
  rfl

private local instance brownLevelEquivalence
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u}) (n : ℕ) :
    Functor.IsEquivalence (C := strictEtaleLevel W O t n)
      (strictEtaleBrownConstant O t W n) :=
  brownConstantEquivalence W (strictEtaleBrownRing O t n)

private def brownGenericRestriction (W : Scheme.{u})
    (A B : CommRingCat.{u + 1}) (f : A ⟶ B) :
    SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose W.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map f)) ⋙
      Etale.SystemProjection.constantModule W A ≅
    Etale.SystemProjection.constantModule W B ⋙
      Sheaf.restrictScalars W.smallEtaleTopology f.hom := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)) ?_)) ?_
  · ext x
    have hn := congrArg (fun g ↦ g.app U a)
      (toSheafify_naturality W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).map f))
    exact congrArg (fun b ↦ b • (show M.val.obj U from x)) hn
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def brownOrdinaryRestriction
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    coefficientRestriction (J := W.smallEtaleTopology) O t h ⋙
      strictEtaleBrownConstant O t W n ≅
    strictEtaleBrownConstant O t W m ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h) :=
  brownGenericRestriction W _ _ (CommRingCat.ofHom (strictEtaleBrownRingMap O t h))

private def brownDerivedRestriction
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) {m n : ℕ} (h : m ≤ n) :
    (P.scalar h).restriction ⋙ (strictEtaleBrownConstant O t W n).mapDerivedCategory
      (C₁ := strictEtaleLevel W O t n) ≅
      (strictEtaleBrownConstant O t W m).mapDerivedCategory
      (C₁ := strictEtaleLevel W O t m) ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h) := by
  let r := coefficientRestriction (J := W.smallEtaleTopology) O t h
  let e : (P.scalar h).restriction ≅ r.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel W O t m) (.up ℤ))
      (DerivedCategory.Q ⋙ (P.scalar h).restriction)
      (DerivedCategory.Q ⋙ r.mapDerivedCategory)
      (P.scalar h).restriction r.mapDerivedCategory
      ((P.scalar h).restrictionFactors ≪≫ r.mapDerivedCategoryFactors.symm)
  exact isoWhiskerRight e ((strictEtaleBrownConstant O t W n).mapDerivedCategory
      (C₁ := strictEtaleLevel W O t n)) ≪≫
    Functor.mapDerivedCategorySquareIso (A := strictEtaleLevel W O t m)
      (B := strictEtaleLevel W O t n) (brownOrdinaryRestriction O t W h)

private def brownInverseMateIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ⋙ F ≅ G ⋙ R') :
    L ⋙ G ≅ F ⋙ L' := by
  let α := ((mateEquiv a b).symm (.mk _ _ _ _ e.hom))
  letI : IsIso α := isIso_inverseMate_of_equivalences a b e
  exact (asIso α).symm

/-- The realization data can be constructed from a supplied strict evaluation package.

Source: Zheng, Construction 4.1 and Constructions 5.14--5.15, together with the
constant-ring module equivalence of Stacks 03CY. The construction first transports
modules along the constant-ring sheafification equivalence, then localizes the exact
transport at every level. The ordinary restriction maps are the sectionwise scalar
restriction maps; their derived maps are obtained by localization. Scalar extension
is the mate of these restriction maps under the supplied scalar adjunctions. This
statement deliberately omits all coherence equations, which are the subject of the
next theorem.
(blueprint: lem-pur-etale-brown-level-realization-data).
-/
theorem etaleBrownLevelRealizationData_exists
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) :
    Nonempty (StrictEtaleBrownRealizationData O t W P) := by
  refine ⟨{
    ordinaryAdditive := fun n ↦ brownConstantAdditive W (strictEtaleBrownRing O t n)
    derived := fun n ↦ (strictEtaleBrownConstant O t W n).mapDerivedCategory
      (C₁ := strictEtaleLevel W O t n)
    factors := fun n ↦ (strictEtaleBrownConstant O t W n).mapDerivedCategoryFactors
      (C₁ := strictEtaleLevel W O t n)
    equivalence := fun n ↦ inferInstance
    ordinaryRestriction := fun h ↦ brownOrdinaryRestriction O t W h
    restriction := fun h ↦ brownDerivedRestriction O t W P h
    scalar := fun h ↦ brownInverseMateIso (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h))) (brownDerivedRestriction O t W P h) }⟩

end AlgebraicGeometry
