/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import WeilConjectures.AlgebraicGeometry.IntegralSectionCoefficientNaturality
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleSliceOrdinaryComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.StrictTowerOperations

/-! # Local isomorphisms under the integral section comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage integralSectionRingIso

private theorem comparisonNonemptyIso
    {A : Type*} {B : Type*} {C : Type*} [Category A] [Category B] [Category C]
    (L : A ⥤ B) (F : A ⥤ C) (Q : B ≌ C) (e : L ⋙ Q.functor ≅ F)
    (M N : A) : Nonempty (L.obj M ≅ L.obj N) ↔ Nonempty (F.obj M ≅ F.obj N) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨(e.app M).symm ≪≫ Q.functor.mapIso i ≪≫ e.app N⟩
  · rintro ⟨i⟩
    exact ⟨Q.functor.preimageIso (e.app M ≪≫ i ≪≫ (e.app N).symm)⟩

private def scalarPushforwardIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R R' : Sheaf J RingCat.{u + 1}} {S S' : Sheaf K RingCat.{u + 1}}
    (a : R ≅ R') (b : S ≅ S')
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (ψ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S')
    (h : a.hom ≫ ψ = φ ≫
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b.hom) :
    SheafOfModules.pushforward.{u + 1} ψ ⋙ SheafOfModules.restrictScalars a.hom ≅
      SheafOfModules.restrictScalars b.hom ⋙ SheafOfModules.pushforward φ := by
  exact SheafOfModules.pushforwardCongr h

private def restrictComposition
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S) (ψ : S ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1} (φ ≫ ψ) ≅
      SheafOfModules.restrictScalars ψ ⋙ SheafOfModules.restrictScalars φ :=
  (SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) φ ψ).symm

private theorem globalSectionComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) :
    let R := Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)
    let B := (sheafCompose (Scheme.ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)
    ∃ Q : AdicCompletion.Modules l E S ≌ SheafOfModules.{u + 1} B,
      Nonempty (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g ⋙ Q.functor ≅
        integralSectionFunctor l E X ⋙
          SheafOfModules.restrictScalars
            (Scheme.integralDetailedCoefficientComparison X l E).hom ⋙
          Scheme.proEtaleModuleInverseImage g R) := by
  let Λ := DerivedNakayama.integerRing l E
  let R := Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)
  let F := Scheme.proEtaleBaseChange g
  let J := Scheme.ProEt.topology X
  let K := Scheme.ProEt.topology S
  let B := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)
  let a : (Scheme.adicLisseForget X).obj R ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B :=
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  obtain ⟨c, hc, _⟩ := integralSectionCoefficientNaturality l E g
  let d := integralDetailedSectionRingComparison l E X
  let EX := (InternalModuleOperations.equivalence Λ X).trans (restrictionEquivalence d)
  let ES := (InternalModuleOperations.equivalence Λ S).trans (restrictionEquivalence c)
  let r : CondensedRing.lowerStar Λ g ⋙ EX.functor ≅
      ES.functor ⋙ SheafOfModules.pushforward a :=
    Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison Λ g)
        (SheafOfModules.restrictScalars d.hom) ≪≫
      Functor.isoWhiskerLeft (InternalModuleOperations.equivalence Λ S).functor
        (scalarPushforwardIso F d c a (InternalModuleOperations.coefficientMap Λ g) hc)
  obtain ⟨b, _, _⟩ := InternalModuleOperations.comparison_existsUnique EX ES
    (CondensedRing.upperStarLowerStarAdjunction Λ g) (Scheme.canonicalAdjunction g R) r
  let cX := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (integralSectionRingIso l E X).inv
  let t : EX.functor ≅ integralSectionFunctor l E X ⋙
      SheafOfModules.restrictScalars
        (Scheme.integralDetailedCoefficientComparison X l E).hom := by
    have hd : d.hom =
        (Scheme.integralDetailedCoefficientComparison X l E).hom ≫ cX := rfl
    let t0 := eqToIso (congrArg SheafOfModules.restrictScalars hd) ≪≫
      restrictComposition (Scheme.integralDetailedCoefficientComparison X l E).hom cX
    unfold integralSectionFunctor
    exact Functor.isoWhiskerLeft (InternalModuleOperations.equivalence Λ X).functor t0
  exact ⟨ES, ⟨b ≪≫ Functor.isoWhiskerRight t (Scheme.proEtaleModuleInverseImage g R)⟩⟩

private def inverseImageRingedComparison {X S : Scheme.{u}} (g : S ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ T) :
    Scheme.proEtaleModuleInverseImage g R ⋙
        (restrictionEquivalence ((sheafCompose (Scheme.ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).symm).functor ≅
      Scheme.proEtaleRingModulePullback g R T c := by
  let Q := restrictionEquivalence ((sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).symm
  exact ((Scheme.canonicalAdjunction g R).comp Q.toAdjunction).leftAdjointUniq
    (Scheme.proEtaleRingModuleAdjunction g R T c)

private theorem sliceModuleEquivalence {S : Scheme.{u}} (U : S.ProEt)
    (R : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1}) :
    ∃ Q : SheafOfModules.{u + 1}
        (((sheafCompose (Scheme.ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U) ≌
      Scheme.proEtaleRingModules U.left (Scheme.proEtaleSliceRing U R),
      Nonempty (SheafOfModules.overFunctor _ U ⋙ Q.functor ≅
        Scheme.proEtaleSliceModuleRestriction U R) := by
  let J := Scheme.ProEt.topology S
  let K := Scheme.ProEt.topology U.left
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have := Scheme.ProEt.sliceDense S U
  obtain ⟨Q, hQ⟩ := Scheme.ProEt.module_transport (J.over U) K
    (Scheme.ProEt.sliceEquiv S U) (A.over U)
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Scheme.proEtaleSliceRing U R)) (Iso.refl _)
  refine ⟨Q, ⟨?_⟩⟩
  apply Functor.fullyFaithfulCancelRight (SheafOfModules.forget _)
  exact eqToIso (congrArg (fun F ↦ SheafOfModules.overFunctor A U ⋙ F) hQ)

private theorem inverseImageLocalIsomorphisms {X S : Scheme.{u}} (g : S ⟶ X)
    (U : S.ProEt) (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M N : Scheme.proEtaleRingModules X R) :
    Nonempty ((Scheme.proEtaleModuleInverseImage
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g) R).obj M ≅
      (Scheme.proEtaleModuleInverseImage
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g) R).obj N) ↔
    Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g R).obj M) ≅
      (SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g R).obj N)) := by
  let R1 := (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R
  let R2 := (Scheme.proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj R1
  let c := Scheme.proEtaleRingCompositeCoefficients U.hom g R R1 R2
    (Iso.refl _) (Iso.refl _)
  let Q0 := restrictionEquivalence ((sheafCompose (Scheme.ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).symm
  let delta := Scheme.restrictionComparison U CommRingCat.{u + 1}
  let b := Scheme.proEtaleSliceCoefficientIso U R1 R2 (Iso.refl _) delta
  let Qb := restrictionEquivalence ((sheafCompose (Scheme.ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso b).symm
  obtain ⟨Q, ⟨hQ⟩⟩ := sliceModuleEquivalence U R1
  let QT := Q.trans Qb
  obtain ⟨hU, _⟩ := Scheme.proEtaleSlice_ordinary_comparison U R1 R2 (Iso.refl _) delta
  let e : Scheme.proEtaleModuleInverseImage (U.hom ≫ g) R ⋙ Q0.functor ≅
      Scheme.proEtaleModuleInverseImage g R ⋙
        SheafOfModules.overFunctor _ U ⋙ QT.functor :=
    inverseImageRingedComparison (U.hom ≫ g) R R2 c ≪≫
      Scheme.exchangeModuleComposition U.hom g R R1 R2 (Iso.refl _) (Iso.refl _) ≪≫
      Functor.isoWhiskerRight (inverseImageRingedComparison g R R1 (Iso.refl _)).symm
        (Scheme.proEtaleRingModulePullback U.hom R1 R2 (Iso.refl _)) ≪≫
      Functor.isoWhiskerLeft (Scheme.proEtaleModuleInverseImage g R) hU ≪≫
      Functor.isoWhiskerLeft (Scheme.proEtaleModuleInverseImage g R)
        (Functor.isoWhiskerRight hQ.symm Qb.functor)
  constructor
  · rintro ⟨i⟩
    exact ⟨QT.functor.preimageIso
      ((e.app M).symm ≪≫ Q0.functor.mapIso i ≪≫ e.app N)⟩
  · rintro ⟨i⟩
    exact ⟨Q0.functor.preimageIso
      (e.app M ≪≫ QT.functor.mapIso i ≪≫ (e.app N).symm)⟩

private theorem globalSectionIsomorphisms (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (M N : AdicCompletion.Modules l E X) :
    Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).obj M ≅
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).obj N) ↔
    Nonempty ((Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
          ((SheafOfModules.restrictScalars
            (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
              ((integralSectionFunctor l E X).obj M)) ≅
      (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
          ((SheafOfModules.restrictScalars
            (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
              ((integralSectionFunctor l E X).obj N))) := by
  obtain ⟨Q, ⟨e⟩⟩ := globalSectionComparison l E g
  exact comparisonNonemptyIso _ _ Q e M N

/-- The fixed section equivalence and the coefficient comparisons preserve and reflect
isomorphisms after inverse image and localization at a pro-etale member.

Source: Bhatt--Scholze, Proposition 6.8.11(3), the inverse-image and slice-site
comparison in the integral constructibility bridge.
(auxiliary; not a blueprint node).

Proof: the section equivalence identifies internal direct image with ringed direct
image. The coefficient naturality square transports this identification through
the fixed detailed source comparison and a compatible coefficient isomorphism on
the target. Uniqueness of left adjoints then compares internal and algebraic
inverse image. Apply this along U.hom followed by g. For algebraic inverse images,
the composite pullback comparison and the equivalence between the pro-etale site
of U.left and the slice site at U identify inverse image along U.hom with
restriction to U. Thus the two functors in the assertion become naturally
isomorphic after equivalences of their target module categories. Map an
isomorphism through these equivalences for one direction and lift it by full
faithfulness for the other. All constructions apply to arbitrary modules,
including zero objects and empty schemes. -/
theorem integralSectionLocalIsomorphisms (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M N : AdicCompletion.Modules l E X) :
    Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj M ≅
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj N) ↔
    Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj M))) ≅
      (SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj N)))) := by
  exact (globalSectionIsomorphisms l E
    (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g) M N).trans
    (inverseImageLocalIsomorphisms g U
      (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))
      ((SheafOfModules.restrictScalars
        (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
          ((integralSectionFunctor l E X).obj M))
      ((SheafOfModules.restrictScalars
        (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
          ((integralSectionFunctor l E X).obj N)))

end AlgebraicGeometry.ProEtale
