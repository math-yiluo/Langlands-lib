/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-! # Transport of the actual recorded reduction comparison

Source: Stacks Tags 00YV, 06YY and 0GL6; blueprint Charts paragraph of
`lem-sp-et-proet-coefficient-compatibility`
(blueprint: def-sp-et-proet-coefficient-transport).

The transported arrow is the fully faithful preimage of the intrinsic arrow, conjugated
by the canonical support and scalar presentation comparisons. Thus it depends on that
arrow as a morphism, rather than retaining it beside an independently constructed map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

/-- The canonical universe lift of the given ring homomorphism.
Source: Stacks 00YV, constant coefficient size convention
(blueprint: def-sp-et-proet-coefficient-transport). -/
abbrev uliftRingHom {R S : Type u} [CommRing R] [CommRing S] (ψ : R →+* S) :
    ULift.{u + 1, u} R →+* ULift.{u + 1, u} S := ψ.ulift

/-- Scalar extension in the universe-lifted fixed-module presentation.
Source: Stacks 06YY (blueprint: def-sp-et-proet-coefficient-transport). -/
abbrev liftedScalarExtension {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (T : Scheme.{u}) :=
  @pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} R) (ULift.{u + 1, u} S) inferInstance inferInstance (uliftRingHom ψ)

/-- The scalar presentation comparison is the left-adjoint uniqueness isomorphism
whose right comparison is identity on the underlying sheafified abelian presheaf.
The latter is the unique section-normalized comparison of the recorded restriction
lemma, descended termwise. This fixes the tensor unit without any choice of a bare iso.
Source: Stacks 00YV, 03DA and 06YY
(blueprint: def-sp-et-proet-coefficient-transport). -/
def scalarPresentation {R S : Type u} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (ψ : R →+* S) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T R).functor ⋙ scalarExtensionFunctor ψ T ≅
      liftedScalarExtension ψ T ⋙ (sfIntrinsicDerivedEquivalence T S).functor :=
  let e : (sfIntrinsicDerivedEquivalence T S).functor ⋙ scalarRestriction ψ T ≅
      (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
        (ULift.{u + 1, u} R) (ULift.{u + 1, u} S) inferInstance inferInstance
        (uliftRingHom ψ)) ⋙ (sfIntrinsicDerivedEquivalence T R).functor :=
    Functor.mapDerivedCategorySquareIso
    ((sfRealizationRestriction_existsUnique T ψ).exists.choose)
  let rightIso :=
    isoWhiskerRight (sfIntrinsicDerivedEquivalence T S).counitIso.symm
      (scalarRestriction ψ T ⋙ (sfIntrinsicDerivedEquivalence T R).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicDerivedEquivalence T S).inverse
      (isoWhiskerRight e (sfIntrinsicDerivedEquivalence T R).inverse) ≪≫
    isoWhiskerLeft
      ((sfIntrinsicDerivedEquivalence T S).inverse ⋙
        @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
          (ULift.{u + 1, u} R) (ULift.{u + 1, u} S) inferInstance inferInstance
          (uliftRingHom ψ))
      (sfIntrinsicDerivedEquivalence T R).unitIso.symm
  (((sfIntrinsicDerivedEquivalence T R).toAdjunction.comp
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) ψ))).ofNatIsoRight
      rightIso).leftAdjointUniq
    ((Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
          (ULift.{u + 1, u} R) (ULift.{u + 1, u} S) inferInstance inferInstance
          (uliftRingHom ψ))).comp
        (sfIntrinsicDerivedEquivalence T S).toAdjunction)

/-- The direct-image presentation also changes from the identified-coefficient ringed
model to the sectionwise constant-ring model. Their right-adjoint uniqueness comparison
uses the uniquely unit-normalized pullback coordinates, then derives that isomorphism.
Source: Stacks 03D3 and 07A5
(blueprint: def-sp-et-proet-coefficient-transport). -/
def directImagePresentation (R : Type u) [CommRing R] [Finite R]
    {V W : Scheme.{u}} (q : V ⟶ W) :
    (sfIntrinsicDerivedEquivalence V R).functor ⋙ directImageConstantPush R q ≅
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) q).rightDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence W R).functor :=
  isoWhiskerLeft _
    (Functor.rightDerivedFunctorNatIso
      (((proEtaleConstantRingAdjunction R q).ofNatIsoLeft
        ((openSquarePullbackModel_existsUnique R q).exists.choose)).rightAdjointUniq
          (sfIntrinsicConstantModuleAdjunction q R))) ≪≫
    sfIntrinsicDerivedDirectImageComparison q R

/-- Compact-support presentation: cancel the realization unit for open extension, then
use the direct-image comparison uniquely fixed on K-injective representatives. These
are precisely the two presentation comparisons for the recorded Rp_* j_!.
Source: Stacks 00YV, 03DI and 07A5
(blueprint: def-sp-et-proet-coefficient-transport). -/
def supportPresentation (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X R).functor ⋙ reductionCompactSupport R c.i c.g ≅
      rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c ⋙
          (sfIntrinsicDerivedEquivalence Y R).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (mapDerivedCategoryCompIso _ _ ≪≫
        mapDerivedCategoryNatIso
          ((sfIntrinsicModuleEquivalence X R).funInvIdAssoc
            (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i ⋙
              (sfIntrinsicModuleEquivalence c.Z R).functor)) ≪≫
        (mapDerivedCategoryCompIso _ _).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (directImagePresentation R c.g) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
