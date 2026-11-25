/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralPullbackScalarComparison
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre

/-! # Finite reduction under normalized residue coefficients

## References

* Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1)
* Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.8(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

private def restrictionRoundTrip {S : Scheme.{u}}
    {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (e : R ≅ B) :
    pbcDerivedRestrict e.hom ⋙ pbcDerivedRestrict e.inv ≅ 𝟭 _ :=
  pbcDerivedRestrictComp e.inv e.hom (𝟙 B) e.inv_hom_id ≪≫
    coefficientDerivedRestrictIdentity B

private def rawPullbackNormalized {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (e : (adicTowerInverseImage g).obj R ≅ B) :
    adicTowerPullback g R ⋙ pbcDerivedRestrict e.inv ≅
      proEtaleRingDerivedPullback g R B e :=
  Functor.isoWhiskerRight (derivedPullbackScalarIso g R B e).symm
      (pbcDerivedRestrict e.inv) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionRoundTrip e) ≪≫ Functor.rightUnitor _

private def scalarReductionTransport {S : Scheme.{u}}
    {R R' B B' : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (e : R ≅ R') (b : B ≅ B') (π : R ⟶ B) (ρ : R' ⟶ B')
    (h : e.hom ≫ ρ = π ≫ b.hom) :
    pbcDerivedRestrict e.inv ⋙ pbcDerivedExtend ρ ≅
      pbcDerivedExtend π ⋙ pbcDerivedRestrict b.inv := by
  have he : (pbcDerivedRestrict e.inv).IsEquivalence :=
    derivedRestrictIso_isEquivalence e.symm
  have hb : (pbcDerivedRestrict b.inv).IsEquivalence :=
    derivedRestrictIso_isEquivalence b.symm
  have h' : e.inv ≫ π = ρ ≫ b.inv := by
    apply (cancel_mono b.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun z ↦ e.inv ≫ z) h.symm
  exact (scalarAdjunctionCoefficientEquivalence
    (pbcDerivedScalarAdjunction π) (pbcDerivedScalarAdjunction ρ)
    (pbcDerivedRestrict e.inv) (pbcDerivedRestrict b.inv)
    (derivedRestrictionSquare e.inv π b.inv ρ h')).choose.symm

private def constantAssociatedComparison (T : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    pbcAssociatedModule T B ((adicLisseForget T).obj (adicLisseConstantRing T B))
        (CoefficientSerre.proEtaleModuleScalarUnit T B) ≅
      (CoefficientSerre.encoding T B).inverse := by
  let L := pbcAssociatedModule T B
    ((adicLisseForget T).obj (adicLisseConstantRing T B))
    (CoefficientSerre.proEtaleModuleScalarUnit T B)
  let a : L ⊣ (CoefficientSerre.encoding T B).functor :=
    (PresheafOfModules.sheafificationAdjunction
      (CoefficientSerre.proEtaleModuleScalarUnit T B)).restrictFullyFaithful
        (Functor.FullyFaithful.ofFullyFaithful (CoefficientSerre.moduleEmbedding T B))
        (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  exact a.leftAdjointUniq (CoefficientSerre.encoding T B).symm.toAdjunction

private def fixedRestrictIdentity (T : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    Sheaf.restrictScalars (ProEt.topology T) (RingHom.id B) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl (M.obj.obj U))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private def constantLargeIso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (adicLisseForget T).mapIso (pbcLevelConstantComparison T d n) ≪≫
    AdicCoefficients.finiteRingComparison T (PbcQuotient d n)

private theorem constantLargeIso_scalars (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    CoefficientSerre.proEtaleModuleScalarUnit T (PbcQuotient d n) ≫
        (constantLargeIso T d n).hom.hom =
      finiteCoefficientScalarMap T (PbcQuotient d n) := by
  have h := (AdicCoefficients.finiteRingComparison_exists T (PbcQuotient d n)).choose_spec.1.2
  ext U x
  change ((AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).hom.hom.app U).hom
    (((pbcLevelConstantComparison T d n).hom.hom.app U).hom
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (PbcQuotient d n)))).app U x)) = _
  erw [(pbcLevelConstantComparison_exists T d n).exists.choose_spec U x]
  exact ConcreteCategory.congr_hom (congr_app h U)
    (AdicCoefficients.constants T (PbcQuotient d n) |>.app U |>.hom <| x)

private def largeRealizationToConstant (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    finiteCoefficientRealization T (PbcQuotient d n) ⋙
        SheafOfModules.restrictScalars (constantLargeIso T d n).hom ≅
      (CoefficientSerre.encoding T (PbcQuotient d n)).inverse := by
  let B := PbcQuotient d n
  let L := pbcAssociatedModule T B ((adicLisseForget T).obj (adicLisseConstantRing T B))
    (CoefficientSerre.proEtaleModuleScalarUnit T B)
  let e := (pbcAssociatedRestriction_exists T B B
    ((adicLisseForget T).obj (adicLisseConstantRing T B))
    (finiteCoefficientRingSheaf T B)
    (CoefficientSerre.proEtaleModuleScalarUnit T B) (finiteCoefficientScalarMap T B)
    (RingHom.id B) (constantLargeIso T d n).hom (by
      simpa using constantLargeIso_scalars T d n)).exists.choose
  exact e.symm ≪≫ Functor.isoWhiskerRight (fixedRestrictIdentity T B) L ≪≫
    Functor.leftUnitor L ≪≫ constantAssociatedComparison T B

private def constantRingPullbackEncoding {T S : Scheme.{u}} (g : S ⟶ T)
    (B : Type (u + 1)) [CommRing B] :
    proEtaleRingModulePullback g (adicLisseConstantRing T B) (adicLisseConstantRing S B)
        (CoefficientSerre.coefficientIso g B) ≅
      (CoefficientSerre.encoding T B).functor ⋙
        upperStar (ModuleCat.{u + 1} B) g ⋙ (CoefficientSerre.encoding S B).inverse := by
  let ET := CoefficientSerre.encoding T B
  let ES := CoefficientSerre.encoding S B
  let a := ET.toAdjunction.comp
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g).comp ES.symm.toAdjunction)
  let r : ES.functor ⋙ lowerStar (ModuleCat.{u + 1} B) g ⋙ ET.inverse ≅
      proEtaleRingModuleDirectImage g (adicLisseConstantRing T B)
        (adicLisseConstantRing S B) (CoefficientSerre.coefficientIso g B) :=
    Functor.isoWhiskerRight (CoefficientSerre.directImageComparison g B).symm ET.inverse ≪≫
      Functor.isoWhiskerLeft _ ET.unitIso.symm
  exact (proEtaleRingModuleAdjunction g (adicLisseConstantRing T B)
    (adicLisseConstantRing S B) (CoefficientSerre.coefficientIso g B)).leftAdjointUniq
      (a.ofNatIsoRight r)

private def finiteConstantPullbackEncoding {T S : Scheme.{u}} (g : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    SheafOfModules.restrictScalars (constantLargeIso T d n).hom ⋙
        proEtaleRingModulePullback g (adicLisseConstantRing T (PbcQuotient d n))
          (adicLisseConstantRing S (PbcQuotient d n))
          (CoefficientSerre.coefficientIso g (PbcQuotient d n)) ≅
      finiteCoefficientPullback T (PbcQuotient d n) g ⋙
        SheafOfModules.restrictScalars (constantLargeIso S d n).hom := by
  let B := PbcQuotient d n
  let RT := (finiteCoefficientRealization T B).asEquivalence
  let ET := CoefficientSerre.encoding T B
  let ES := CoefficientSerre.encoding S B
  let H := SheafOfModules.restrictScalars (constantLargeIso T d n).hom
  let ht : H ≅ RT.inverse ⋙ ET.inverse :=
    (RT.invFunIdAssoc H).symm ≪≫
      Functor.isoWhiskerLeft RT.inverse (largeRealizationToConstant T d n)
  exact Functor.isoWhiskerRight ht _ ≪≫
    Functor.isoWhiskerLeft _ (constantRingPullbackEncoding g B) ≪≫
    Functor.isoWhiskerLeft RT.inverse
      (ET.invFunIdAssoc (upperStar (ModuleCat.{u + 1} B) g ⋙ ES.inverse)) ≪≫
    Functor.isoWhiskerLeft (RT.inverse ⋙ upperStar (ModuleCat.{u + 1} B) g)
      (largeRealizationToConstant S d n).symm

private def finiteFunctionDerivedPullback {T S : Scheme.{u}} (g : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    let RT := SheafOfModules.restrictScalars
      (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).hom
    let RS := SheafOfModules.restrictScalars
      (AdicCoefficients.finiteRingComparison S (PbcQuotient d n)).hom
    letI := WeilConjectures.restriction_isEquivalence
      (AdicCoefficients.finiteRingComparison T (PbcQuotient d n))
    letI := WeilConjectures.restriction_isEquivalence
      (AdicCoefficients.finiteRingComparison S (PbcQuotient d n))
    RT.mapDerivedCategory ⋙ d.finitePull g n ≅
      finiteCoefficientDerivedPullback T (PbcQuotient d n) g ⋙ RS.mapDerivedCategory := by
  let B := PbcQuotient d n
  let RT := SheafOfModules.restrictScalars (AdicCoefficients.finiteRingComparison T B).hom
  let RS := SheafOfModules.restrictScalars (AdicCoefficients.finiteRingComparison S B).hom
  letI := WeilConjectures.restriction_isEquivalence (AdicCoefficients.finiteRingComparison T B)
  letI := WeilConjectures.restriction_isEquivalence (AdicCoefficients.finiteRingComparison S B)
  letI := WeilConjectures.restriction_isEquivalence (constantLargeIso T d n)
  letI := WeilConjectures.restriction_isEquivalence (constantLargeIso S d n)
  letI : (finiteCoefficientPullback T B g).Additive :=
    finiteCoefficientPullback_additive T B g
  letI : PreservesFiniteLimits (finiteCoefficientPullback T B g) :=
    finiteCoefficientPullback_preservesFiniteLimits T B g
  letI : PreservesFiniteColimits (finiteCoefficientPullback T B g) :=
    finiteCoefficientPullback_preservesFiniteColimits T B g
  let cT := pbcLevelConstantComparison T d n
  let cS := pbcLevelConstantComparison S d n
  let κ := CoefficientSerre.coefficientIso g B
  have hc : κ.hom ≫ cS.hom = (adicTowerInverseImage g).map cT.hom ≫
      (d.finiteRingIso g n).hom := by
    dsimp only [cT, cS, AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, asIso_hom]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  let a := proEtaleRingRestrictionDerivedPullback g
    (adicLisseConstantRing T B) (d.finiteRing T n)
    (adicLisseConstantRing S B) (d.finiteRing S n)
    cT.hom cS.hom κ (d.finiteRingIso g n) hc
  let iT : RT ⋙ pbcRestrict cT.hom ≅
      SheafOfModules.restrictScalars (constantLargeIso T d n).hom := Iso.refl _
  let iS : RS ⋙ pbcRestrict cS.hom ≅
      SheafOfModules.restrictScalars (constantLargeIso S d n).hom := Iso.refl _
  have : (pbcDerivedRestrict cS.hom).IsEquivalence := derivedRestrictIso_isEquivalence cS
  let F := (Functor.FullyFaithful.ofFullyFaithful (pbcDerivedRestrict cS.hom)).whiskeringRight
    (FiniteCoefficientDerivedCategory T B)
  apply F.preimageIso
  exact Functor.isoWhiskerLeft RT.mapDerivedCategory a ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso RT
      (pbcRestrict cT.hom) ≪≫ Functor.mapDerivedCategoryNatIso iT) _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (finiteConstantPullbackEncoding g d n) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ ((Functor.mapDerivedCategoryNatIso iS).symm ≪≫
      (Functor.mapDerivedCategoryCompIso RS (pbcRestrict cS.hom)).symm)

private def liftRingIso (S : Scheme.{u})
    {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (e : (adicLisseForget S).obj R ≅ (adicLisseForget S).obj B) : R ≅ B :=
  (fullyFaithfulSheafCompose (ProEt.topology S)
    (Functor.FullyFaithful.ofFullyFaithful
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).preimageIso e

private theorem liftRingIso_hom (S : Scheme.{u})
    {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (e : (adicLisseForget S).obj R ≅ (adicLisseForget S).obj B) :
    (adicLisseForget S).map (liftRingIso S e).hom = e.hom :=
  (fullyFaithfulSheafCompose (ProEt.topology S)
    (Functor.FullyFaithful.ofFullyFaithful
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).map_preimage _

/-- Restriction along the finite coefficient isomorphism, on a localization representative.
The representative is canonical up to its supplied localization isomorphism. -/
def integralResidueFiniteModel
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ)
    (M : FiniteCoefficientDerivedCategory S (PbcQuotient (pbcIntegralDatum l E) n)) :
    DerivedCategory (SheafOfModules.{u + 1} (completedAdicFiniteRing S d n)) :=
  let e := (AdicCoefficients.finiteRingComparison S
      (PbcQuotient (pbcIntegralDatum l E) n)).symm ≪≫
    integralDetailedLevelComparison S l E n ≪≫ c.finite n
  DerivedCategory.Q.obj
    (((SheafOfModules.restrictScalars e.inv).mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage M))

private local instance integralResidueFiniteCategory (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} R)] :
    Category.{u + 2} (DerivedCategory (SheafOfModules.{u + 1} R)) := inferInstance

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Reduction commutes with the normalized integral coefficient comparison and inverse image.
There is no completeness, perfectness or covering hypothesis. -/
theorem integralResidueFiniteReduction
    (T S : Scheme.{u}) (g : S ⟶ T) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (C : CochainComplex
      (FiniteCoefficientModules T (PbcQuotient (pbcIntegralDatum l E) n)) ℤ)
    (eC : Nonempty
      ((DerivedCategory.Q.obj (((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison T
          (PbcQuotient (pbcIntegralDatum l E) n)).hom).mapHomologicalComplex (.up ℤ)).obj C) :) ≅
        (pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K)) :
    Nonempty
      ((completedAdicQuotientReduction S d n).obj
          ((adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) ⋙
            pbcDerivedRestrict ((pbcIntegralDatum l E).integralRingIso g ≪≫
              WeilConjectures.purCoefficientIso l E S ≪≫ c.completed.symm).inv).obj K) ≅
        integralResidueFiniteModel S l E d c n
          ((finiteCoefficientDerivedPullback T (PbcQuotient (pbcIntegralDatum l E) n) g).obj
            (DerivedCategory.Q.obj C))) := by
  let D := pbcIntegralDatum l E
  let i := D.integralRingIso g
  let e := WeilConjectures.purCoefficientIso l E S ≪≫ c.completed.symm
  let bR := integralDetailedLevelComparison S l E n ≪≫ c.finite n
  let b := liftRingIso S (R := (pbcAdicRings S D).obj (Opposite.op n))
    (B := completedAdicFiniteCommRing S d n) bR
  have hb : (adicLisseForget S).map b.hom = bR.hom :=
    liftRingIso_hom S (R := (pbcAdicRings S D).obj (Opposite.op n))
      (B := completedAdicFiniteCommRing S d n) bR
  have hb' : (adicLisseForget S).map b.inv = bR.inv := by
    apply (cancel_mono bR.hom).mp
    calc
      (adicLisseForget S).map b.inv ≫ bR.hom = 𝟙 _ := by
        rw [← hb, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
      _ = bR.inv ≫ bR.hom := bR.inv_hom_id.symm
  have he : (adicLisseForget S).mapIso (WeilConjectures.purCoefficientIso l E S) =
      integralDetailedCoefficientComparison S l E :=
    (WeilConjectures.purCoefficientIso_existsUnique l E S).exists.choose_spec
  have hπ : e.hom ≫ completedAdicCommProjection S d n =
      pbcAdicProjection S D n ≫ b.hom := by
    apply (adicLisseForget S).map_injective
    rw [Functor.map_comp, Functor.map_comp, hb]
    change (adicLisseForget S).map e.hom ≫ completedAdicProjection S d n = _
    rw [← c.completed_projection n]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Functor.map_comp]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := (integralDetailedCoefficientComparison_exists S l E).exists.choose_spec n
    change (integralDetailedCoefficientComparison S l E).hom ≫ _ = _ at h
    simpa only [← he, Functor.mapIso_hom, bR, Iso.trans_hom, Category.assoc] using
      congrArg (fun z ↦ z ≫ (c.finite n).hom) h
  let raw := adicTowerPullback g (pbcAdicCompletion T D)
  let pulled := (D.pull g).obj K
  let a : (pbcDerivedRestrict (i ≪≫ e).inv).obj (raw.obj K) ≅
      (pbcDerivedRestrict e.inv).obj pulled :=
    ((pbcDerivedRestrictComp e.inv i.inv (i ≪≫ e).inv rfl).app (raw.obj K)).symm ≪≫
      (pbcDerivedRestrict e.inv).mapIso
        ((rawPullbackNormalized g (pbcAdicCompletion T D) (pbcAdicCompletion S D) i).app K)
  let σ := scalarReductionTransport e b (pbcAdicProjection S D n)
    (completedAdicCommProjection S d n) hπ
  let red := completedAdicQuotientReduction S d n
  let Rb := pbcDerivedRestrict b.inv
  let RT := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison T (PbcQuotient D n)).hom
  let RS := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison S (PbcQuotient D n)).hom
  have := WeilConjectures.restriction_isEquivalence
    (AdicCoefficients.finiteRingComparison T (PbcQuotient D n))
  have := WeilConjectures.restriction_isEquivalence
    (AdicCoefficients.finiteRingComparison S (PbcQuotient D n))
  let fp := finiteCoefficientDerivedPullback T (PbcQuotient D n) g
  let M := fp.obj (DerivedCategory.Q.obj C)
  let r := (AdicCoefficients.finiteRingComparison S (PbcQuotient D n)).symm ≪≫ bR
  let F := SheafOfModules.restrictScalars r.inv
  have : F.IsEquivalence := WeilConjectures.restriction_isEquivalence r.symm
  let t : RS ⋙ pbcRestrict b.inv ≅ F := by
    dsimp only [pbcRestrict, proEtaleRingRestrictScalars]
    rw [hb']
    exact Iso.refl _
  let t' : RS.mapDerivedCategory ⋙ Rb ≅ F.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso RS (pbcRestrict b.inv) ≪≫
      Functor.mapDerivedCategoryNatIso t
  obtain ⟨eC⟩ := eC
  let j : RT.mapDerivedCategory.obj (DerivedCategory.Q.obj C) ≅
      (pbcCompletedReduction T D n).obj K := RT.mapDerivedCategoryFactors.app C ≪≫ eC
  let endIso : F.mapDerivedCategory.obj M ≅ integralResidueFiniteModel S l E d c n M :=
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M :)
  refine ⟨?_⟩
  exact red.mapIso a ≪≫ σ.app pulled ≪≫
    Rb.mapIso (((D.chi g n).app K).symm) ≪≫
    Rb.mapIso ((D.finitePull g n).mapIso j.symm) ≪≫
    Rb.mapIso ((finiteFunctionDerivedPullback g D n).app (DerivedCategory.Q.obj C)) ≪≫
    t'.app M ≪≫ endIso

end AlgebraicGeometry.Scheme
