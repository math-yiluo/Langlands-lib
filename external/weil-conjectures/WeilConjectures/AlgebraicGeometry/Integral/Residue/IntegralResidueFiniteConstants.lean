/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotientLift
public import WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence

/-! # Constants under the normalized finite coefficient comparison

## References

* Bhatt--Scholze, Lemma 6.5.8(1), (2) and Proposition 6.6.11
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

private def constantPresentation (S : Scheme.{u}) (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (α : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology S) α]
    [Presheaf.IsLocallySurjective (ProEt.topology S) α] :=
  siteConstantModulePresheafGeneral (C := S.ProEt) P ⋙
    PresheafOfModules.sheafification α

private def constantPresentationRestriction (S : Scheme.{u})
    (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (α : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology S) α]
    [Presheaf.IsLocallySurjective (ProEt.topology S) α] :
    constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ≅
      constantPresentation S P R α ⋙
        ConstantScalarComparison.restriction (ProEt.topology S) P R α := by
  let J := ProEt.topology S
  let η := (PresheafOfModules.sheafificationAdjunction α).unit
  let γ : constantSheaf J (ModuleCat.{u + 1} P) ⟶
      constantPresentation S P R α ⋙
        ConstantScalarComparison.restriction J P R α :=
    { app := ConstantScalarComparison.constantComparisonHom J P R α
      naturality := by
        intro M N f
        apply Sheaf.hom_ext
        apply sheafify_hom_ext J _ _
          ((ConstantScalarComparison.restriction J P R α).obj
            ((constantPresentation S P R α).obj N)).property
        change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj M) ≫
            ((constantSheaf J (ModuleCat.{u + 1} P)).map f).hom ≫
              (ConstantScalarComparison.constantComparisonHom J P R α N).hom =
          toSheafify J ((Functor.const S.ProEtᵒᵖ).obj M) ≫
            (ConstantScalarComparison.constantComparisonHom J P R α M).hom ≫ _
        change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj M) ≫
            sheafifyMap J ((Functor.const S.ProEtᵒᵖ).map f) ≫
              (ConstantScalarComparison.constantComparisonHom J P R α N).hom = _
        rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
        have hM := (sheafificationAdjunction J (ModuleCat.{u + 1} P)).homEquiv
          ((Functor.const S.ProEtᵒᵖ).obj M)
          ((ConstantScalarComparison.restriction J P R α).obj
            ((PresheafOfModules.sheafification α).obj
              (ConstantScalarComparison.constantPresheaf P M))) |>.apply_symm_apply
            (show (Functor.const S.ProEtᵒᵖ).obj M ⟶ _ from
              { app := fun U ↦ (η.app
                  (ConstantScalarComparison.constantPresheaf P M)).app U
                naturality := by
                  intro U V g
                  ext x
                  exact ConcreteCategory.congr_hom
                    ((η.app (ConstantScalarComparison.constantPresheaf P M)).naturality g) x })
        have hN := (sheafificationAdjunction J (ModuleCat.{u + 1} P)).homEquiv
          ((Functor.const S.ProEtᵒᵖ).obj N)
          ((ConstantScalarComparison.restriction J P R α).obj
            ((PresheafOfModules.sheafification α).obj
              (ConstantScalarComparison.constantPresheaf P N))) |>.apply_symm_apply
            (show (Functor.const S.ProEtᵒᵖ).obj N ⟶ _ from
              { app := fun U ↦ (η.app
                  (ConstantScalarComparison.constantPresheaf P N)).app U
                naturality := by
                  intro U V g
                  ext x
                  exact ConcreteCategory.congr_hom
                    ((η.app (ConstantScalarComparison.constantPresheaf P N)).naturality g) x })
        change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj M) ≫
          (ConstantScalarComparison.constantComparisonHom J P R α M).hom = _ at hM
        change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj N) ≫
          (ConstantScalarComparison.constantComparisonHom J P R α N).hom = _ at hN
        erw [hN, ← Category.assoc, hM]
        ext U x
        exact ConcreteCategory.congr_hom
          (congrArg (fun z ↦ z.app U)
            (η.naturality ((siteConstantModulePresheafGeneral
              (C := S.ProEt) P).map f))) x }
  have (M : ModuleCat.{u + 1} P) : IsIso (γ.app M) :=
    ConstantScalarComparison.constantComparisonHom_isIso J P R α M
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact asIso γ

private def associatedConstants (S : Scheme.{u}) (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (α : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology S) α]
    [Presheaf.IsLocallySurjective (ProEt.topology S) α] :
    constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ⋙
        pbcAssociatedModule S P R α ≅ constantPresentation S P R α := by
  let E := sheafToPresheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ⋙
    finiteCoefficientModulePresheaf S.ProEt P
  have : E.Full := by
    have := (coefficientModulePresheafFullyFaithful S.ProEt P).full
    exact inferInstance
  have : E.Faithful := by
    have := (coefficientModulePresheafFullyFaithful S.ProEt P).faithful
    exact inferInstance
  let G := ConstantScalarComparison.restriction (ProEt.topology S) P R α
  have : G.Full :=
    (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology S) P R α).full
  have : G.Faithful :=
    (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology S) P R α).faithful
  let a : pbcAssociatedModule S P R α ⊣ G :=
    (PresheafOfModules.sheafificationAdjunction α).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful E) (Functor.FullyFaithful.id _)
      (Iso.refl _) (Iso.refl _)
  have : (pbcAssociatedModule S P R α).IsEquivalence :=
    coefficientRealization_isEquivalence (ProEt.topology S) P R α
  exact Functor.fullyFaithfulCancelRight G
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P))
        (asIso a.unit).symm ≪≫ Functor.rightUnitor _ ≪≫
      constantPresentationRestriction S P R α)

private def constantScalarSquare (S : Scheme.{u})
    (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R T : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (α : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (β : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ T.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology S) α]
    [Presheaf.IsLocallySurjective (ProEt.topology S) α]
    [Presheaf.IsLocallyInjective (ProEt.topology S) β]
    [Presheaf.IsLocallySurjective (ProEt.topology S) β]
    (q : P ≃+* Q) (r : R ⟶ T)
    (h : α ≫ r.hom = (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫ β) :
    ModuleCat.restrictScalars.{u + 1} q.toRingHom ⋙ constantPresentation S P R α ≅
      constantPresentation S Q T β ⋙ SheafOfModules.restrictScalars r := by
  let C := constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} Q)
  let H := pbcAssociatedModule S P R α
  have : (ModuleCat.restrictScalars.{u + 1} q.toRingHom).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q.toRingHom).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u + 1} q.toRingHom).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q.toRingHom).isRightAdjoint
  let a := (pbcAssociatedRestriction_exists S P Q R T α β q.toRingHom r h).exists.choose
  exact Functor.isoWhiskerLeft _ (associatedConstants S P R α).symm ≪≫
    Functor.isoWhiskerRight
      (constantCommuteCompose (ProEt.topology S)
        (ModuleCat.restrictScalars.{u + 1} q.toRingHom)).symm H ≪≫
    Functor.isoWhiskerLeft C a ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedConstants S Q T β) _

private def finiteTransport (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ) :=
  (AdicCoefficients.finiteRingComparison S
      (PbcQuotient (pbcIntegralDatum l E) n)).symm ≪≫
    integralDetailedLevelComparison S l E n ≪≫ c.finite n

private theorem finiteTransport_constants (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ) :
    let P := PbcQuotient (pbcIntegralDatum l E) n
    let A := Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)
    let q := (integralResidueQuotientEquiv l E d hd n).trans
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm
    finiteCoefficientScalarMap S P ≫ (finiteTransport S l E d c n).hom.hom =
      (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫
        koszulConstantUnit S A ≫
          ((adicLisseForget S).map (residueLisseConstantComparison S d n)).hom := by
  dsimp only
  let P := PbcQuotient (pbcIntegralDatum l E) n
  let C := constantSheaf (ProEt.topology S) CommRingCat.{u + 1}
  let F := adicLisseForget S
  have hk : (constantLargeIso S (pbcIntegralDatum l E) n).hom ≫
      (finiteTransport S l E d c n).hom =
        F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom) ≫
          (c.finite n).hom := by
    simp only [constantLargeIso, finiteTransport, integralDetailedLevelComparison,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Category.id_comp]
    rfl
  rw [← constantLargeIso_scalars S (pbcIntegralDatum l E) n, ← Category.assoc]
  change adicLisseConstantUnit S P ≫
    ((constantLargeIso S (pbcIntegralDatum l E) n).hom ≫
      (finiteTransport S l E d c n).hom).hom = _
  rw [hk]
  ext U x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hu := congrArg (fun k ↦ (k.app U).hom (Ideal.Quotient.mk _ a))
    (toSheafify_naturality (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom)).symm
  change (F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom)).hom.app U
      ((adicLisseConstantUnit S P).app U (Ideal.Quotient.mk _ a)) =
    (adicLisseConstantUnit S _).app U
      (integralCoefficientULift l E n (Ideal.Quotient.mk _ a)) at hu
  change (c.finite n).hom.hom.app U
      ((F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom)).hom.app U
        ((adicLisseConstantUnit S P).app U (Ideal.Quotient.mk _ a))) = _
  have hq : integralCoefficientULift l E n (Ideal.Quotient.mk _ a) =
      ULift.up (Ideal.Quotient.mk _ a.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec a
  rw [hu, hq, c.finite_constants]
  change _ = (residueLisseConstantComparison S d n).hom.app U
    ((koszulConstantUnit S _).app U
      (ULift.up (integralResidueQuotientEquiv l E d hd n (Ideal.Quotient.mk _ a))))
  rw [integralResidueQuotientEquiv_mk,
    residueLisseConstantComparison_apply]

private def derivedChangeIso (S : Scheme.{u})
    {R T : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (e : R ≅ T) :
    completedAdicDerivedChange S e.hom ≅ pbcDerivedRestrict e.inv := by
  have : (pbcDerivedRestrict e.hom).IsEquivalence := derivedRestrictIso_isEquivalence e
  let E := (pbcDerivedRestrict e.hom).asEquivalence
  let H := pbcDerivedRestrict e.inv
  exact (pbcDerivedScalarAdjunction e.hom).leftAdjointUniq E.symm.toAdjunction ≪≫
    (Functor.rightUnitor E.inverse).symm ≪≫
    Functor.isoWhiskerLeft E.inverse (restrictionRoundTrip e).symm ≪≫
    E.invFunIdAssoc H

private def restrictSquare (S : Scheme.{u})
    {R T U : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    (f : R ⟶ T) (g : T ⟶ U) (h : R ⟶ U) (w : f ≫ g = h) :
    SheafOfModules.restrictScalars g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars.{u + 1} h :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun V ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app V).hom (g.hom.app V).hom
        (h.hom.app V).hom (congrArg (fun z : R ⟶ U ↦ (z.hom.app V).hom) w.symm)
        (M.val.obj V)).symm) (by intros; ext x; rfl)))
    (by intros; ext V x; rfl)

attribute [local irreducible] constantPresentation constantPresentationRestriction
  associatedConstants constantScalarSquare derivedChangeIso restrictSquare

private def transportedPresentation (S : Scheme.{u})
    (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R V W : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (α : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (β : (Functor.const S.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ V.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology S) α]
    [Presheaf.IsLocallySurjective (ProEt.topology S) α]
    [Presheaf.IsLocallyInjective (ProEt.topology S) β]
    [Presheaf.IsLocallySurjective (ProEt.topology S) β]
    (q : P ≃+* Q) (e : R ≅ W) (φ : V ≅ W)
    (h₀ : α ≫ e.hom.hom =
      (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫ β ≫ φ.hom.hom) :
    ModuleCat.restrictScalars.{u + 1} q.toRingHom ⋙
        constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ⋙
        pbcAssociatedModule S P R α ⋙ SheafOfModules.restrictScalars e.inv ≅
      constantPresentation S Q V β ⋙ SheafOfModules.restrictScalars φ.inv := by
  let r := e ≪≫ φ.symm
  have h : α ≫ r.hom.hom =
      (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫ β := by
    change α ≫ (e.hom ≫ φ.inv).hom = _
    calc
      _ = (α ≫ e.hom.hom) ≫ φ.inv.hom := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [h₀]
        change (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫
          β ≫ (φ.hom ≫ φ.inv).hom = _
        rw [φ.hom_inv_id]
        change (Functor.const S.ProEtᵒᵖ).map (RingCat.ofHom q.toRingHom) ≫
          β ≫ 𝟙 _ = _
        rw [Category.comp_id]
  let T := SheafOfModules.restrictScalars.{u + 1} e.inv
  let F := pbcAssociatedModule S P R α
  let C := constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P)
  let a : C ⋙ F ≅ constantPresentation S P R α := associatedConstants S P R α
  let b := constantScalarSquare S P Q R V α β q r.hom h
  exact Functor.isoWhiskerLeft _
      ((Functor.associator C F T).symm ≪≫ Functor.isoWhiskerRight a T) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight b T ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantPresentation S Q V β)
      (restrictSquare S e.inv r.hom φ.inv (by
        dsimp only [r, Iso.trans_hom, Iso.symm_hom]
        exact e.inv_hom_id_assoc _))

private def liftedRestriction (A : Type u) [CommRing A]
    (P : Type (u + 1)) [CommRing P] (q : P ≃+* A) :
    ModuleCat.uliftFunctor.{u + 1, u} A ⋙ ModuleCat.restrictScalars.{u + 1} q.toRingHom ≅
      (ModuleCat.uliftFunctor.{u + 1, u} A ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom) ⋙
      ModuleCat.restrictScalars.{u + 1}
        (q.trans (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm).toRingHom :=
  Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{u + 1, u} A)
    (ModuleCat.restrictScalarsComp'
      (q.trans (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm).toRingHom
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom q.toRingHom
      (by ext x; rfl)) ≪≫ (Functor.associator _ _ _).symm

attribute [local irreducible] transportedPresentation liftedRestriction

private def ordinaryConstants (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ) :
    let A := Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)
    let P := PbcQuotient (pbcIntegralDatum l E) n
    let φ := (adicLisseForget S).mapIso (asIso (residueLisseConstantComparison S d n))
    integralResidueQuotientLift l E d hd n ⋙
        constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ⋙
        finiteCoefficientRealization S P ⋙
        SheafOfModules.restrictScalars (finiteTransport S l E d c n).inv ≅
      (ModuleCat.uliftFunctor.{u + 1, u} A ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom ⋙
        koszulConstantFunctor S A) ⋙ SheafOfModules.restrictScalars φ.inv := by
  dsimp only
  let A := Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)
  let P := PbcQuotient (pbcIntegralDatum l E) n
  let q := (integralResidueQuotientEquiv l E d hd n).trans
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm
  let e := finiteTransport S l E d c n
  let φ := (adicLisseForget S).mapIso (asIso (residueLisseConstantComparison S d n))
  let L := ModuleCat.uliftFunctor.{u + 1, u} A ⋙
    ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom
  have := (koszulConstantUnit_local S A).1
  have := (koszulConstantUnit_local S A).2
  let t : ModuleCat.restrictScalars.{u + 1} q.toRingHom ⋙
        constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P) ⋙
        finiteCoefficientRealization S P ⋙ SheafOfModules.restrictScalars e.inv ≅
      koszulConstantFunctor S A ⋙ SheafOfModules.restrictScalars φ.inv := by
    simpa only [pbcAssociatedModule, finiteCoefficientRealization,
      constantPresentation, koszulConstantFunctor] using
      transportedPresentation S P (ULift.{u + 1} A) _ _ _
        (finiteCoefficientScalarMap S P) (koszulConstantUnit S A) q e φ
        (finiteTransport_constants S l E d hd c n)
  exact Functor.isoWhiskerRight
      (liftedRestriction A P (integralResidueQuotientEquiv l E d hd n)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L t ≪≫
    (Functor.associator _ _ _).symm

attribute [local irreducible] ordinaryConstants

/-- Normalized coefficient transport identifies the two constant complex realizations.
This is global on S; there is no morphism, chart, or perfectness hypothesis. -/
theorem integralResidueFiniteConstants
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ)
    (B : CochainComplex (ModuleCat.{u}
      (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1))) ℤ) :
    Nonempty
      (integralResidueFiniteModel S l E d c n
          ((finiteCoefficientRealization S
            (PbcQuotient (pbcIntegralDatum l E) n)).mapDerivedCategory.obj
              (DerivedCategory.Q.obj
                (((constantSheaf (ProEt.topology S)
                    (ModuleCat.{u + 1}
                      (PbcQuotient (pbcIntegralDatum l E) n))).mapHomologicalComplex (.up ℤ)).obj
                    (((integralResidueQuotientLift l E d hd n).mapHomologicalComplex
                      (.up ℤ)).obj B)))) ≅
        (completedAdicDerivedChange S (residueLisseConstantComparison S d n)).obj
          ((residueLisseDerivedConstant S
            (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1))).obj
              (DerivedCategory.Q.obj B))) := by
  let A := Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)
  let P := PbcQuotient (pbcIntegralDatum l E) n
  let e := finiteTransport S l E d c n
  let R := SheafOfModules.restrictScalars.{u + 1} e.inv
  have : R.IsEquivalence := WeilConjectures.restriction_isEquivalence e.symm
  let F := finiteCoefficientRealization S P
  let C := constantSheaf (ProEt.topology S) (ModuleCat.{u + 1} P)
  let K := (C.mapHomologicalComplex (.up ℤ)).obj
    (((integralResidueQuotientLift l E d hd n).mapHomologicalComplex (.up ℤ)).obj B)
  let M := F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  let j : R.mapDerivedCategory.obj M ≅ integralResidueFiniteModel S l E d c n M :=
    R.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      R.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  let φ := asIso (residueLisseConstantComparison S d n)
  let R₀ := pbcRestrict φ.inv
  let H := ModuleCat.uliftFunctor.{u + 1, u} A ⋙
    ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom ⋙ koszulConstantFunctor S A
  have : (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom).isRightAdjoint
  let i :
      (R.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
        (R₀.mapHomologicalComplex (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj B) :=
    _root_.HomologicalComplex.Hom.isoOfComponents
      (fun k ↦ (ordinaryConstants S l E d hd c n).app (B.X k))
      (fun k k' _ ↦ ((ordinaryConstants S l E d hd c n).hom.naturality (B.d k k')).symm)
  refine ⟨j.symm ≪≫ R.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
    R.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso i ≪≫
    (R₀.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (.up ℤ)).obj B)).symm ≪≫
    R₀.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app B).symm ≪≫ ?_⟩
  exact ((derivedChangeIso S φ).app
    ((residueLisseDerivedConstant S A).obj (DerivedCategory.Q.obj B))).symm

end AlgebraicGeometry.Scheme
