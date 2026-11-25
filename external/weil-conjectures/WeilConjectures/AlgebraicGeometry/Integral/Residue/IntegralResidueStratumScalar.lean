/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumInput
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

/-! # Scalar normalization on a residue stratum

## References

* Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1)
* Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.8(1), Proposition 6.6.11
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem residueScalar_direct {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exchangeScalar d Y ≫ proEtaleRingDirectImageMap f
        (d.completedRing Y) (d.completedRing X) (d.integralRingIso f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (exchangeScalar d X) := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have h := congrArg (fun z ↦ (adj.homEquiv _ _) z) (exchangeScalar_comm d f)
  rw [adj.homEquiv_naturality_left] at h
  rw [adj.homEquiv_naturality_right] at h
  change _ = _ at h
  have hc : (adj.homEquiv _ _) (exchangeConstantIso f A).hom =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hc] at h
  exact h.symm

private theorem residueScalar_sections {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app V ≫
        (exchangeScalar d Y).hom.app V ≫
        (proEtaleRingDirectImageMap f (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso f)).hom.app V =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
          ((proEtaleBaseChange f).op.obj V) ≫
            (exchangeScalar d X).hom.app ((proEtaleBaseChange f).op.obj V) := by
  have h := congrArg (fun z ↦ z.hom.app V) (residueScalar_direct d f)
  have hc := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of A)))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hcV := congrArg (fun z ↦ z.app V) hc
  change (toSheafify _ _).app V ≫
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom.app V =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
          ((proEtaleBaseChange f).op.obj V) at hcV
  change (exchangeScalar d Y).hom.app V ≫
      (proEtaleRingDirectImageMap f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f)).hom.app V =
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom.app V ≫
      (exchangeScalar d X).hom.app ((proEtaleBaseChange f).op.obj V) at h
  rw [h, ← Category.assoc, hcV]

private theorem residueScalar_sameSite
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u})
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) :
    exchangeScalar (pbcIntegralDatum l E) S ≫
        (WeilConjectures.purCoefficientIso l E S).hom ≫ c.completed.inv =
      completedAdicScalar S d := by
  let D := pbcIntegralDatum l E
  let A := PbcIntegralRing l E
  let F := adicLisseForget S
  let C := constantSheaf (ProEt.topology S) CommRingCat.{u + 1}
  have hp (n : ℕ) :
      F.map (WeilConjectures.purCoefficientIso l E S).hom ≫
          limit.π (WeilConjectures.integralCoefficientSheafSystem l E S) (op n) =
        F.map (pbcAdicProjection S D n) ≫ (integralDetailedLevelComparison S l E n).hom := by
    have h := congrArg Iso.hom
      (WeilConjectures.purCoefficientIso_existsUnique l E S).exists.choose_spec
    change F.map (WeilConjectures.purCoefficientIso l E S).hom =
      (integralDetailedCoefficientComparison S l E).hom at h
    exact (congrArg (fun z ↦ z ≫
      limit.π (WeilConjectures.integralCoefficientSheafSystem l E S) (op n)) h).trans
        ((integralDetailedCoefficientComparison_exists S l E).exists.choose_spec n)
  have hs (n : ℕ) : exchangeScalar D S ≫ pbcAdicProjection S D n =
      C.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison S D n).hom := by
    dsimp only [exchangeScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists S
      { toCompleteCoefficientDatum := D.toCompleteCoefficientDatum,
        quotientFinite := D.quotientFinite }).exists.choose_spec n]
    rfl
  have hq (n : ℕ) :
      F.map (exchangeScalar D S) ≫ F.map (WeilConjectures.purCoefficientIso l E S).hom ≫
          limit.π (WeilConjectures.integralCoefficientSheafSystem l E S) (op n) =
        F.map (C.map (CommRingCat.ofHom
          ((integralCoefficientULift l E n).toRingHom.comp
            (Ideal.Quotient.mk (D.ideal ^ (n + 1)))))) := by
    refine (congrArg (fun z ↦ F.map (exchangeScalar D S) ≫ z) (hp n)).trans ?_
    calc
      _ = F.map (exchangeScalar D S ≫ pbcAdicProjection S D n) ≫
          (integralDetailedLevelComparison S l E n).hom := by
        exact (Category.assoc (F.map (exchangeScalar D S))
          (F.map (pbcAdicProjection S D n))
          (integralDetailedLevelComparison S l E n).hom).symm.trans
            (congrArg (fun z ↦ z ≫ (integralDetailedLevelComparison S l E n).hom)
              (F.map_comp (exchangeScalar D S) (pbcAdicProjection S D n)).symm)
      _ = F.map (C.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison S D n).hom) ≫
          (integralDetailedLevelComparison S l E n).hom :=
        congrArg (fun z ↦ F.map z ≫ (integralDetailedLevelComparison S l E n).hom) (hs n)
      _ = _ := by
        let k := pbcLevelConstantComparison S D n
        let q := CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal ^ (n + 1)))
        let e := (integralCoefficientULift l E n).toCommRingCatIso
        change F.map (C.map q ≫ k.hom) ≫ F.map (k.inv ≫ C.map e.hom) = _
        calc
          _ = F.map ((C.map q ≫ k.hom) ≫ (k.inv ≫ C.map e.hom)) :=
            (F.map_comp _ _).symm
          _ = F.map (C.map q ≫ C.map e.hom) :=
            congrArg F.map (by simp only [Category.assoc, Iso.hom_inv_id_assoc])
          _ = F.map (C.map (q ≫ e.hom)) := congrArg F.map (C.map_comp q e.hom).symm
          _ = _ := rfl
  have hc (n : ℕ) : F.map c.completed.inv ≫ completedAdicProjection S d n =
      limit.π (WeilConjectures.integralCoefficientSheafSystem l E S) (op n) ≫
        (c.finite n).hom := by
    have h := c.completed_projection n
    change F.map c.completed.hom ≫
      limit.π (WeilConjectures.integralCoefficientSheafSystem l E S) (op n) ≫
        (c.finite n).hom = completedAdicProjection S d n at h
    rw [← h]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [F.map_id]
    simp only [Category.id_comp]
  apply F.map_injective
  apply limit.hom_ext (F := completedAdicRingSystem S d)
  intro n
  change F.map ((exchangeScalar D S ≫
      (WeilConjectures.purCoefficientIso l E S).hom ≫ c.completed.inv) ≫
        completedAdicCommProjection S d n.unop) =
    F.map (completedAdicScalar S d ≫ completedAdicCommProjection S d n.unop)
  apply congrArg F.map
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology S) _ _
    (completedAdicFiniteCommRing S d n.unop).property
  ext U a
  let f := (integralCoefficientULift l E n.unop).toRingHom.comp
    (Ideal.Quotient.mk (D.ideal ^ (n.unop + 1)))
  have hm : F.map (exchangeScalar D S ≫
      (WeilConjectures.purCoefficientIso l E S).hom ≫ c.completed.inv) ≫
        completedAdicProjection S d n.unop =
      F.map (C.map (CommRingCat.ofHom f)) ≫ (c.finite n.unop).hom := by
    simpa only [Functor.map_comp, Category.assoc, hc] using
      congrArg (fun z ↦ z ≫ (c.finite n.unop).hom) (hq n.unop)
  have hu : (F.map (C.map (CommRingCat.ofHom f))).hom.app U
        ((adicLisseConstantUnit S A).app U a) =
      (adicLisseConstantUnit S
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n.unop + 1)))).app U
        (ULift.up (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal l E (n.unop + 1)) a.down)) := by
    have h := congrArg (fun k ↦ (k.app U).hom a)
      (toSheafify_naturality (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).map (CommRingCat.ofHom f))).symm
    change (F.map (C.map (CommRingCat.ofHom f))).hom.app U
      ((adicLisseConstantUnit S A).app U a) =
        (adicLisseConstantUnit S _).app U (f a) at h
    change _ = (adicLisseConstantUnit S _).app U
      (integralCoefficientULift l E n.unop (Ideal.Quotient.mk _ a)) at h
    have ha : integralCoefficientULift l E n.unop (Ideal.Quotient.mk _ a) =
        ULift.up (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal l E (n.unop + 1)) a.down) :=
      (integralCoefficientULift_exists l E n.unop).exists.choose_spec a
    exact h.trans (congrArg (fun b ↦ (adicLisseConstantUnit S _).app U b) ha)
  have h := congrArg
    (fun k ↦ k.hom.app U ((adicLisseConstantUnit S A).app U a)) hm
  change _ = (c.finite n.unop).hom.hom.app U
    ((F.map (C.map (CommRingCat.ofHom f))).hom.app U
      ((adicLisseConstantUnit S A).app U a)) at h
  rw [hu] at h
  exact h.trans ((c.finite_constants n.unop U a.down).trans
    ((completedAdicScalar_exists S d).exists.choose_spec n.unop U a).symm)

/-- The normalized stratum comparison carries every constant integral scalar to itself. -/
theorem integralResidueStratum_scalar
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (g : S ⟶ T)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (_hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S)
    (V : T.ProEtᵒᵖ) (a : PbcIntegralRing l E) :
    (integralResidueStratumCoefficient T l E S g d c).hom.hom.app
        ((proEtaleBaseChange g).op.obj V)
      ((proEtaleRingDirectImageMap g (pbcAdicCompletion T (pbcIntegralDatum l E))
          ((adicTowerInverseImage g).obj (pbcAdicCompletion T (pbcIntegralDatum l E)))
          (Iso.refl _)).hom.app V
        ((exchangeScalar (pbcIntegralDatum l E) T).hom.app V
          ((adicLisseConstantUnit T (PbcIntegralRing l E)).app V a))) =
      (completedAdicScalar S d).hom.app ((proEtaleBaseChange g).op.obj V)
        ((adicLisseConstantUnit S (PbcIntegralRing l E)).app
          ((proEtaleBaseChange g).op.obj V) a) := by
  let D := pbcIntegralDatum l E
  let A := PbcIntegralRing l E
  let R := pbcAdicCompletion T D
  let R' := (adicTowerInverseImage g).obj R
  let α := D.integralRingIso g
  let V' := (proEtaleBaseChange g).op.obj V
  let x := (exchangeScalar D T).hom.app V ((adicLisseConstantUnit T A).app V a)
  have hh : proEtaleRingDirectImageMap g R R' (Iso.refl _) ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map α.hom =
    proEtaleRingDirectImageMap g R (D.completedRing S) α := by
    dsimp only [proEtaleRingDirectImageMap, Iso.refl_hom]
    rw [(proEtaleSheafDirectImage g CommRingCat.{u + 1}).map_id]
    exact congrArg (fun z ↦ z ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map α.hom)
        (Category.comp_id ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R))
  have hr := congrArg (fun q ↦ q.hom.app V x) hh
  change α.hom.hom.app V'
      ((proEtaleRingDirectImageMap g R R' (Iso.refl _)).hom.app V x) =
    (proEtaleRingDirectImageMap g R (D.completedRing S) α).hom.app V x at hr
  have hs := congrArg (fun q ↦ q.hom a) (residueScalar_sections D g V)
  change (proEtaleRingDirectImageMap g R (D.completedRing S) α).hom.app V x =
    (exchangeScalar D S).hom.app V' ((adicLisseConstantUnit S A).app V' a) at hs
  have hn := congrArg
    (fun q ↦ q.hom.app V' ((adicLisseConstantUnit S A).app V' a))
    (residueScalar_sameSite l E S d c)
  change c.completed.inv.hom.app V'
      ((WeilConjectures.purCoefficientIso l E S).hom.hom.app V'
        (α.hom.hom.app V'
          ((proEtaleRingDirectImageMap g R R' (Iso.refl _)).hom.app V x))) = _
  exact (congrArg (fun b ↦ c.completed.inv.hom.app V'
      ((WeilConjectures.purCoefficientIso l E S).hom.hom.app V' b)) (hr.trans hs)).trans hn

end AlgebraicGeometry.Scheme
