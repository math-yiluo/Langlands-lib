/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Scalar restriction of consecutive constant quotient realizations

This is the coefficient comparison substep of the consecutive quotient
realization argument.  It contains no tower model or supplied model
isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- Consecutive constant quotient realization commutes with derived restriction.

Source: Stacks Project, proetale.tex, Tags 0D6D and 03Q3, scalar comparison
for consecutive quotient coefficients.  The proof pastes the canonical
constant quotient scalar comparison at the two levels with the derived
constant realization scalar extension comparison; the quotient maps are
identified by completion evaluation.  This statement is the coefficient-only
part of the realization reduction and does not use an adic tower.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-scalar-reduction).
-/
theorem constantAdicQuotient_realization_scalar_reduction
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) (W : Y.Etale) (_w : W.left)
    (E' : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1)))) :
    let q : (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1)) →+*
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right
        (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
        (Nat.le_succ (n + 1)))
    let Rn := constantAdicQuotientRealization (W.hom ≫ g) d n
    let Rnp := constantAdicQuotientRealization (W.hom ≫ g) d (n + 1)
    let T := pbcDerivedExtend ((adicTowerInverseImage (W.hom ≫ g)).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    Nonempty (Rn.obj ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension q).obj E') ≅
      T.obj (Rnp.obj E')) := by
  let h := W.hom ≫ g
  let J := d.ideal.map (algebraMap A (AdicCompletion d.ideal A))
  let q := Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J)
    (Nat.le_succ (n + 1)))
  let r := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  let Qp := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (constantAdicQuotientMap d.ideal (n + 1))
  let Qn := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (constantAdicQuotientMap d.ideal n)
  let Cp := adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1 + 1))
  let Cn := adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))
  let ep := pbcLevelConstantComparison X d (n + 1)
  let en := pbcLevelConstantComparison X d n
  let Bp := pbcRestrict ep.inv
  let Bn := pbcRestrict en.inv
  let a := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom r)
  let c := pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)
  let b := (adicTowerInverseImage h).map c
  let Pp := adicTowerPullback h ((pbcAdicRings X d).obj (op (n + 1)))
  let Pn := adicTowerPullback h ((pbcAdicRings X d).obj (op n))
  have : Cp.Additive := CompletedConstantReduction.constant_additive X _
  have : Cn.Additive := CompletedConstantReduction.constant_additive X _
  have : PreservesFiniteLimits Cp := (constantAdicFinite_constant_exact X _).1
  have : PreservesFiniteColimits Cp := (constantAdicFinite_constant_exact X _).2
  have : PreservesFiniteLimits Cn := (constantAdicFinite_constant_exact X _).1
  have : PreservesFiniteColimits Cn := (constantAdicFinite_constant_exact X _).2
  let eqp := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal (n + 1))
    (quotient_map_bijective d.ideal d.finitelyGenerated (n + 1))
  let eqn := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : Qp.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars eqp.toRingHom).IsEquivalence
  have : Qn.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars eqn.toRingHom).IsEquivalence
  have : Bp.IsEquivalence := inferInstanceAs
    (proEtaleScalarEquivalence X ((adicLisseForget X).mapIso ep.symm)).functor.IsEquivalence
  have : Bn.IsEquivalence := inferInstanceAs
    (proEtaleScalarEquivalence X ((adicLisseForget X).mapIso en.symm)).functor.IsEquivalence
  -- The algebraic coefficient square commutes on quotient representatives.
  have hq : q.comp (constantAdicQuotientMap d.ideal (n + 1)) =
      (constantAdicQuotientMap d.ideal n).comp r := by
    ext x
    rfl
  let k₁ : ModuleCat.restrictScalars q ⋙ Qp ≅ Qn ⋙ ModuleCat.restrictScalars r :=
    (ModuleCat.restrictScalarsComp _ _).symm ≪≫
      ModuleCat.restrictScalarsComp' r (constantAdicQuotientMap d.ideal n) _ hq
  let a₀ := ConstantScalarRealization.moduleDerivedAdjunction q
  let a₁ := ConstantScalarRealization.moduleDerivedAdjunction r
  let a₂ := ConstantScalarRealization.derivedAdjunction (ProEt.topology X) r
  let a₃ := pbcDerivedScalarAdjunction c
  have hm₁ := isIso_inverseMate_of_equivalences a₀ a₁
    (Functor.mapDerivedCategorySquareIso k₁)
  let m₁ := asIso ((mateEquiv a₀ a₁).symm
    (Functor.mapDerivedCategorySquareIso k₁).hom)
  -- Exact constant realization has an invertible scalar mate.
  let k₂ := (ConstantScalarRealization.restrictionIso (ProEt.topology X) r).symm
  have hm₂ := constant_square_mate_isIso X r
  let m₂ := asIso ((mateEquiv a₁ a₂).symm
    (Functor.mapDerivedCategorySquareIso k₂).hom)
  -- Naturality of the finite coefficient comparison gives the third square.
  have hn : a ≫ en.hom = ep.hom ≫ c := by
    simpa only [a, r, en, ep, c, adicLisseRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ, pbcAdicQuotient] using
      pbcConstantSystemComparison_naturality X d (homOfLE (Nat.le_succ n)).op
  have he : ep.inv ≫ a = c ≫ en.inv := by
    apply (cancel_mono en.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let k₃ : pbcRestrict a ⋙ Bp ≅ Bn ⋙ pbcRestrict c :=
    pbcRestrictComp ep.inv a (c ≫ en.inv) he ≪≫
      (pbcRestrictComp c en.inv (c ≫ en.inv) rfl).symm
  have hm₃ : IsIso ((mateEquiv a₂ a₃).symm
      (Functor.mapDerivedCategorySquareIso k₃).hom) :=
    isIso_inverseMate_of_equivalences a₂ a₃ (Functor.mapDerivedCategorySquareIso k₃)
  let m₃ := asIso ((mateEquiv a₂ a₃).symm
    (Functor.mapDerivedCategorySquareIso k₃).hom)
  -- Inverse image commutes with scalar extension by the ring-sheaf-change mate.
  let k₄ := proEtaleRingRestrictionDerivedPullback h
    ((pbcAdicRings X d).obj (op (n + 1))) ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage h).obj ((pbcAdicRings X d).obj (op (n + 1))))
    ((adicTowerInverseImage h).obj ((pbcAdicRings X d).obj (op n)))
    c b (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hm₄ := inverseImage_mate_isIso h c
  let m₄ := asIso ((mateEquiv a₃ (pbcDerivedScalarAdjunction b)).symm k₄.inv)
  -- Expand the exact realizations and compose the four mate isomorphisms.
  let fn := (Functor.mapDerivedCategoryCompIso Qn (Cn ⋙ Bn)).symm ≪≫
    Functor.isoWhiskerLeft Qn.mapDerivedCategory (Functor.mapDerivedCategoryCompIso Cn Bn).symm
  let fp := (Functor.mapDerivedCategoryCompIso Qp (Cp ⋙ Bp)).symm ≪≫
    Functor.isoWhiskerLeft Qp.mapDerivedCategory (Functor.mapDerivedCategoryCompIso Cp Bp).symm
  exact ⟨Pn.mapIso (fn.app ((ConstantScalarRealization.moduleDerivedExtension q).obj E')) ≪≫
    Pn.mapIso (Bn.mapDerivedCategory.mapIso
      (Cn.mapDerivedCategory.mapIso (m₁.symm.app E'))) ≪≫
    Pn.mapIso (Bn.mapDerivedCategory.mapIso (m₂.symm.app (Qp.mapDerivedCategory.obj E'))) ≪≫
    Pn.mapIso (m₃.symm.app (Cp.mapDerivedCategory.obj (Qp.mapDerivedCategory.obj E'))) ≪≫
    m₄.symm.app (Bp.mapDerivedCategory.obj
      (Cp.mapDerivedCategory.obj (Qp.mapDerivedCategory.obj E'))) ≪≫
    (pbcDerivedExtend b).mapIso (Pp.mapIso (fp.symm.app E'))⟩

end AlgebraicGeometry.Scheme
