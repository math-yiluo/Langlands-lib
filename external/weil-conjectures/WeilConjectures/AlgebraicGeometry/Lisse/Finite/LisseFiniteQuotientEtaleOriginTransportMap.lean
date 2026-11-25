/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import all WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-! # The comparison morphism for finite quotient origin transport

## References

* Stacks Project, Tags 09AL, 09B1 and 09C6, transporting `K_n = epsilon^(-1) L_n` along a supplied
  local constant model
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] FiniteQuotientOriginProof.scalar_additive
  FiniteQuotientOriginProof.relative_additive FiniteQuotientOriginProof.scalar_equivalence
  FiniteQuotientOriginProof.relative_equivalence

private def targetEncodingIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))) :
    (relativeRestriction f (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory.obj
      ((pbcDerivedRestrict ((adicTowerInverseImage f).map
        (pbcLevelConstantComparison X d n).hom)).obj
        ((adicTowerPullback f ((pbcAdicRings X d).obj (op n))).obj K)) ≅
      (finiteQuotientOriginPullback f d n).obj K := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let e := pbcLevelConstantComparison X d n
  let c := proEtaleRingRestrictionDerivedPullback f _ _
    ((adicTowerInverseImage f).obj _) ((adicTowerInverseImage f).obj _)
    e.hom ((adicTowerInverseImage f).map e.hom) (Iso.refl _) (Iso.refl _) (by simp)
  exact (relativeRestriction f B).mapDerivedCategory.mapIso (c.app K) ≪≫
    FiniteQuotientOriginProof.fixedPullbackIso f B ((pbcDerivedRestrict e.hom).obj K)

private def constantEncodingIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))) :
    (finiteQuotientOriginEncoding X (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory.obj
      ((pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom).obj
        ((constantAdicQuotientModules X d n).mapDerivedCategory.obj E)) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1}
        (A ⧸ d.ideal ^ (n + 1)))).mapDerivedCategory.obj
          ((ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)).mapDerivedCategory.obj
            E) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let Q := ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)
  let L := adicLisseConstantModules X B
  have : L.Additive := CompletedConstantReduction.constant_additive X B
  have : PreservesFiniteLimits L := (constantAdicFinite_constant_exact X B).1
  have : PreservesFiniteColimits L := (constantAdicFinite_constant_exact X B).2
  let R := pbcRestrict (pbcLevelConstantComparison X d n).hom
  let S := scalarRestriction X B
  let F := constantAdicQuotientModules X d n
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcLevelConstantComparison X d n))
  let e0 : (F ⋙ R) ⋙ S ≅ Q ⋙ constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} B) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Q ⋙ L) e.counitIso) S ≪≫
      Functor.isoWhiskerLeft Q (constantEncodingNatIso X B).symm
  exact (Functor.mapDerivedCategoryCompIso R S).app (F.mapDerivedCategory.obj E) ≪≫
    (Functor.mapDerivedCategoryCompIso F (R ⋙ S)).app E ≪≫
      (Functor.mapDerivedCategoryNatIso e0).app E ≪≫
        ((Functor.mapDerivedCategoryCompIso Q _).app E).symm

/-- A constant model on an étale chart gives an isomorphism to the actual pullback
of `K`, hence a morphism which is monic and epic.
-/
theorem lisse_finite_quotient_etale_origin_transport_map
    {X Y : Scheme.{u}} {g : Y ⟶ X}
    {A : Type (u + 1)} [CommRing A] {d : AdicCoefficientDatum A} {n : ℕ}
    {K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    {V : Y.Etale}
    (C : LisseFiniteQuotientEtaleOriginCore X Y g d n K V)
    (Z : V.left.Etale)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (hE : Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj
        C.level ≅ (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj E))
    (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))) :
    ∃ f : (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ⟶
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj K,
      Mono f ∧ Epi f := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let Q := ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)
  let QV := Sheaf.restrictScalars V.left.smallEtaleTopology (constantAdicQuotientMap d.ideal n)
  let QZ := Sheaf.restrictScalars Z.left.smallEtaleTopology (constantAdicQuotientMap d.ideal n)
  let UZ := AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) Z.hom
  let FV := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) V.left
  let FZ := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Z.left
  let t : W.left ⟶ Z.left := _w.left
  have ht : t ≫ Z.hom ≫ V.hom = W.hom := _w.w
  let h := t ≫ Z.hom
  let H := ProEtale.upperStar (ModuleCat.{u + 1} B) h
  let T := ProEtale.upperStar (ModuleCat.{u + 1} B) t
  let PZ := ProEtale.upperStar (ModuleCat.{u + 1} B) Z.hom
  let PG := ProEtale.upperStar (ModuleCat.{u + 1} B) (V.hom ≫ g)
  let PE := ProEtale.upperStar (ModuleCat.{u + 1} B) (W.hom ≫ g)
  obtain ⟨eE⟩ := hE
  obtain ⟨eC⟩ := C.comparison
  let eQ := Functor.mapDerivedCategoryCompIso QV UZ ≪≫
    Functor.mapDerivedCategoryNatIso
      (AlgebraicGeometry.Etale.upperStarRestrictScalarsIsoSheaf
        (constantAdicQuotientMap d.ideal n) Z.hom) ≪≫
      (Functor.mapDerivedCategoryCompIso (AlgebraicGeometry.Etale.upperStar _ Z.hom) QZ).symm
  let eConst := Functor.mapDerivedCategoryCompIso
      (constantSheaf Z.left.smallEtaleTopology _) QZ ≪≫
    Functor.mapDerivedCategoryNatIso
      (constantCommuteCompose Z.left.smallEtaleTopology Q) ≪≫
      (Functor.mapDerivedCategoryCompIso Q (constantSheaf Z.left.smallEtaleTopology _)).symm
  let eZ := eQ.app C.level ≪≫ QZ.mapDerivedCategory.mapIso eE ≪≫ eConst.app E
  let eCompare := Functor.mapDerivedCategoryCompIso UZ FZ ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) Z.hom).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV PZ).symm
  let eFConst := Functor.mapDerivedCategoryCompIso
      (constantSheaf Z.left.smallEtaleTopology _) FZ ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} B) Z.left)
  let eTConst := Functor.mapDerivedCategoryCompIso
      (constantSheaf (ProEt.topology Z.left) _) T ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} B) t)
  let eH := (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} B) t Z.hom)).app
        (FV.mapDerivedCategory.obj (QV.mapDerivedCategory.obj C.level)) ≪≫
    ((Functor.mapDerivedCategoryCompIso PZ T).app _).symm
  let eModel := eH ≪≫
    T.mapDerivedCategory.mapIso ((eCompare.app (QV.mapDerivedCategory.obj C.level)).symm ≪≫
      FZ.mapDerivedCategory.mapIso eZ ≪≫ eFConst.app (Q.mapDerivedCategory.obj E)) ≪≫
    eTConst.app (Q.mapDerivedCategory.obj E)
  have hcomp : h ≫ (V.hom ≫ g) = W.hom ≫ g := by
    dsimp [h]
    rw [Category.assoc, ← ht]
    simp only [Category.assoc]
  let J := (finiteQuotientOriginEncoding X B).mapDerivedCategory.obj
    ((pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom).obj K)
  let ePull := (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarCongr (ModuleCat.{u + 1} B) hcomp.symm)).app J ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} B) h (V.hom ≫ g))).app J ≪≫
    ((Functor.mapDerivedCategoryCompIso PG H).app J).symm
  let eTarget := ePull ≪≫ H.mapDerivedCategory.mapIso eC.symm ≪≫ eModel
  let R := pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
    (pbcLevelConstantComparison X d n).hom)
  let S := relativeRestriction (W.hom ≫ g) B
  have : R.IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence W.left ((adicLisseForget W.left).mapIso
      ((adicTowerInverseImage (W.hom ≫ g)).mapIso
        (pbcLevelConstantComparison X d n)))).functor.IsEquivalence
  let D := R.mapDerivedCategory ⋙ S.mapDerivedCategory
  let eSource := targetEncodingIso (W.hom ≫ g) d n
      ((constantAdicQuotientModules X d n).mapDerivedCategory.obj E) ≪≫
    PE.mapDerivedCategory.mapIso (constantEncodingIso X d n E) ≪≫
    (Functor.mapDerivedCategoryCompIso (constantSheaf (ProEt.topology X) _) PE).app
      (Q.mapDerivedCategory.obj E) ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} B) (W.hom ≫ g))).app
      (Q.mapDerivedCategory.obj E)
  let eEncoded := eSource ≪≫ eTarget.symm ≪≫ (targetEncodingIso (W.hom ≫ g) d n K).symm
  let e := (Functor.FullyFaithful.ofFullyFaithful D).preimageIso eEncoded
  exact ⟨e.hom, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
