/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison

/-! # Finite inverse image and normalized slice isomorphisms

## References

* Bhatt--Scholze, Section 6.5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- An isomorphism after finite inverse image gives an isomorphism on the actual slice.
There are no constant-complex or perfectness hypotheses. -/
theorem integralResidueFiniteSlice
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) (n : ℕ) (Y : S.Etale)
    (M N : FiniteCoefficientDerivedCategory S (PbcQuotient (pbcIntegralDatum l E) n))
    (e : Nonempty
      ((finiteCoefficientDerivedPullback S (PbcQuotient (pbcIntegralDatum l E) n)
          Y.hom).obj M ≅
        (finiteCoefficientDerivedPullback S (PbcQuotient (pbcIntegralDatum l E) n)
          Y.hom).obj N)) :
    Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
          ((toProEt S).obj Y) (integralResidueFiniteModel S l E d c n M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n)
          ((toProEt S).obj Y) (integralResidueFiniteModel S l E d c n N)) := by
  let D := pbcIntegralDatum l E
  let B := PbcQuotient D n
  let U := (toProEt S).obj Y
  let R := D.finiteRing S n
  let RY := D.finiteRing Y.left n
  let a := AdicCoefficients.finiteRingComparison S B
  let aY := AdicCoefficients.finiteRingComparison Y.left B
  let T := SheafOfModules.restrictScalars a.hom
  let TY := SheafOfModules.restrictScalars aY.hom
  let := WeilConjectures.restriction_isEquivalence a
  let := WeilConjectures.restriction_isEquivalence aY
  let b := integralDetailedLevelComparison S l E n ≪≫ c.finite n
  let H := SheafOfModules.restrictScalars b.inv
  have : H.IsEquivalence := WeilConjectures.restriction_isEquivalence b.symm
  let V := SheafOfModules.overFunctor (completedAdicFiniteRing S d n) U
  have : V.Additive := (ringedOverFunctor_exactGeneral _ U).1
  have : PreservesFiniteLimits V := (ringedOverFunctor_exactGeneral _ U).2.1
  have : PreservesFiniteColimits V := (ringedOverFunctor_exactGeneral _ U).2.2
  let W := SheafOfModules.overFunctor ((adicLisseForget S).obj R) U
  have : W.Additive := (ringedOverFunctor_exactGeneral _ U).1
  have : PreservesFiniteLimits W := (ringedOverFunctor_exactGeneral _ U).2.1
  have : PreservesFiniteColimits W := (ringedOverFunctor_exactGeneral _ U).2.2
  let J := SheafOfModules.restrictScalars
    (((ProEt.topology S).overPullback RingCat.{u + 1} U).mapIso b.symm).hom
  let := WeilConjectures.restriction_isEquivalence
    (((ProEt.topology S).overPullback RingCat.{u + 1} U).mapIso b.symm)
  let scalar : H ⋙ V ≅ W ⋙ J := Iso.refl _
  let swap : H.mapDerivedCategory ⋙ V.mapDerivedCategory ≅
      W.mapDerivedCategory ⋙ J.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso H V ≪≫
      Functor.mapDerivedCategoryNatIso scalar ≪≫
      (Functor.mapDerivedCategoryCompIso W J).symm
  let p := finiteFunctionDerivedPullback Y.hom D n
  obtain ⟨e⟩ := e
  let h : (D.finitePull Y.hom n).obj (T.mapDerivedCategory.obj M) ≅
      (D.finitePull Y.hom n).obj (T.mapDerivedCategory.obj N) :=
    p.app M ≪≫ TY.mapDerivedCategory.mapIso e ≪≫ (p.app N).symm
  let Z := pbcDerivedRestrict (D.finiteRingIso Y.hom n).inv
  have : Z.IsEquivalence := derivedRestrictIso_isEquivalence (D.finiteRingIso Y.hom n).symm
  let raw := adicTowerPullback Y.hom R
  let r := rawPullbackNormalized Y.hom R RY (D.finiteRingIso Y.hom n)
  let hraw : raw.obj (T.mapDerivedCategory.obj M) ≅
      raw.obj (T.mapDerivedCategory.obj N) :=
    Z.preimageIso (r.app (T.mapDerivedCategory.obj M) ≪≫ h ≪≫
      (r.app (T.mapDerivedCategory.obj N)).symm)
  obtain ⟨q, ⟨hq⟩⟩ := chartDerivedEquivalence U R
  let hs : W.mapDerivedCategory.obj (T.mapDerivedCategory.obj M) ≅
      W.mapDerivedCategory.obj (T.mapDerivedCategory.obj N) :=
    (hq.app (T.mapDerivedCategory.obj M)).symm ≪≫ q.functor.mapIso hraw ≪≫
      hq.app (T.mapDerivedCategory.obj N)
  have model (K : FiniteCoefficientDerivedCategory S B) :
      integralResidueFiniteModel S l E d c n K ≅
        H.mapDerivedCategory.obj (T.mapDerivedCategory.obj K) := by
    let F := SheafOfModules.restrictScalars (a.symm ≪≫ b).inv
    have : F.IsEquivalence := WeilConjectures.restriction_isEquivalence (a.symm ≪≫ b).symm
    let f : F ≅ T ⋙ H := Iso.refl _
    exact (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K) ≪≫
      (Functor.mapDerivedCategoryNatIso f ≪≫ (Functor.mapDerivedCategoryCompIso T H).symm).app K
  have slice (K : DerivedCategory (SheafOfModules.{u + 1}
      (completedAdicFiniteRing S d n))) :
      ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d n) U K ≅
        V.mapDerivedCategory.obj K :=
    (V.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
      V.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)
  exact ⟨slice _ ≪≫ V.mapDerivedCategory.mapIso (model M) ≪≫
    swap.app (T.mapDerivedCategory.obj M) ≪≫ J.mapDerivedCategory.mapIso hs ≪≫
    (swap.app (T.mapDerivedCategory.obj N)).symm ≪≫
    V.mapDerivedCategory.mapIso (model N).symm ≪≫ (slice _).symm⟩

end AlgebraicGeometry.Scheme
