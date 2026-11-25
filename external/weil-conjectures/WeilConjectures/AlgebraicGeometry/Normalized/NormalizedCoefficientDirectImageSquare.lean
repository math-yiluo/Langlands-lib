/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.CategoryTheory.Exact.ExactRestrictionDerivedIdentityUnit
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientDirectImageRestrictionCube

/-! # Compatibility of normalized direct-image squares with coefficient presentations

## References

* Stacks Project, Cohomology on Sites, Tags 0D6D and 0D6E
* Stacks Project, together with the uniqueness of right derivation
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The canonical comparison for the source coefficient presentation. -/
def normalizedCoefficientSourceComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R₀ R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (b : R₀ ≅ R)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ RX)
    (F : pbcModules X RX ⥤ pbcModules Y R) [F.Additive]
    (hF : F = proEtaleRingModuleDirectImage f R RX cR) :
    F.rightDerivedFunctor ⋙ pbcDerivedRestrict b.hom ≅
      pbcDerivedRestrict
          (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso b ≪≫ cR).hom) ⋙
        DerivedScalarMate.push f R₀ := by
  subst F
  exact proEtaleRingRestrictionDerivedDirectImage f R₀ R
    (DerivedScalarMate.inverseRing f R₀) RX b.hom
    (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso b ≪≫ cR).hom)
    (Iso.refl _) cR (by simp)

/-- The canonical comparison between identified and literal target coefficients. -/
def normalizedCoefficientTargetComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (G : pbcModules X SX ⥤ pbcModules Y SY) [G.Additive]
    (hG : G = proEtaleRingModuleDirectImage f SY SX cS) :
    G.rightDerivedFunctor ≅ pbcDerivedRestrict cS.hom ⋙ DerivedScalarMate.push f SY := by
  subst G
  exact (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (coefficientDerivedRestrictIdentity SY).symm ≪≫
    proEtaleRingRestrictionDerivedDirectImage f SY SY
      (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom
      (Iso.refl _) cS (by simp)

private theorem coefficientComparison_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (RV SV : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
    (hc : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom) :
    CategoryTheory.ExactDerivedSquare.unitNormalized
      (proEtaleRingModuleDirectImage f SV SU cS)
      (proEtaleRingModuleDirectImage f RV RU cR)
      (pbcRestrict aU) (pbcRestrict aV)
      (pbcDerivedRestrict aU) (pbcDerivedRestrict aV)
      (pbcRestrict aU).mapDerivedCategoryFactors
      (pbcRestrict aV).mapDerivedCategoryFactors
      (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS hc).hom
      (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS hc).hom := by
  intro C
  exact (proEtaleRingRestrictionDerivedDirectImage_existsUnique
    f RV SV RU SU aV aU cR cS hc).choose_spec.1 C

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  proEtaleRingRestrictionDirectImage proEtaleRingRestrictionDerivedDirectImage
  pbcDerivedRestrictComp

/-- Changing the two coefficient presentations preserves the normalized restriction /
direct-image square. This theorem involves only exact scalar restrictions and right
derived direct images; it involves neither scalar extension nor its mate. -/
theorem normalizedCoefficientDirectImageSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R₀ R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (b : R₀ ≅ R)
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φY : R ⟶ SY) (φX : RX ⟶ SX)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ RX)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (hc : cR.hom ≫ φX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫ cS.hom)
    (F : pbcModules X RX ⥤ pbcModules Y R) [F.Additive]
    (hF : F = proEtaleRingModuleDirectImage f R RX cR)
    (G : pbcModules X SX ⥤ pbcModules Y SY) [G.Additive]
    (hG : G = proEtaleRingModuleDirectImage f SY SX cS)
    (i : pbcRestrict φX ⋙ F ≅ G ⋙ pbcRestrict φY)
    (hi : ∀ (M : pbcModules X SX) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (i.hom.app M).val.app U x)
        (fun x : ((proEtaleRingModuleDirectImage f SY SX cS).obj M).val.obj U ↦ x))
    (e : pbcDerivedRestrict φX ⋙ F.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ pbcDerivedRestrict φY)
    (he : ∀ C : CochainComplex (pbcModules X SX) ℤ,
      F.rightDerivedFunctorUnitQ
          (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).obj C) ≫
        F.rightDerivedFunctor.map
          ((pbcRestrict φX).mapDerivedCategoryFactors.inv.app C) ≫
        e.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex i.hom (.up ℤ)).app C) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        (pbcDerivedRestrict φY).map (G.rightDerivedFunctorUnitQ C)) :
    let χ := b.hom ≫ φY
    let q := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso b ≪≫ cR
    let hq : q.hom ≫ φX = DerivedScalarMate.inverseMap f χ ≫ cS.hom := by
      dsimp only [q, χ, Iso.trans_hom, Functor.mapIso_hom, DerivedScalarMate.inverseMap]
      rw [Category.assoc, hc, ← Category.assoc, ← Functor.map_comp]
    let k := derivedRestrictionSquare q.hom φX cS.hom
      (DerivedScalarMate.inverseMap f χ) hq
    let r := pbcDerivedRestrictComp b.hom φY χ rfl
    let p := normalizedCoefficientSourceComparison f R₀ R RX b cR F hF
    let z := normalizedCoefficientTargetComparison f SY SX cS G hG
    ∀ M : DerivedCategory (pbcModules X SX),
      (pbcDerivedRestrict b.hom).map (e.hom.app M) ≫
          r.hom.app (G.rightDerivedFunctor.obj M) ≫
          (pbcDerivedRestrict χ).map (z.hom.app M) =
        p.hom.app ((pbcDerivedRestrict φX).obj M) ≫
          (DerivedScalarMate.push f R₀).map (k.hom.app M) ≫
          (DerivedScalarMate.restrictionPush f χ).inv.app
            ((pbcDerivedRestrict cS.hom).obj M) := by
  subst F
  subst G
  dsimp only
  let χ := b.hom ≫ φY
  let q := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso b ≪≫ cR
  have hq : q.hom ≫ φX = DerivedScalarMate.inverseMap f χ ≫ cS.hom := by
    dsimp only [q, χ, Iso.trans_hom, Functor.mapIso_hom, DerivedScalarMate.inverseMap]
    rw [Category.assoc, hc, ← Category.assoc, ← Functor.map_comp]
  let H := proEtaleRingModuleDirectImage f R₀ (DerivedScalarMate.inverseRing f R₀)
    (Iso.refl _)
  let J := proEtaleRingModuleDirectImage f SY (DerivedScalarMate.inverseRing f SY)
    (Iso.refl _)
  let FR := proEtaleRingModuleDirectImage f R RX cR
  let GS := proEtaleRingModuleDirectImage f SY SX cS
  let cp := proEtaleRingRestrictionDirectImage f R₀ R
    (DerivedScalarMate.inverseRing f R₀) RX b.hom q.hom (Iso.refl _) cR (by simp [q])
  let dp := proEtaleRingRestrictionDerivedDirectImage f R₀ R
    (DerivedScalarMate.inverseRing f R₀) RX b.hom q.hom (Iso.refl _) cR (by simp [q])
  let cz := proEtaleRingRestrictionDirectImage f SY SY
    (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom (Iso.refl _) cS (by simp)
  let dz := proEtaleRingRestrictionDerivedDirectImage f SY SY
    (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom (Iso.refl _) cS (by simp)
  let cd := proEtaleRingRestrictionDirectImage f R₀ SY
    (DerivedScalarMate.inverseRing f R₀) (DerivedScalarMate.inverseRing f SY)
    χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _) (by simp)
  let dd := DerivedScalarMate.restrictionPush f χ
  let a := pbcRestrictComp q.hom φX (q.hom ≫ φX) rfl ≪≫
    (pbcRestrictComp (DerivedScalarMate.inverseMap f χ) cS.hom
      (q.hom ≫ φX) hq.symm).symm
  let d := pbcRestrictComp b.hom φY χ rfl ≪≫
    (pbcRestrictComp χ (𝟙 SY) χ (by simp)).symm
  have hn : CategoryTheory.ExactDerivedSquare.unitNormalized
      GS FR (pbcRestrict φX) (pbcRestrict φY)
      (pbcDerivedRestrict φX) (pbcDerivedRestrict φY)
      (pbcRestrict φX).mapDerivedCategoryFactors
      (pbcRestrict φY).mapDerivedCategoryFactors i.inv e.inv := by
    intro C
    exact invertNormalizedSquare FR.rightDerivedFunctor DerivedCategory.Q
      ((pbcRestrict φX).mapDerivedCategoryFactors.app C)
      ((NatIso.mapHomologicalComplex i.symm (.up ℤ)).app C)
      (e.app (DerivedCategory.Q.obj C))
      ((pbcRestrict φY).mapDerivedCategoryFactors.app
        ((GS.mapHomologicalComplex (.up ℤ)).obj C))
      (FR.rightDerivedFunctorUnitQ
        (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).obj C))
      ((pbcDerivedRestrict φY).map (GS.rightDerivedFunctorUnitQ C)) (he C)
  have hp := coefficientComparison_normalized f R₀ R
    (DerivedScalarMate.inverseRing f R₀) RX b.hom q.hom (Iso.refl _) cR (by simp [q])
  have hz := coefficientComparison_normalized f SY SY
    (DerivedScalarMate.inverseRing f SY) SX (𝟙 SY) cS.hom (Iso.refl _) cS (by simp)
  have hd := coefficientComparison_normalized f R₀ SY
    (DerivedScalarMate.inverseRing f R₀) (DerivedScalarMate.inverseRing f SY)
    χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _) (by simp)
  have hcubes := coefficientDirectImageRestrictionCube f R₀ R RX b SY SX φY φX
    cR cS hc i hi
  have cube := CategoryTheory.ExactDerivedSquare.normalized_cube
    GS FR (pbcRestrict φX) (pbcRestrict φY) H J
    (pbcRestrict q.hom) (pbcRestrict b.hom)
    (pbcRestrict cS.hom) (pbcRestrict (𝟙 SY))
    (pbcRestrict (DerivedScalarMate.inverseMap f χ)) (pbcRestrict χ)
    i.symm cp cz cd e.symm dp dz dd hn hp hz hd a d hcubes
  have ha : Functor.mapDerivedCategorySquareIso a =
      derivedRestrictionSquare q.hom φX cS.hom (DerivedScalarMate.inverseMap f χ) hq := by
    apply Iso.ext
    simp only [a, derivedRestrictionSquare, pbcDerivedRestrictComp,
      Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Category.assoc]
  have hdcomp : Functor.mapDerivedCategorySquareIso d =
      pbcDerivedRestrictComp b.hom φY χ rfl ≪≫
        (pbcDerivedRestrictComp χ (𝟙 SY) χ (by simp)).symm := by
    apply Iso.ext
    simp only [d, pbcDerivedRestrictComp, Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Category.assoc]
  have hid : ∀ M : DerivedCategory (pbcModules Y SY),
      (pbcDerivedRestrictComp χ (𝟙 SY) χ (by simp)).inv.app M =
        (pbcDerivedRestrict χ).map ((coefficientDerivedRestrictIdentity SY).inv.app M) := by
    intro M
    have hh := exactRestrictionDerivedIdentityUnit (pbcRestrict χ) (pbcRestrict (𝟙 SY))
      (coefficientRestrictIdentity Y SY) (pbcRestrictComp χ (𝟙 SY) χ (by simp))
      (by
        intro N
        ext U x
        exact restrictionComp_apply χ (𝟙 SY) χ (by simp) N U x) M
    have hh' : (pbcDerivedRestrictComp χ (𝟙 SY) χ (by simp)).hom.app M =
        (pbcDerivedRestrict χ).map ((coefficientDerivedRestrictIdentity SY).hom.app M) := by
      simpa only [pbcDerivedRestrictComp, pbcDerivedRestrict,
        coefficientDerivedRestrictIdentity] using hh
    apply (cancel_epi ((pbcDerivedRestrictComp χ (𝟙 SY) χ (by simp)).hom.app M)).mp
    rw [Iso.hom_inv_id_app, hh', ← Functor.map_comp, Iso.hom_inv_id_app]
    exact ((pbcDerivedRestrict χ).map_id
      ((pbcDerivedRestrict (𝟙 SY)).obj M)).symm
  intro M
  have h := cube M
  rw [ha, hdcomp] at h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at h
  rw [hid] at h
  apply (cancel_mono (dd.hom.app ((pbcDerivedRestrict cS.hom).obj M))).mp
  dsimp only [dd]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  have h' := congrArg (fun t ↦ (pbcDerivedRestrict b.hom).map (e.hom.app M) ≫ t) h
  dsimp only [pbcDerivedRestrict] at h'
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h'
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h'
  simpa only [normalizedCoefficientSourceComparison, normalizedCoefficientTargetComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    Functor.map_comp, Category.assoc, χ, q, dp, dz, dd, FR, GS, H, J,
    pbcDerivedRestrict, DerivedScalarMate.push, proEtaleRingDerivedDirectImage] using h'.symm

end AlgebraicGeometry.Scheme
