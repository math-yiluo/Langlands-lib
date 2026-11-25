/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantDerivedScalarFactorization
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Scalar tensor carries the output of the source completion reflector to a complete object.

## References

* Stacks Project, Tags 099B and 0A0E
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

private theorem scalarComplete_levelConstant_hom (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison W d n).hom =
      AdicCoefficients.constantComparison W (A ⧸ d.ideal ^ (n + 1)) := by
  let := d.quotientFinite
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings W d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison W d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b

private theorem scalarComplete_levelConstant_scalar (W : Scheme.{u}) (n : ℕ) :
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (pbcScalarQuotientMap l E F i n)) ≫
        (pbcLevelConstantComparison W (pbcIntegralDatum l F) n).hom =
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) := by
  rw [scalarComplete_levelConstant_hom, scalarComplete_levelConstant_hom]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1

private theorem scalarComplete_quotientScalar_square (W : Scheme.{u}) (n : ℕ) :
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (pbcScalarQuotientMap l E F i n)) ≫
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (integralCoefficientULift l F n).toCommRingCatIso.hom =
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
      integralScalarQuotientSheafMap l E F i W n := by
  let C := constantSheaf (ProEt.topology W) CommRingCat.{u + 1}
  change C.map _ ≫ C.map _ = C.map _ ≫ C.map _
  rw [← C.map_comp, ← C.map_comp]
  apply congrArg C.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change integralCoefficientULift l F n
      (pbcScalarQuotientMap l E F i n (Ideal.Quotient.mk _ x)) = _
  rw [show pbcScalarQuotientMap l E F i n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (ULift.up (integralScalarIntegerInclusion l E F i x.down)) from rfl]
  have hqL (z : PbcIntegralRing l F) :
      integralCoefficientULift l F n (Ideal.Quotient.mk _ z) =
        ULift.up (Ideal.Quotient.mk _ z.down) :=
    (integralCoefficientULift_exists l F n).exists.choose_spec z
  have hqE (z : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ z) =
        ULift.up (Ideal.Quotient.mk _ z.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec z
  rw [hqL]
  change ULift.up _ = ULift.up
    (integralScalarQuotientMap l E F i n
      ((integralCoefficientULift l E n (Ideal.Quotient.mk _ x)).down))
  rw [hqE]
  rfl

private theorem scalarComplete_detailedLevel_scalar (W : Scheme.{u}) (n : ℕ) :
    (adicLisseForget W).map
        (AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n)) ≫
      (integralDetailedLevelComparison W l F n).hom =
    (integralDetailedLevelComparison W l E n).hom ≫
      (adicLisseForget W).map (integralScalarQuotientSheafMap l E F i W n) := by
  let FC := adicLisseForget W
  let C := constantSheaf (ProEt.topology W) CommRingCat.{u + 1}
  let eE := pbcLevelConstantComparison W (pbcIntegralDatum l E) n
  let eL := pbcLevelConstantComparison W (pbcIntegralDatum l F) n
  have hc : AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) ≫
        eL.inv = eE.inv ≫ C.map (CommRingCat.ofHom (pbcScalarQuotientMap l E F i n)) := by
    apply (Iso.comp_inv_eq eL).mpr
    rw [Category.assoc]
    exact ((Iso.inv_comp_eq eE).mpr (scalarComplete_levelConstant_scalar l E F i W n)).symm
  change FC.map _ ≫ FC.map (eL.inv ≫ C.map _) =
    FC.map (eE.inv ≫ C.map _) ≫ FC.map _
  simp only [← FC.map_comp]
  apply congrArg FC.map
  rw [← Category.assoc, hc, Category.assoc, scalarComplete_quotientScalar_square l E F i W n,
    ← Category.assoc]

private theorem scalarComplete_coefficientScalar_square (W : Scheme.{u}) :
    (purCoefficientIso l E W).hom ≫ integralCompletedScalarMap l E F i W =
      pbcScalarCoefficientMap l E F i W ≫ (purCoefficientIso l F W).hom := by
  let FC := adicLisseForget W
  have hp (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (n : ℕ) :
      FC.map (purCoefficientIso l A W).hom ≫
          limit.π (integralCoefficientSheafSystem l A W) (Opposite.op n) =
        FC.map (pbcAdicProjection W (pbcIntegralDatum l A) n) ≫
          (integralDetailedLevelComparison W l A n).hom := by
    have h := congrArg Iso.hom (purCoefficientIso_existsUnique l A W).exists.choose_spec
    change FC.map (purCoefficientIso l A W).hom =
      (integralDetailedCoefficientComparison W l A).hom at h
    rw [h]
    exact (integralDetailedCoefficientComparison_exists W l A).exists.choose_spec n
  apply FC.map_injective
  apply limit.hom_ext
  intro n
  change (FC.map (purCoefficientIso l E W).hom ≫
      FC.map (integralCompletedScalarMap l E F i W)) ≫ limit.π _ n =
    (FC.map (pbcScalarCoefficientMap l E F i W) ≫
      FC.map (purCoefficientIso l F W).hom) ≫ limit.π _ n
  have hg := congrArg FC.map
    ((integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec n.unop)
  change FC.map (integralCompletedScalarMap l E F i W) ≫ limit.π _ n =
    FC.map (integralScalarRho l E F i W n.unop) at hg
  have hf := congrArg FC.map
    ((pbcScalarCoefficientMap_exists l E F i W).exists.choose_spec n.unop)
  simp only [FC.map_comp] at hf
  change FC.map (pbcScalarCoefficientMap l E F i W) ≫ FC.map (pbcAdicProjection W
      (pbcIntegralDatum l F) n.unop) = _ at hf
  rw [Category.assoc, Category.assoc, hg, hp F n.unop]
  rw [← Category.assoc, hf, Category.assoc, scalarComplete_detailedLevel_scalar l E F i W n.unop]
  change FC.map (purCoefficientIso l E W).hom ≫
      FC.map (completedIntegralCommRingProjectionUnrestricted l E W n.unop ≫
        integralScalarQuotientSheafMap l E F i W n.unop) = _
  rw [FC.map_comp, ← Category.assoc]
  change (FC.map (purCoefficientIso l E W).hom ≫
      limit.π (integralCoefficientSheafSystem l E W) n) ≫ FC.map _ = _
  rw [hp E n.unop, Category.assoc]

private noncomputable def scalarComplete_model (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙ (purCoefficientModel l F W).functor ≅
      (purCoefficientModel l E W).functor ⋙ completedDerivedScalarExtension l E F i W := by
  let eR := purCoefficientIso l E W
  let eS := purCoefficientIso l F W
  have hmap : integralCompletedScalarMap l E F i W =
      WeilConjectures.completedCoefficientMap l E F i W := by
    apply (completedCoefficientMap_existsUnique l E F i W).unique
    · exact (integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec
  have hsq := scalarComplete_coefficientScalar_square l E F i W
  rw [hmap] at hsq
  change eR.hom ≫ WeilConjectures.completedCoefficientMap l E F i W =
    pbcScalarCoefficientMap l E F i W ≫ eS.hom at hsq
  have hinv : WeilConjectures.completedCoefficientMap l E F i W ≫ eS.inv =
      eR.inv ≫ pbcScalarCoefficientMap l E F i W := by
    apply (Iso.comp_inv_eq eS).mpr
    rw [Category.assoc]
    exact ((Iso.inv_comp_eq eR).mpr hsq.symm).symm
  exact (coefficientExtensionIso eR.symm eS.symm
    (WeilConjectures.completedCoefficientMap l E F i W)
    (pbcScalarCoefficientMap l E F i W) hinv).symm

/-- Scalar tensor carries the output of the source completion reflector to a complete object. -/
theorem pbcScalarCompletedObjectComplete (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) := by
  let M := (pbcActualCompletion (pbcIntegralDatum l E) W).obj K
  have hM : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) M :=
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))).leftAdjoint.obj
      K).property
  have hc : IsDerivedCompleteUnrestricted l E W
      ((purCoefficientModel l E W).functor.obj M) :=
    (purCoefficientModel_predicates l E W M).1.mp hM
  have htarget := ((finiteFreeCompletedScalarComparison l E F i W).2.1 _ hc).2
  apply (purCoefficientModel_predicates l F W _).2.mpr
  apply complete_of_iso l F W ((scalarComplete_model l E F i W).app M).symm
  obtain ⟨D, hl, htarget⟩ := htarget
  exact (sfDerivedComplete_iff_legacy l F W D hl _).mpr htarget

end AlgebraicGeometry.Scheme
