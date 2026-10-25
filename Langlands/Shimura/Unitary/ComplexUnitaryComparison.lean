import Langlands.Shimura.Unitary.ComplexUnitarySplitting
import Langlands.Shimura.Unitary.GaloisCocharacters

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual iterated complex unitary pullback agrees with direct rational pullback. -/
def complexDirectUnitaryGroupSchemeIso :
    D.complexRationalUnitaryGroupScheme ≅ D.rationalUnitaryBaseChange rationalComplexBaseMap :=
  (GroupScheme.baseChangeCompIso (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ)
    DeligneTorus.complexBaseMap D.rationalUnitaryGroupScheme).symm ≪≫
      eqToIso (congrArg (fun b => D.rationalUnitaryBaseChange b) rationalComplexBaseMap_tower)

/-- The actual direct complex unitary pullback is split by the Harris signature charts. -/
def directComplexUnitaryGroupSchemeIso :
    D.rationalUnitaryBaseChange rationalComplexBaseMap ≅ D.complexSplitUnitaryGroupScheme :=
  D.complexDirectUnitaryGroupSchemeIso.symm ≪≫ D.complexUnitaryGroupSchemeIso C

/-- The rational unitary inclusion pulled back successively to R and C. -/
def complexUnitaryInclusion : D.complexRationalUnitaryGroupScheme ⟶
    D.complexRationalGroupScheme :=
  (GroupScheme.baseChange DeligneTorus.complexBaseMap).map
    ((GroupScheme.baseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ)).map
      D.rationalUnitaryInclusion)

omit [IsScalarTower E K A] in
/-- The scalar-extension model comparisons commute with the actual unitary inclusion. -/
theorem complexUnitaryModelIso_inclusion :
    D.complexUnitaryModelIso.hom ≫
      AlgebraInvolution.SchemeModel.baseChangedUnitaryInclusion
        (D.rationalBasis.baseChange ℝ) (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)
          DeligneTorus.complexBaseMap =
      D.complexUnitaryInclusion ≫
        (GroupScheme.baseChange DeligneTorus.complexBaseMap).map D.realGroupSchemeIso.hom := by
  simpa only [complexUnitaryModelIso, Functor.mapIso_hom, complexUnitaryInclusion,
    AlgebraInvolution.SchemeModel.baseChangedUnitaryInclusion, rationalUnitaryInclusion,
    realGroupSchemeIso, AlgebraInvolution.SchemeModel.realScalarExtensionIso,
    Functor.map_comp] using
    congrArg ((GroupScheme.baseChange DeligneTorus.complexBaseMap).map)
      (AlgebraInvolution.SchemeModel.scalarExtensionIso_unitaryInclusion ℝ D.rationalBasis
        D.toSecondKindInvolution.rationalInvolution)

/-- Including a complex unitary point preserves its matrices and adds multiplier one. -/
theorem complexUnitaryInclusion_points (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) :
    D.complexGroupPointsEquiv C T (x ≫ D.complexUnitaryInclusion.hom.hom) =
      (D.complexUnitaryPointsEquiv C T x, 1) := by
  have hi :
      (x ≫ D.complexUnitaryInclusion.hom.hom) ≫
        ((GroupScheme.baseChange DeligneTorus.complexBaseMap).map
          D.realGroupSchemeIso.hom).hom.hom =
      (x ≫ D.complexUnitaryModelIso.hom.hom.hom) ≫
        (AlgebraInvolution.SchemeModel.baseChangedUnitaryInclusion
          (D.rationalBasis.baseChange ℝ)
          (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)
          DeligneTorus.complexBaseMap).hom.hom := by
    have h := congrArg (fun f => x ≫ f.hom.hom) D.complexUnitaryModelIso_inclusion
    simpa only [Grp.comp_hom_hom, Category.assoc] using h.symm
  change C.iteratedScalarGroupSplitting D.totallyRealBasis _
    (AlgebraInvolution.SchemeModel.baseChangedPointsEquiv _ _ _ T
      ((x ≫ D.complexUnitaryInclusion.hom.hom) ≫
        ((GroupScheme.baseChange DeligneTorus.complexBaseMap).map
          D.realGroupSchemeIso.hom).hom.hom)) = _
  rw [hi, ← AlgebraInvolution.SchemeModel.baseChangedUnitaryInclusion_points]
  exact C.iteratedScalarUnitarySplitting_inclusion D.totallyRealBasis
    (AlgebraInvolution.complexTestAlgebra T) (D.complexUnitaryAlgebraPointsEquiv T x)

end Langlands.Shimura.CentralSimpleUnitaryData
