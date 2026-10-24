import Langlands.Shimura.Unitary.AffinePointRestriction
import Langlands.Shimura.Unitary.GaloisCocharacters

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
private theorem compositionComparison_fst {B S U : Scheme} (b : S ⟶ B) (c : U ⟶ S)
    (d : U ⟶ B) (h : c ≫ b = d) (G : GroupScheme B) :
    ((baseChangeCompIso b c G).symm ≪≫
      eqToIso (congrArg (fun k => (Over.pullback k).mapGrp.obj G) h)).hom.hom.hom.left ≫
        Limits.pullback.fst G.X.hom d =
      Limits.pullback.fst (Limits.pullback.snd G.X.hom b) c ≫
        Limits.pullback.fst G.X.hom b := by
  subst d
  change ((baseChangeCompIso b c G).inv.hom.hom.left ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id, baseChangeCompIso_inv_fst]

end Langlands.GroupScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

open AlgebraInvolution.SchemeModel

variable (T : Type) [CommRing T] [Algebra ℂ T] [Algebra ℝ T] [Algebra ℚ T]
  [IsScalarTower ℝ ℂ T] [IsScalarTower ℚ ℝ T] [IsScalarTower ℚ ℂ T]

/-- Project a complex affine point to the real pullback, identifying the affine test scheme. -/
def complexAffineRealPoint
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    (algSpec (CommRingCat.of ℝ)).obj (op (CommAlgCat.of ℝ T)) ⟶
      (D.rationalBaseChange (scalarBaseMap ℚ ℝ)).X :=
  (restrictedAffineTestIso ℝ ℂ T).inv ≫
    GroupScheme.baseChangePointsEquiv DeligneTorus.complexBaseMap
      (D.rationalBaseChange (scalarBaseMap ℚ ℝ)) _ x

/-- Project through both scalar extensions to the original rational affine point. -/
def complexAffineRationalPoint
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    (algSpec (CommRingCat.of ℚ)).obj (op (CommAlgCat.of ℚ T)) ⟶
      D.rationalGroupScheme.X :=
  originalAffinePoint D.rationalBasis D.toSecondKindInvolution.rationalInvolution
    (D.complexAffineRealPoint T x)

omit [IsScalarTower E K A] [Algebra ℚ T] [IsScalarTower ℚ ℝ T] [IsScalarTower ℚ ℂ T] in
theorem complexAffineRealPoint_left
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    (D.complexAffineRealPoint T x).left =
      x.left ≫ Limits.pullback.fst
        (D.rationalBaseChange (scalarBaseMap ℚ ℝ)).X.hom DeligneTorus.complexBaseMap := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

omit [IsScalarTower E K A] [IsScalarTower ℚ ℂ T] in
theorem complexAffineRationalPoint_left
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    (D.complexAffineRationalPoint T x).left =
      (x.left ≫ Limits.pullback.fst
        (D.rationalBaseChange (scalarBaseMap ℚ ℝ)).X.hom DeligneTorus.complexBaseMap) ≫
          Limits.pullback.fst D.rationalGroupScheme.X.hom (scalarBaseMap ℚ ℝ) := by
  rw [complexAffineRationalPoint, originalAffinePoint_left, complexAffineRealPoint_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsScalarTower E K A] in
/-- The canonical direct-pullback comparison preserves projection to the rational group. -/
theorem complexDirectGroupSchemeIso_hom_fst :
    D.complexDirectGroupSchemeIso.hom.hom.hom.left ≫
        Limits.pullback.fst D.rationalGroupScheme.X.hom rationalComplexBaseMap =
      Limits.pullback.fst (D.rationalBaseChange (scalarBaseMap ℚ ℝ)).X.hom
          DeligneTorus.complexBaseMap ≫
        Limits.pullback.fst D.rationalGroupScheme.X.hom (scalarBaseMap ℚ ℝ) := by
  exact GroupScheme.compositionComparison_fst (scalarBaseMap ℚ ℝ)
    DeligneTorus.complexBaseMap rationalComplexBaseMap rationalComplexBaseMap_tower
    D.rationalGroupScheme

omit [IsScalarTower E K A] in
/-- Direct and iterated pullbacks give the same original rational affine point. -/
theorem complexAffineRationalPoint_direct
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    D.complexAffineRationalPoint T x =
      originalAffinePoint D.rationalBasis D.toSecondKindInvolution.rationalInvolution
        (x ≫ D.complexDirectGroupSchemeIso.hom.hom.hom) := by
  apply Over.OverMorphism.ext
  rw [complexAffineRationalPoint_left, originalAffinePoint_left, Over.comp_left]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => x.left ≫ f) D.complexDirectGroupSchemeIso_hom_fst).symm.trans
      (Category.assoc _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
omit [IsScalarTower E K A] [Algebra ℚ T] [IsScalarTower ℚ ℝ T] [IsScalarTower ℚ ℂ T] in
/-- The real algebra model comparison commutes with affine projection from the complex pullback. -/
theorem complexAffineRealPoint_comparison
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    originalAffinePoint (D.rationalBasis.baseChange ℝ)
        (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)
        (x ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
          D.realGroupSchemeIso.hom).hom.hom) =
      D.complexAffineRealPoint T x ≫ D.realGroupSchemeIso.hom.hom.hom := by
  have h := GroupScheme.baseChangePointsEquiv_comp DeligneTorus.complexBaseMap
    D.realGroupSchemeIso.hom _ x
  exact (congrArg (fun k => (restrictedAffineTestIso ℝ ℂ T).inv ≫ k) h).trans
    (Category.assoc _ _ _).symm

/-- Affine similitude coordinates in the real algebra model after complex scalar extension. -/
def complexAffineSimilitudes
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    ((D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).baseChange T).similitudes :=
  baseChangedAffinePointsEquiv (S := ℂ) T (D.rationalBasis.baseChange ℝ)
    (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)
    (x ≫ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.map
      D.realGroupSchemeIso.hom).hom.hom)

omit [IsScalarTower E K A] [IsScalarTower ℚ ℂ T] in
/-- The actual iterated affine coordinates are tensor expansion of the rational coordinates. -/
theorem complexAffineSimilitudes_tower
    (x : (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :
    D.complexAffineSimilitudes T x =
      AlgebraInvolution.baseChangeTowerSimilitudes ℝ T
        D.toSecondKindInvolution.rationalInvolution
        (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ T)
          (D.complexAffineRationalPoint T x)) := by
  rw [complexAffineSimilitudes, baseChangedAffinePointsEquiv_eq_originalAffinePoint,
    complexAffineRealPoint_comparison]
  exact scalarExtensionIso_originalAffinePoints D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution (D.complexAffineRealPoint T x)

end Langlands.Shimura.CentralSimpleUnitaryData
