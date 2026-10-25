import Langlands.Shimura.Unitary.ComplexGroupPoints
import Langlands.GroupScheme.GeneralLinearProduct

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura

private def kernelEquivOfProduct {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G →* H) (e : G ≃* J × H) (he : ∀ x, (e x).2 = f x) : f.ker ≃* J where
  toFun x := (e x.val).1
  invFun y := ⟨e.symm (y, 1), by
    change f (e.symm (y, 1)) = 1
    rw [← he, e.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact ((he x.val).trans x.property).symm
  right_inv y := congrArg Prod.fst (e.apply_symm_apply (y, 1))
  map_mul' x y := congrArg Prod.fst (e.map_mul x.val y.val)

namespace HarrisSignatureCharts

universe u v w z s
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {κ : Type z} [Fintype κ] (b : Module.Basis κ E A)
  (S : Type s) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The multiplier-one part of the actual complex splitting consists of the GL factors. -/
def iteratedScalarUnitarySplitting :
    ((σ.rationalInvolution.baseChange ℝ).baseChange S).unitary ≃*
      ((E →+* ℝ) → (Matrix (Fin n) (Fin n) S)ˣ) :=
  ((σ.rationalInvolution.baseChange ℝ).baseChange S).unitaryEquivKernel.trans
    (kernelEquivOfProduct _ (C.iteratedScalarGroupSplitting b S)
      (C.iteratedScalarGroupSplitting_multiplier b S))

/-- Unitary coordinates are the selected matrices in the existing scalar algebra splitting. -/
@[simp] theorem iteratedScalarUnitarySplitting_matrix
    (x : ((σ.rationalInvolution.baseChange ℝ).baseChange S).unitary) (τ : E →+* ℝ) :
    ((C.iteratedScalarUnitarySplitting b S x τ) : Matrix (Fin n) (Fin n) S) =
      (C.iteratedScalarMatrixEquiv b S (x.val : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ).1 := rfl

/-- Including a unitary element adds exactly the scalar coordinate one. -/
theorem iteratedScalarUnitarySplitting_inclusion
    (x : ((σ.rationalInvolution.baseChange ℝ).baseChange S).unitary) :
    C.iteratedScalarGroupSplitting b S
      (((σ.rationalInvolution.baseChange ℝ).baseChange S).unitaryInclusion x) =
        (C.iteratedScalarUnitarySplitting b S x, 1) := by
  apply Prod.ext
  · rfl
  · rw [C.iteratedScalarGroupSplitting_multiplier]
    rfl

end HarrisSignatureCharts

namespace CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual rational unitary group, pulled back first to R and then to C. -/
abbrev complexRationalUnitaryGroupScheme : GroupScheme (Spec (CommRingCat.of ℂ)) :=
  (GroupScheme.baseChange DeligneTorus.complexBaseMap).obj
    (D.rationalUnitaryBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ))

/-- The real unitary model comparison, pulled back along Spec(C) to Spec(R). -/
def complexUnitaryModelIso :
    D.complexRationalUnitaryGroupScheme ≅
      (GroupScheme.baseChange DeligneTorus.complexBaseMap).obj
        (AlgebraInvolution.SchemeModel.unitaryGroupScheme (D.rationalBasis.baseChange ℝ)
          (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)) :=
  (GroupScheme.baseChange DeligneTorus.complexBaseMap).mapIso
    (AlgebraInvolution.SchemeModel.scalarExtensionUnitaryIso ℝ D.rationalBasis
      D.toSecondKindInvolution.rationalInvolution)

/-- All complex test-scheme points are unitary elements in the actual iterated scalar algebra. -/
def complexUnitaryAlgebraPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ D.complexRationalUnitaryGroupScheme.X) ≃*
      ((D.toSecondKindInvolution.rationalInvolution.baseChange ℝ).baseChange
        (AlgebraInvolution.complexTestAlgebra T)).unitary :=
  (((yonedaGrp.mapIso D.complexUnitaryModelIso).app (op T)).groupIsoToMulEquiv).trans
    (AlgebraInvolution.SchemeModel.baseChangedUnitaryPointsEquiv
      (D.rationalBasis.baseChange ℝ)
      (D.toSecondKindInvolution.rationalInvolution.baseChange ℝ)
      DeligneTorus.complexBaseMap T)

omit [IsScalarTower E K A] in
/-- Restriction of unitary points is the tensor coefficient map. -/
theorem complexUnitaryAlgebraPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) :
    (D.complexUnitaryAlgebraPointsEquiv T' (a ≫ x)).val =
      Units.map (AlgebraInvolution.changeCoefficients (A := ℝ ⊗[ℚ] A)
        ((AlgebraInvolution.complexTestAlgebraMap a).restrictScalars ℝ)).toMonoidHom
          (D.complexUnitaryAlgebraPointsEquiv T x).val := by
  change (AlgebraInvolution.SchemeModel.baseChangedUnitaryPointsEquiv _ _ _ T'
    ((a ≫ x) ≫ D.complexUnitaryModelIso.hom.hom.hom)).val = _
  rw [Category.assoc, AlgebraInvolution.SchemeModel.baseChangedUnitaryPointsEquiv_naturality]
  rfl

/-- The actual complex unitary points are one general linear matrix at each real place. -/
def complexUnitaryPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ D.complexRationalUnitaryGroupScheme.X) ≃*
      ((E →+* ℝ) → (Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))ˣ) :=
  (D.complexUnitaryAlgebraPointsEquiv T).trans
    (C.iteratedScalarUnitarySplitting D.totallyRealBasis (AlgebraInvolution.complexTestAlgebra T))

/-- Restriction of the unitary coordinates is entrywise restriction of invertible matrices. -/
theorem complexUnitaryPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) :
    D.complexUnitaryPointsEquiv C T' (a ≫ x) = fun τ =>
      Matrix.GeneralLinearGroup.map a.left.appTop.hom
        (D.complexUnitaryPointsEquiv C T x τ) := by
  funext τ
  apply Units.ext
  change (C.iteratedScalarMatrixEquiv D.totallyRealBasis _
    ((D.complexUnitaryAlgebraPointsEquiv T' (a ≫ x)).val :
      (AlgebraInvolution.complexTestAlgebra T') ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ).1 = _
  rw [D.complexUnitaryAlgebraPointsEquiv_naturality]
  exact congrArg (fun p => (p τ).1)
    (C.iteratedScalarMatrixEquiv_natural D.totallyRealBasis
      (AlgebraInvolution.complexTestAlgebraMap a)
        ((D.complexUnitaryAlgebraPointsEquiv T x).val :
          (AlgebraInvolution.complexTestAlgebra T) ⊗[ℝ] (ℝ ⊗[ℚ] A)))

/-- The split unitary group scheme has GL factors and no multiplier factor. -/
abbrev complexSplitUnitaryGroupScheme (_D : CentralSimpleUnitaryData E K A n) :
    GroupScheme (Spec (CommRingCat.of ℂ)) :=
  GroupScheme.pi fun _ : E →+* ℝ =>
    GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of ℂ)

/-- The point equivalence to the actual finite product scheme. -/
def complexUnitarySplitPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ D.complexRationalUnitaryGroupScheme.X) ≃*
      (T ⟶ D.complexSplitUnitaryGroupScheme.X) :=
  (D.complexUnitaryPointsEquiv C T).trans
    ((GroupScheme.piPointsEquiv
      (fun _ : E →+* ℝ => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of ℂ)) T).trans
      (MulEquiv.piCongrRight fun _ : E →+* ℝ =>
        GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T)).symm

/-- The comparison preserves the selected unitary matrix at each real place. -/
theorem complexUnitarySplitPointsEquiv_coordinates
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) (τ : E →+* ℝ) :
    GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T
      (GroupScheme.piPointsEquiv _ T (D.complexUnitarySplitPointsEquiv C T x) τ) =
        D.complexUnitaryPointsEquiv C T x τ := by
  exact congrFun
    (((GroupScheme.piPointsEquiv
      (fun _ : E →+* ℝ =>
        GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of ℂ)) T).trans
      (MulEquiv.piCongrRight fun _ : E →+* ℝ =>
        GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T)).apply_symm_apply
      (D.complexUnitaryPointsEquiv C T x)) τ

/-- The unitary comparison is natural for all complex test schemes. -/
theorem complexUnitarySplitPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) :
    D.complexUnitarySplitPointsEquiv C T' (a ≫ x) =
      a ≫ D.complexUnitarySplitPointsEquiv C T x := by
  apply (GroupScheme.piPointsEquiv _ T').injective
  funext τ
  apply (GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T').injective
  rw [complexUnitarySplitPointsEquiv_coordinates, GroupScheme.piPointsEquiv_naturality]
  rw [GroupScheme.GeneralLinear.pointsEquiv_naturality,
    complexUnitarySplitPointsEquiv_coordinates]
  exact congrFun (D.complexUnitaryPointsEquiv_naturality C a x) τ

/-- The actual complex unitary group scheme is the finite product of GL_n factors. -/
def complexUnitaryGroupSchemeIso :
    D.complexRationalUnitaryGroupScheme ≅ D.complexSplitUnitaryGroupScheme :=
  GroupScheme.isoOfPoints (D.complexUnitarySplitPointsEquiv C)
    (D.complexUnitarySplitPointsEquiv_naturality C)

/-- The scheme isomorphism realizes the established unitary matrix coordinates. -/
theorem complexUnitaryGroupSchemeIso_hom_points
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ D.complexRationalUnitaryGroupScheme.X) (τ : E →+* ℝ) :
    GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T
      (GroupScheme.piPointsEquiv _ T
        (x ≫ (D.complexUnitaryGroupSchemeIso C).hom.hom.hom) τ) =
          D.complexUnitaryPointsEquiv C T x τ := by
  rw [complexUnitaryGroupSchemeIso, GroupScheme.comp_isoOfPoints_hom]
  exact D.complexUnitarySplitPointsEquiv_coordinates C T x τ

/-- The inverse scheme morphism recovers the prescribed GL matrices at all real places. -/
theorem complexUnitaryGroupSchemeIso_inv_points
    (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ D.complexSplitUnitaryGroupScheme.X) (τ : E →+* ℝ) :
    D.complexUnitaryPointsEquiv C T
      (y ≫ (D.complexUnitaryGroupSchemeIso C).inv.hom.hom) τ =
        GroupScheme.GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of ℂ) T
          (GroupScheme.piPointsEquiv _ T y τ) := by
  rw [complexUnitaryGroupSchemeIso, GroupScheme.comp_isoOfPoints_inv]
  have h := D.complexUnitarySplitPointsEquiv_coordinates C T
    ((D.complexUnitarySplitPointsEquiv C T).symm y) τ
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

end CentralSimpleUnitaryData
end Langlands.Shimura
