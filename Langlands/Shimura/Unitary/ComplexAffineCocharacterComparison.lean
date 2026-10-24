import Langlands.GroupScheme.AffineTestComparison
import Langlands.Shimura.Unitary.ComplexAffineCocharacter

set_option maxHeartbeats 100000
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct Classical

namespace Langlands.GroupScheme.Gm
universe u

/-- Relative evaluation on the base ring has the identity-test underlying morphism. -/
theorem relativeAffineUnitPoint_self_left (R : Type u) [CommRing R] (v : Rˣ) :
    (relativeAffineUnitPoint R R v).left =
      ((affinePointsEquiv (𝟙 (Spec (CommRingCat.of R)))).symm v).left :=
  specIdentityTestIso_unit_left (CommRingCat.of R) v

end Langlands.GroupScheme.Gm

namespace Langlands.GroupScheme
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Projected affine evaluation of a composite cocharacter, with explicit composition. -/
theorem affineCocharacterValue_comp_left
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (H : GroupScheme (Spec (CommRingCat.of S)))
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶ H)
    (e : H ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (v : Sˣ) :
    (G.affineCocharacterValue (χ ≫ e) v).left =
      ((((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm v).left ≫
        χ.hom.hom.left) ≫ e.hom.hom.left) ≫
        Limits.pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [affineCocharacterValue_left, Grp.comp_hom_hom, Over.comp_left, ← Category.assoc]

end Langlands.GroupScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (T : Type) [CommRing T] [Algebra ℂ T]

/-- Relative affine cocharacter evaluation as a homomorphism of point groups. -/
def complexAffineCocharacterValueHom
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme) :
    Tˣ →* ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X) :=
  ((GroupScheme.pointsMap χ).app
      (op ((algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T))))).hom.comp
    (GroupScheme.Gm.affinePointsEquiv
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ T)))).symm.toMonoidHom

omit [IsScalarTower E K A] in
/-- The bundled map has the existing affine evaluation as its underlying function. -/
theorem complexAffineCocharacterValueHom_apply
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (v : Tˣ) :
    D.complexAffineCocharacterValueHom T χ v = D.complexAffineCocharacterValue T χ v := rfl

omit [IsScalarTower E K A] in
/-- Underlying scheme map of the direct-model cocharacter evaluation. -/
theorem complexCocharacterValue_left
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (v : ℂˣ) :
    (D.complexCocharacterValue χ v).left =
      ((((GroupScheme.Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of ℂ)))).symm v).left ≫
        χ.hom.hom.left) ≫ D.complexDirectGroupSchemeIso.hom.hom.hom.left) ≫
        Limits.pullback.fst D.rationalGroupScheme.X.hom rationalComplexBaseMap :=
  GroupScheme.affineCocharacterValue_comp_left D.rationalGroupScheme
    D.complexRationalGroupScheme χ D.complexDirectGroupSchemeIso.hom v

omit [IsScalarTower E K A] in
/-- Underlying map of relative affine cocharacter evaluation. -/
theorem complexAffineCocharacterValue_left
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (v : Tˣ) :
    (D.complexAffineCocharacterValue T χ v).left =
      (GroupScheme.Gm.relativeAffineUnitPoint ℂ T v).left ≫ χ.hom.hom.left := rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsScalarTower E K A] in
/-- Projection of affine cocharacter evaluation agrees with the identity-test evaluation. -/
theorem complexAffineCocharacterValue_rational
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (v : ℂˣ) :
    D.complexAffineRationalPoint ℂ (D.complexAffineCocharacterValue ℂ χ v) =
      D.complexCocharacterValue χ v := by
  apply Over.OverMorphism.ext
  rw [D.complexAffineRationalPoint_left, D.complexAffineCocharacterValue_left,
    D.complexCocharacterValue_left, GroupScheme.Gm.relativeAffineUnitPoint_self_left]
  simp only [Category.assoc, D.complexDirectGroupSchemeIso_hom_fst]

/-- Embedding-labelled matrix weights of the actual cocharacter value. -/
theorem harrisCocharacter_embedding_matrices (hΦ : IsCMSection E K Φ)
    (first : Bool) (u : ℂˣ) (p : (E →+* ℝ) × Bool) :
    D.complexEmbeddingPointMatrices C hΦ
        (D.complexCocharacterValue (D.harrisCocharacter C first) u) (cmFactorEmbedding Φ p) =
      if p.2 then
        (ComplexMatrix.splitDiagonal ℂ n (if p.1 = C.distinguished then n - 1 else n)
          (if first then ((u : ℂ), 1) else (1, (u : ℂ)))).1
      else
        (ComplexMatrix.splitDiagonal ℂ n (if p.1 = C.distinguished then n - 1 else n)
          (if first then ((u : ℂ), 1) else (1, (u : ℂ)))).2 := by
  rw [← D.complexAffineCocharacterValue_rational,
    D.complexEmbeddingPointMatrices_affine,
    D.harrisCocharacter_affine_matrices]

end Langlands.Shimura.CentralSimpleUnitaryData

