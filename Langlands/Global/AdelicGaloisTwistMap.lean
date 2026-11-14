import Langlands.Global.AdeleGaloisAction
import Langlands.Global.AdelicGaloisBorelTwisting

/-! # The Galois automorphism of upper-field adelic points of a scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical identification of the adelic Weil points with upper adelic points. -/
abbrev weilAdelicEquiv :
    AdelicGroupPoints F (W F L G) ≃ₜ* AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) :=
  AdelicWeilRestriction.adelicPointsContinuousEquiv F L (AffineWeil.unitBaseChange F L G)

/-- Ground-group points with coefficients in `L ⊗_F 𝔸_F`, identified with the upper
adelic points through the Weil points. -/
def tensorAdelicEquiv :
    G.affinePoints (CommAlgCat.of F (L ⊗[F] Adeles F)) ≃*
      AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) :=
  (AffineWeil.unitGroundPointsEquiv F L G (CommAlgCat.of F (Adeles F))).symm.trans
    (AdelicWeilRestriction.adelicPointsEquiv F L (AffineWeil.unitBaseChange F L G))

/-- The identification in coordinates: base change, then the canonical tensor map. -/
theorem tensorAdelicEquiv_apply (p : G.affinePoints (CommAlgCat.of F (L ⊗[F] Adeles F))) :
    tensorAdelicEquiv F L G p =
      (AffineWeil.unitBaseChange F L G).affinePointMap
        (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
        (affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G p) := by
  have h : AffineWeil.pointsEquiv F L (AffineWeil.unitBaseChange F L G) (Adeles F)
      ((AffineWeil.unitGroundPointsEquiv F L G (CommAlgCat.of F (Adeles F))).symm p) =
      affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G p := by
    apply (affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G).symm.injective
    rw [MulEquiv.symm_apply_apply]
    exact (AffineWeil.unitGroundPointsEquiv F L G (CommAlgCat.of F (Adeles F))).apply_symm_apply p
  exact congrArg ((AffineWeil.unitBaseChange F L G).affinePointMap
    (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))) h

theorem weilAdelicEquiv_eq (x : AdelicGroupPoints F (W F L G)) :
    weilAdelicEquiv F L G x =
      tensorAdelicEquiv F L G
        (AffineWeil.unitGroundPointsEquiv F L G (CommAlgCat.of F (Adeles F)) x) := by
  rw [tensorAdelicEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- The Galois automorphism `σ` of the upper adelic points: conjugation of the Weil
points by the actual ground-field Galois endomorphism. -/
def galoisTwist (σ : L ≃ₐ[F] L) :
    AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) →ₜ*
      AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) :=
  ((weilAdelicEquiv F L G : AdelicGroupPoints F (W F L G) →ₜ* _).comp
    (AdelicGroupPoints.map F (W F L G) (W F L G) (AffineWeil.unitGaloisAction F L G σ))).comp
      ((weilAdelicEquiv F L G).symm : _ →ₜ* AdelicGroupPoints F (W F L G))

theorem galoisTwist_weilAdelicEquiv (σ : L ≃ₐ[F] L) (x : AdelicGroupPoints F (W F L G)) :
    galoisTwist F L G σ (weilAdelicEquiv F L G x) =
      weilAdelicEquiv F L G
        (AdelicGroupPoints.map F (W F L G) (W F L G) (AffineWeil.unitGaloisAction F L G σ) x) := by
  change weilAdelicEquiv F L G (AdelicGroupPoints.map F (W F L G) (W F L G)
    (AffineWeil.unitGaloisAction F L G σ) ((weilAdelicEquiv F L G).symm
      (weilAdelicEquiv F L G x))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- In tensor coordinates the twist is coefficient conjugation by `σ ⊗ 1`. -/
theorem galoisTwist_tensorAdelicEquiv (σ : L ≃ₐ[F] L)
    (p : G.affinePoints (CommAlgCat.of F (L ⊗[F] Adeles F))) :
    galoisTwist F L G σ (tensorAdelicEquiv F L G p) =
      tensorAdelicEquiv F L G (TensorGaloisPoint.conjugate F L (Adeles F) G σ p) := by
  obtain ⟨x, rfl⟩ :=
    (AffineWeil.unitGroundPointsEquiv F L G (CommAlgCat.of F (Adeles F))).surjective p
  rw [← weilAdelicEquiv_eq, galoisTwist_weilAdelicEquiv, weilAdelicEquiv_eq]
  congr 1
  exact AffineWeil.unitGaloisAction_groundPoints F L G σ _ x

/-- The tensor point `L → L ⊗_F 𝔸_F` of a point with coefficients in `L`. -/
abbrev tensorLeft :
    G.affinePoints (CommAlgCat.of F L) →* G.affinePoints (CommAlgCat.of F (L ⊗[F] Adeles F)) :=
  G.affinePointMap (CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft (S := L) : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F))

omit [NumberField L] [FiniteDimensional F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- Coefficient conjugation by `σ ⊗ 1` restricts to conjugation by `σ` on `L`-points. -/
theorem conjugate_tensorLeft (σ : L ≃ₐ[F] L) (x : G.affinePoints (CommAlgCat.of F L)) :
    TensorGaloisPoint.conjugate F L (Adeles F) G σ (tensorLeft F L G x) =
      tensorLeft F L G (GaloisPoint.conjugate F L G σ x) := by
  have h : CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeLeft (S := L) : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F) ≫
      CommAlgCat.ofHom (TensorGaloisPoint.coefficientConjugate F L (Adeles F) σ) =
      CommAlgCat.ofHom σ.toAlgHom ≫ CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeLeft (S := L) : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F) := by
    ext c
    simp [TensorGaloisPoint.coefficientConjugate, Algebra.TensorProduct.includeLeft_apply]
  have h1 := DFunLike.congr_fun (affinePointMap_comp G (CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeLeft (S := L) : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F))
    (CommAlgCat.ofHom (TensorGaloisPoint.coefficientConjugate F L (Adeles F) σ))) x
  have h2 := DFunLike.congr_fun (affinePointMap_comp G (CommAlgCat.ofHom σ.toAlgHom)
    (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeLeft (S := L) : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F))) x
  rw [h] at h1
  exact h1.symm.trans h2

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- The two identifications of rational points of the base change with `L`-points of
the ground group agree. -/
theorem affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv
    (q : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    affinePointsBaseChangeMulEquiv F L L G (baseChangeCoeffEquiv F L G q) =
      rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q := by
  apply (affinePointsBaseChangeMulEquiv F L L G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, rationalCoeffEquiv_left,
    baseChangeCoeffEquiv_left]

/-- The rational section of a base-change point is the image of its tensor point. -/
theorem tensorAdelicEquiv_tensorLeft (q : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    tensorAdelicEquiv F L G (tensorLeft F L G (baseChangeCoeffEquiv F L G q)) =
      rational L (AffineWeil.unitBaseChange F L G)
        (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q) := by
  have hn := affinePointsBaseChangeMulEquiv_naturality F L L (L ⊗[F] Adeles F) G
    (Algebra.TensorProduct.includeLeft (S := L)) (baseChangeCoeffEquiv F L G q)
  rw [tensorAdelicEquiv_apply, tensorLeft, ← hn,
    affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv]
  have h : CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (S := L) :
        L →ₐ[L] L ⊗[F] Adeles F) ≫ CommAlgCat.ofHom (numberFieldAdeleTensorMap F L) =
      CommAlgCat.ofHom (Algebra.ofId L (Adeles L)) := by
    ext1
    exact Subsingleton.elim _ _
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp, h]
  rfl

omit [FiniteDimensional F L] in
set_option maxRecDepth 2048 in
/-- The scalar extension of a norm-one point, as a Weil point transported upstairs. -/
theorem scalarExtensionNormOneMap_val (g : normOneSubgroup F G) :
    (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      weilAdelicEquiv F L G (unitMap F L G (g : AdelicGroupPoints F G)) := rfl

variable [IsGalois F L]

/-- The twist fixes the scalar extension of every ground-field norm-one point. -/
theorem galoisTwist_scalarExtension (σ : L ≃ₐ[F] L) (g : normOneSubgroup F G) :
    galoisTwist F L G σ (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
      scalarExtensionNormOneMap F L G g := by
  rw [scalarExtensionNormOneMap_val, galoisTwist_weilAdelicEquiv]
  congr 1
  exact (mem_unitRange_iff F L G (unitMap F L G g)).mp ⟨g, rfl⟩ σ

omit [IsGalois F L] in
/-- Clause 1: the twist acts on rational sections by the Galois conjugation of rational
points of the base change. -/
theorem galoisTwist_rationalSection (σ : L ≃ₐ[F] L)
    (q : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    galoisTwist F L G σ (rationalSection F L G q) =
      rationalSection F L G (rationalConjugate F L G σ q) := by
  rw [rationalSection, rationalSection, ← tensorAdelicEquiv_tensorLeft,
    ← tensorAdelicEquiv_tensorLeft, galoisTwist_tensorAdelicEquiv, conjugate_tensorLeft,
    baseChangeCoeffEquiv_rationalConjugate]

end Langlands.Global.AdelicGaloisUnit
