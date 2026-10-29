import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-! # The constants and structural morphism of polynomial projective space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Constants identify the base ring with the degree-zero ring of polynomial projective
space. -/
def projectiveSpaceConstantsEquiv (R : Type u) [CommRing R] (n : ℕ) :
    R ≃+* projectiveSpaceGrading R n 0 :=
  RingEquiv.ofBijective (projectiveSpaceConstants R n) (by
    constructor
    · intro r s h
      exact MvPolynomial.C_injective (Fin (n + 1)) R (congrArg Subtype.val h)
    · intro p
      refine ⟨p.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr
          p.property)).symm)

@[simp]
lemma projectiveSpaceConstantsEquiv_toRingHom (R : Type u) [CommRing R] (n : ℕ) :
    (projectiveSpaceConstantsEquiv R n).toRingHom = projectiveSpaceConstants R n :=
  rfl

instance projectiveSpaceCoordinateRing_finiteType (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.FiniteType (projectiveSpaceGrading R n 0) (ProjectiveCoordinateRing R n) := by
  apply RingHom.finiteType_algebraMap.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := projectiveSpaceConstants R n)
  change (algebraMap R (ProjectiveCoordinateRing R n)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance projectiveSpaceToSpec_isProper (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (projectiveSpaceToSpec R n) := by
  have : IsIso (CommRingCat.ofHom (projectiveSpaceConstants R n)) := by
    change IsIso (projectiveSpaceConstantsEquiv R n).toCommRingCatIso.hom
    infer_instance
  have : IsIso (Spec.map (CommRingCat.ofHom (projectiveSpaceConstants R n))) :=
    inferInstance
  have hProj : IsProper (Proj.toSpecZero (projectiveSpaceGrading R n)) := inferInstance
  have hSpec : IsProper (Spec.map (CommRingCat.ofHom (projectiveSpaceConstants R n))) :=
    inferInstance
  unfold projectiveSpaceToSpec
  exact MorphismProperty.comp_mem @IsProper _ _ hProj hSpec

end Langlands.AlgebraicGeometry
