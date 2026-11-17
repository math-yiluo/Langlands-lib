import Langlands.GroupScheme.NormOneOuterDescent
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Actual norm-one automorphisms on affine coefficient units -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits

open Langlands.CentralSimple

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- An actual norm-one group-scheme automorphism acts on affine tensor units by
the canonical actual affine point comparison. -/
def coefficientAutomorphism (f : normOne K A ≅ normOne K A)
    (R : CommAlgCat.{u} (CommRingCat.of K)) :
    reducedNormOne K A R ≃* reducedNormOne K A R :=
  (normOneAffinePointsEquiv K A R).symm.trans
    ((((yonedaGrp.mapIso f).app
      (op ((algSpec (CommRingCat.of K)).obj (op R)))).groupIsoToMulEquiv).trans
        (normOneAffinePointsEquiv K A R))

/-- The induced coefficient automorphism is exactly the point action of the
actual scheme automorphism in affine coordinates. -/
theorem coefficientAutomorphism_affinePoints (f : normOne K A ≅ normOne K A)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (normOne K A).X) :
    coefficientAutomorphism K A f R (normOneAffinePointsEquiv K A R x) =
      normOneAffinePointsEquiv K A R (x ≫ f.hom.hom.hom) := by
  change normOneAffinePointsEquiv K A R
    ((normOneAffinePointsEquiv K A R).symm
      (normOneAffinePointsEquiv K A R x) ≫ f.hom.hom.hom) = _
  rw [MulEquiv.symm_apply_apply]

/-- On affine test schemes, the all-test tensor unit is the affine tensor unit
transported through the canonical inverse global-sections comparison. -/
theorem normOnePointsEquiv_affine_val (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (normOne K A).X) :
    (normOnePointsEquiv K A ((algSpec (CommRingCat.of K)).obj (op R)) x).val =
      Units.map (Algebra.TensorProduct.map
        (Corepresented.affineSectionsIso R).inv.hom (AlgHom.id K A)).toMonoidHom
          (normOneAffinePointsEquiv K A R x).val := by
  rw [normOnePointsEquiv_val, normOneAffinePointsEquiv_val]
  exact Corepresented.pointsEquiv_eq_affinePointsEquiv
    (FiniteAlgebraUnits.functor K A)
    (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K A)) R _

/-- The all-test coordinates of the image point recover the induced coefficient
automorphism through the canonical global-sections comparison. -/
theorem normOnePointsEquiv_coefficientAutomorphism_val
    (f : normOne K A ≅ normOne K A)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (normOne K A).X) :
    (normOnePointsEquiv K A ((algSpec (CommRingCat.of K)).obj (op R))
      (x ≫ f.hom.hom.hom)).val =
        Units.map (Algebra.TensorProduct.map
          (Corepresented.affineSectionsIso R).inv.hom (AlgHom.id K A)).toMonoidHom
            (coefficientAutomorphism K A f R
              (normOneAffinePointsEquiv K A R x)).val := by
  rw [coefficientAutomorphism_affinePoints, normOnePointsEquiv_affine_val]

variable (L : Type u) [Field L] [Algebra K L]

/-- Coefficient Galois conjugation agrees with precomposition of actual affine
points by the corresponding spectrum automorphism. -/
theorem normOneAffinePointsEquiv_coefficientConjugate (σ : L ≃ₐ[K] L)
    (x : (algSpec (CommRingCat.of K)).obj
      (op (CommAlgCat.of (CommRingCat.of K) L)) ⟶ (normOne K A).X) :
    normOneAffinePointsEquiv K A (CommAlgCat.of (CommRingCat.of K) L)
      ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ x) =
        NormOneOuterDescent.coefficientConjugateNormOne K A L σ
          (normOneAffinePointsEquiv K A (CommAlgCat.of (CommRingCat.of K) L) x) := by
  apply Subtype.ext
  change FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A) _
    (((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ x) ≫
      (normOneι K A).hom.hom) =
        Units.map (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)).toMonoidHom
          (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A) _
            (x ≫ (normOneι K A).hom.hom))
  rw [Category.assoc, FiniteAlgebraUnits.affinePointsEquiv_naturality]
  rfl

/-- Every actual norm-one automorphism gives a coefficient automorphism that
commutes with Galois conjugation. -/
theorem coefficientAutomorphism_covariant (f : normOne K A ≅ normOne K A)
    (σ : L ≃ₐ[K] L) (x : reducedNormOne K A L) :
    coefficientAutomorphism K A f (CommAlgCat.of (CommRingCat.of K) L)
      (NormOneOuterDescent.coefficientConjugateNormOne K A L σ x) =
        NormOneOuterDescent.coefficientConjugateNormOne K A L σ
          (coefficientAutomorphism K A f (CommAlgCat.of (CommRingCat.of K) L) x) := by
  obtain ⟨x, rfl⟩ := (normOneAffinePointsEquiv K A
    (CommAlgCat.of (CommRingCat.of K) L)).surjective x
  rw [← normOneAffinePointsEquiv_coefficientConjugate,
    coefficientAutomorphism_affinePoints, coefficientAutomorphism_affinePoints,
    ← normOneAffinePointsEquiv_coefficientConjugate, Category.assoc]

end Langlands.GroupScheme.CentralSimpleUnits
