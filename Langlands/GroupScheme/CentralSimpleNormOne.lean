import Langlands.GroupScheme.FiniteAlgebraReducedNorm
import Langlands.Algebra.ReducedNorm

/-! # Actual reduced-norm-one groups of finite-dimensional central simple algebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]

/-- The actual unit group scheme with the canonical finite-dimensional coordinate basis. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  FiniteAlgebraUnits.groupScheme (Module.finBasis k A)

/-- The actual character given by the unconditional reduced norm. -/
def reducedNormHom : groupScheme k A ⟶ (Gm (Spec (CommRingCat.of k))).toGrp :=
  FiniteAlgebraUnits.GaloisNorm.norm (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A)

/-- On every test the actual character is exactly the published unconditional norm on units. -/
theorem reducedNormHom_points (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme k A).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of k)) T (x ≫ (reducedNormHom k A).hom.hom) =
      Langlands.CentralSimple.reducedNormUnits k A
        ((algΓ (CommRingCat.of k)).obj T).unop
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis k A) T x) :=
  FiniteAlgebraUnits.GaloisNorm.norm_points (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) T x

/-- On every affine test the actual character recovers the original reduced-norm operation. -/
theorem reducedNormHom_affine_points (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme k A).X) :
    Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op R)).hom
        (x ≫ (reducedNormHom k A).hom.hom) =
      Langlands.CentralSimple.reducedNormUnits k A R
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis k A) R x) :=
  FiniteAlgebraUnits.GaloisNorm.norm_affine_points (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) R x

/-- The actual reduced-norm-one group, with no supplied splitting data. -/
def normOne : GroupScheme (Spec (CommRingCat.of k)) := kernel (reducedNormHom k A)

/-- The canonical actual inclusion in the algebra-unit group. -/
def normOneι : normOne k A ⟶ groupScheme k A := kernelι (reducedNormHom k A)

/-- The actual unconditional norm-one inclusion is closed. -/
theorem normOne_isClosedSubgroup : IsClosedSubgroup (normOneι k A) :=
  FiniteAlgebraUnits.GaloisNorm.normOne_isClosedSubgroup (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A)

instance normOne_isAffine : IsAffine (normOne k A).X.left :=
  inferInstanceAs (IsAffine
    (FiniteAlgebraUnits.GaloisNorm.normOne (Module.finBasis k A)
      (Langlands.CentralSimple.finiteGaloisSplittingChart k A)).X.left)

instance normOne_locallyOfFiniteType : LocallyOfFiniteType (normOne k A).X.hom :=
  inferInstanceAs (LocallyOfFiniteType
    (FiniteAlgebraUnits.GaloisNorm.normOne (Module.finBasis k A)
      (Langlands.CentralSimple.finiteGaloisSplittingChart k A)).X.hom)

/-- Actual points of the unconditional kernel are the published reduced-norm-one tensor units. -/
def normOnePointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (normOne k A).X) ≃*
      Langlands.CentralSimple.reducedNormOne k A
        ((algΓ (CommRingCat.of k)).obj T).unop :=
  FiniteAlgebraUnits.GaloisNorm.normOnePointsEquiv (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) T

/-- The same comparison on every affine coefficient algebra. -/
def normOneAffinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of k)) :
    ((algSpec (CommRingCat.of k)).obj (op R) ⟶ (normOne k A).X) ≃*
      Langlands.CentralSimple.reducedNormOne k A R :=
  FiniteAlgebraUnits.GaloisNorm.normOneAffinePointsEquiv (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) R

/-- Actual rational points recover the published base coefficient reduced-norm-one group. -/
def normOneRationalPointsEquiv :
    rationalPoints (normOne k A) ≃* Langlands.CentralSimple.reducedNormOne k A k :=
  FiniteAlgebraUnits.GaloisNorm.normOneRationalPointsEquiv (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A)

/-- Actual test pullback restricted to the unconditional reduced-norm-one tensor group. -/
def normOneUnitsRestrict {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    Langlands.CentralSimple.reducedNormOne k A ((algΓ (CommRingCat.of k)).obj T).unop →*
      Langlands.CentralSimple.reducedNormOne k A ((algΓ (CommRingCat.of k)).obj T').unop :=
  FiniteAlgebraUnits.GaloisNorm.normOneUnitsRestrict (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) a

/-- The unconditional norm-one comparison respects every actual change of relative test. -/
theorem normOnePointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (normOne k A).X) :
    normOnePointsEquiv k A T' (a ≫ x) =
      normOneUnitsRestrict k A a (normOnePointsEquiv k A T x) :=
  FiniteAlgebraUnits.GaloisNorm.normOnePointsEquiv_naturality (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) a x

@[simp] theorem normOnePointsEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (normOne k A).X) :
    (normOnePointsEquiv k A T x).val =
      FiniteAlgebraUnits.pointsEquiv (Module.finBasis k A) T
        (x ≫ (normOneι k A).hom.hom) := rfl

@[simp] theorem normOneAffinePointsEquiv_val (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (normOne k A).X) :
    (normOneAffinePointsEquiv k A R x).val =
      FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis k A) R
        (x ≫ (normOneι k A).hom.hom) := rfl

/-- The rational comparison respects the actual inclusion into the algebra-unit group. -/
theorem normOneRationalPointsEquiv_val (x : rationalPoints (normOne k A)) :
    (normOneRationalPointsEquiv k A x).val =
      FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis k A)
        (CommAlgCat.of (CommRingCat.of k) k)
        (GaloisPointComparison.rationalCoeffEquiv k (groupScheme k A)
          (rationalPoints.map (normOneι k A) x)) :=
  FiniteAlgebraUnits.GaloisNorm.normOneRationalPointsEquiv_val (Module.finBasis k A)
    (Langlands.CentralSimple.finiteGaloisSplittingChart k A) x

/-- The actual unconditional character agrees with every supplied finite Galois chart. -/
theorem reducedNormHom_eq_from_chart {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (e : L ⊗[k] A ≃ₐ[L]
      Matrix (Fin (Langlands.CentralSimple.reducedDegree k A))
        (Fin (Langlands.CentralSimple.reducedDegree k A)) L) :
    reducedNormHom k A = FiniteAlgebraUnits.GaloisNorm.norm (Module.finBasis k A) e := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) T).injective
  rw [reducedNormHom_points, FiniteAlgebraUnits.GaloisNorm.norm_points]
  apply Units.ext
  exact (Langlands.CentralSimple.reducedNorm_splitting_independent k A
    (Module.finBasis k A) e _ _).symm

end Langlands.GroupScheme.CentralSimpleUnits
