import Langlands.GroupScheme.Rational.TorusActionCoordinates
import Langlands.GroupScheme.Rational.CoordinateAction
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof

/-! # Actual eigenfunctions and corepresented homogeneous coordinates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R}
    (c : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- Homogeneity is precisely the eigenfunction identity on all algebra points. -/
theorem isHomogeneous_iff_coord_act (m : I → ℤ) (f : B) :
    IsHomogeneous c σ m f ↔
      ∀ (A : CommAlgCat.{u} R) (t : I → Aˣ) (x : F.obj A),
        coord c (σ.act t x) f =
          coord c x f * (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) := by
  constructor
  · intro hf A t x
    exact coord_act_of_isHomogeneous c σ t x hf
  · intro hf
    change coord c (σ.act (universalUnits I B) (F.map (constHom I B) (univ c))) f =
      AddMonoidAlgebra.single m f
    rw [hf, coord_map, coord_univ, AlgHom.comp_id, exponentValue_universalUnits]
    change AddMonoidAlgebra.single 0 f * AddMonoidAlgebra.single m 1 = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

end Corepresented

namespace TorusActionCoordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- Exponent vectors evaluate on the original acting points as the specified units. -/
theorem characterValue_torusPoint {A : CommAlgCat.{u} (CommRingCat.of k)}
    (t : I → Aˣ) (m : I → ℤ) :
    Lie.characterValue (PointedCoordinateWeights.characterEquiv e m)
        (AutomorphicAction.torusPoint e t) =
      splitTorus.exponentValue I t (Multiplicative.ofAdd m) := by
  rw [PointedCoordinateWeights.characterValue_eq_pointCharacter]
  simp only [PointedCoordinateWeights.pointCharacter, AutomorphicAction.torusPoint,
    Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id, MulEquiv.apply_symm_apply]

/-- The counit in the corepresentation is the original coordinate augmentation. -/
@[simp] theorem counit_eq_coordinateOrigin :
    AffineLinearEmbedding.counit (corepresentation G) = Lie.coordinateOrigin G := rfl

/-- The coaction grading is the actual character eigenspace convention. -/
theorem isHomogeneous_iff_isEigenfunction (m : I → ℤ) (f : Lie.coordinateAlgebra G) :
    Corepresented.IsHomogeneous (corepresentation G) (b.toCorepresentedTorusAction e) m f ↔
      CoordinateWeights.IsEigenfunction b (PointedCoordinateWeights.characterEquiv e m) f := by
  rw [Corepresented.isHomogeneous_iff_coord_act]
  constructor
  · intro hf A _ _ s x
    let t := splitTorus.algebraPointsEquiv I A (s ≫ e.hom.hom.hom)
    have h := hf (CommAlgCat.of (CommRingCat.of k) A) t x
    rw [AutomorphicAction.toCorepresentedTorusAction_act_point] at h
    rw [PointedCoordinateWeights.characterValue_eq_pointCharacter]
    simpa only [coord_eq_pointCoordinates, PointedCoordinateWeights.pointCharacter, mul_comm]
      using h
  · intro hf A t x
    have h := hf A (AutomorphicAction.torusPoint e t) x
    rw [characterValue_torusPoint] at h
    simpa only [coord_eq_pointCoordinates, AutomorphicAction.toCorepresentedTorusAction_act,
      mul_comm] using h

/-- Both weight-space constructions are equal submodules of the original coordinate algebra. -/
theorem homogeneousSubmodule_eq_weightSpace (m : I → ℤ) :
    Corepresented.homogeneousSubmodule (corepresentation G) (b.toCorepresentedTorusAction e) m =
      CoordinateWeights.weightSpace b (PointedCoordinateWeights.characterEquiv e m) := by
  ext f
  exact isHomogeneous_iff_isEigenfunction b e m f

/-- The homogeneous and actual character eigenspaces have the same coordinate vectors. -/
def homogeneousWeightSpaceEquiv (m : I → ℤ) :
    Corepresented.homogeneousSubmodule (corepresentation G) (b.toCorepresentedTorusAction e) m
      ≃ₗ[k] CoordinateWeights.weightSpace b (PointedCoordinateWeights.characterEquiv e m) :=
  LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_weightSpace b e m)

end TorusActionCoordinates

end Langlands.GroupScheme
