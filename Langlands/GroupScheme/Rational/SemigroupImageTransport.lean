import Langlands.GroupScheme.Rational.SemigroupComparisonStatement
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.CoordinateSemigroupStatement
import Langlands.GroupScheme.Rational.DominantPullbackProof
import Langlands.GroupScheme.ImageEnvelopeStabilityProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Image transport for actual semigroup subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneratedImage

variable {B : Scheme.{u}} {H G : GroupScheme B} (f : H ⟶ G)
    (D : GeneratedImage f.hom.hom)

/-- The factor of an actual homomorphism through its represented closed envelope. -/
def factorGroupHom : H ⟶ D.group :=
  D.represents.factorHom f (by
    rintro T x ⟨y, rfl⟩
    exact closedImageEnvelope_containsImage f.hom.hom T y)

theorem factorGroupHom_comp : D.factorGroupHom f ≫ D.inclusion = f :=
  D.represents.factorHom_comp _ _

theorem factorGroupHom_hom : (D.factorGroupHom f).hom.hom = D.factor := by
  exact D.factor_unique _ (congrArg (fun a => a.hom.hom) (D.factorGroupHom_comp f))

/-- A dominant power of a homomorphic image already makes the single factor
 dominant; the power map factors through the source group multiplication. -/
theorem factorGroupHom_isDominant (n : ℕ) (hn : IsDominant (D.powerMap n).left) :
    IsDominant (D.factorGroupHom f).hom.hom.left := by
  have he : orderedPowerMap (𝟙 H.X) n ≫ (D.factorGroupHom f).hom.hom = D.powerMap n := by
    rw [orderedPowerMap_comp, D.factorGroupHom_hom f]
    simp only [Category.id_comp]
    rfl
  have : IsDominant ((orderedPowerMap (𝟙 H.X) n).left ≫
      (D.factorGroupHom f).hom.hom.left) := by
    change IsDominant (orderedPowerMap (𝟙 H.X) n ≫
      (D.factorGroupHom f).hom.hom).left
    rw [he]
    exact hn
  exact IsDominant.of_comp (orderedPowerMap (𝟙 H.X) n).left
    (D.factorGroupHom f).hom.hom.left

end GeneratedImage

namespace CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- Dominant equivariant group maps include target augmentation weights in source
 augmentation weights. Reducedness rules out invisible nilpotent coordinates. -/
theorem support_subset_of_dominant (c : AutomorphicAction S.toGrp H)
    (b : AutomorphicAction S.toGrp G) (f : H ⟶ G)
    (hf : IsEquivariant c b f.hom.hom) (hG : IsReduced G.X.left)
    (hdom : IsDominant f.hom.hom.left) : support b ⊆ support c := by
  exact support_subset_of_injective c b f hf
    (PointedCoordinateWeights.dominantPullbackStatement k H.X G.X f.hom.hom hG hdom)

end CoordinateWeights

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- Coordinate/Lie containment transports a semigroup bound across a dominant
 equivariant map, including inseparable maps and semigroups containing zero. -/
theorem actionWeightSupport_subset_of_dominant
    (hcontain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hH : Smooth H.X.hom) (hG : Smooth G.X.hom)
    (hHconn : ConnectedSpace H.X.left) (hGconn : ConnectedSpace G.X.left)
    (hS : IsSplitTorus S.toGrp)
    (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
    (f : H ⟶ G) (hf : CoordinateWeights.IsEquivariant c b f.hom.hom)
    (hdom : IsDominant f.hom.hom.left) (A : AddSubsemigroup (characterLattice S))
    (hA : actionWeightSupport c ⊤ ⊆ A) : actionWeightSupport b ⊤ ⊆ A := by
  let : Smooth G.X.hom := hG
  have hred := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    k G.X.left G.X.hom
  apply (hcontain k G hG inferInstance hGconn S hS b A).mp
  exact (CoordinateWeights.support_subset_of_dominant c b f hf hred hdom).trans
    ((hcontain k H hH inferInstance hHconn S hS c A).mpr hA)

end RelativeRoot

end Langlands.GroupScheme
