import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientChart
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeParabolicNormalizerProof
import Langlands.GroupScheme.RelativeParabolicQuotientConstruction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.SelfNormalizingProperAmbientProof

/-! # Smooth proper affine-base parabolic quotient charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open SubgroupFunctor HomogeneousQuotientFromEmbedding
open Langlands.AlgebraicGeometry.AlgebraicSpace

section Supplied

variable {S : Scheme.{u}} {G P : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (Q : HomogeneousQuotient i) (hn : (range i).normalizer = range i)

/-- The actual right-coset quotient of a self-normalizing parabolic maps naturally
into the actual parabolic presheaf. -/
def homogeneousQuotientChart : (schemeYoneda S).obj Q.scheme ⟶ parabolicPresheaf G hG := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact quotientChart hG i hi Q.projection (fun U g h => by rw [hn]; exact Q.fibers U g h)

/-- Every group-valued lift evaluates to its actual conjugate family. -/
theorem homogeneousQuotientChart_app_comp {T : Over S} (g : T ⟶ G.X) :
    (homogeneousQuotientChart hG i hi Q hn).app (op T) ⟨g ≫ Q.projection⟩ =
      conjugateParabolic hG i hi g := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact quotientChart_app_comp hG i hi Q.projection
    (fun U g h => by rw [hn]; exact Q.fibers U g h) g

/-- Self-normalization makes the homogeneous quotient chart injective on all tests. -/
theorem homogeneousQuotientChart_injective (T : Over S) :
    Function.Injective ((homogeneousQuotientChart hG i hi Q hn).app (op T)) := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact quotientChart_injective hG i hi Q.projection
    (fun U g h => by rw [hn]; exact Q.fibers U g h) T

/-- The supplied homogeneous quotient chart is a monomorphism of presheaves. -/
theorem homogeneousQuotientChart_mono : Mono (homogeneousQuotientChart hG i hi Q hn) := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact quotientChart_mono hG i hi Q.projection
    (fun U g h => by rw [hn]; exact Q.fibers U g h)

/-- Each actual conjugate has exactly one parameter in the homogeneous quotient. -/
theorem homogeneousQuotientChart_existsUnique_conjugate {T : Over S} (g : T ⟶ G.X) :
    ∃! a : T ⟶ Q.scheme,
      (homogeneousQuotientChart hG i hi Q hn).app (op T) ⟨a⟩ =
        conjugateParabolic hG i hi g := by
  refine ⟨g ≫ Q.projection, homogeneousQuotientChart_app_comp hG i hi Q hn g, ?_⟩
  intro a ha
  have h := homogeneousQuotientChart_injective hG i hi Q hn T
    (ha.trans (homogeneousQuotientChart_app_comp hG i hi Q hn g).symm)
  exact congrArg ULift.down h

end Supplied

section Affine

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)

include hG hi in
/-- An actual relative parabolic over an affine base is its full normalizer. -/
theorem affineParabolic_normalizer_eq : (range i).normalizer = range i :=
  relativeParabolicSelfNormalizer R G P i hG hi.smooth
    (relativeParabolicClosed _ G P i hG hi)
    (fun k _ _ => hi.isParabolicSubgroup_baseChange hG (Spec.algebraMap R k))

/-- The actual smooth right-coset quotient of a parabolic over an affine base,
with its proper structure morphism. -/
def affineParabolicQuotient : RelativeParabolicQuotient.ProperHomogeneousQuotient i :=
  RelativeParabolicQuotient.properQuotientOfDynamicAndAmbient
    parabolicDynamic selfNormalizingProperAmbient hG hi.smooth
    (relativeParabolicClosed _ G P i hG hi)
    (fun k _ _ => hi.isParabolicSubgroup_baseChange hG (Spec.algebraMap R k))

/-- The actual affine-base parabolic quotient is smooth over its base. -/
theorem affineParabolicQuotient_smooth :
    Smooth (affineParabolicQuotient hG i hi).quotient.scheme.hom := by
  let : Smooth G.X.hom := hG.smooth
  exact RelativeParabolicQuotientFibers.smooth _

/-- A smooth proper chart of the actual parabolic presheaf over an affine base. -/
def affineParabolicChart :
    (schemeYoneda (Spec (CommRingCat.of R))).obj
        (affineParabolicQuotient hG i hi).quotient.scheme ⟶ parabolicPresheaf G hG :=
  homogeneousQuotientChart hG i hi (affineParabolicQuotient hG i hi).quotient
    (affineParabolic_normalizer_eq hG i hi)

/-- The affine-base chart is a monomorphism of actual presheaves. -/
theorem affineParabolicChart_mono : Mono (affineParabolicChart hG i hi) :=
  homogeneousQuotientChart_mono hG i hi (affineParabolicQuotient hG i hi).quotient
    (affineParabolic_normalizer_eq hG i hi)

end Affine

end Langlands.GroupScheme.ParabolicSubgroupModuli
