import Langlands.GroupScheme.Descent.RadicalTensorIdeal
import Langlands.GroupScheme.Descent.GaloisIdealSheafDescent

/-! # Defining-ideal descent of a represented radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Descent.RadicalTensorIdeal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}
    {A : Type u} [CommRing A] [Algebra k A]
    (e : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ≅ G.X)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance : IsAffine (pullback G.X.hom (algebraBaseMap k K)) := by
  infer_instance

local instance : IsAffine ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The full defining ideal on the affine base change is the actual section
kernel used in tensor coordinates. -/
theorem ideal_top_comap_sectionsEquiv :
    (i.hom.hom.left.ker.ideal
      ⟨⊤, isAffineOpen_top ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.left⟩).comap
        (TensorCoordinates.sectionsEquiv k K A G.X e).toRingHom =
      coordinateIdeal (k := k) (K := K) (A := A) (G := G) (e := e) (i := i) := by
  rw [Scheme.ker_of_isAffine]
  simp [coordinateIdeal, RingHom.comap_ker]

/-- A represented radical over any Galois extension has a defining ideal sheaf
pulled back from the original affine group scheme. -/
def idealSheafDescent [IsGalois k K] (hi : IsUnipotentRadical i) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      i.hom.hom.left.ker :=
  AffineIdealDescent.ofGaloisStableTensorIdeal k K A
    (pullback.fst G.X.hom (algebraBaseMap k K)) i.hom.hom.left.ker
    (TensorCoordinates.groundSectionsEquiv k A G.X e)
    (TensorCoordinates.sectionsEquiv k K A G.X e)
    (TensorCoordinates.projection_comp_groundSectionsEquiv k K A G.X e)
    (by
      intro σ x hx
      rw [ideal_top_comap_sectionsEquiv e] at hx ⊢
      exact coefficientConjugate_mem (k := k) (K := K) (A := A) (G := G)
        (e := e) (i := i) hi σ x hx)

include e in
/-- The descended full defining ideal supplies equality of the two actual
closed-subgroup images over the double overlap. -/
theorem overlap_range_eq [IsGalois k K] (hi : IsUnipotentRadical i) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i) :=
  hi.isClosedSubgroup.overlap_range_eq_of_definingIdealDescent
    (algebraBaseMap k K) (idealSheafDescent e hi)

end Langlands.GroupScheme.Descent.RadicalTensorIdeal
