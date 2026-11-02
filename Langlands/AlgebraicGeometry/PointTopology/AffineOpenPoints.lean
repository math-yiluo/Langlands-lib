import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.Localization

/-!
# Actual affine basic-open point comparisons
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

local instance affineBasicOpen_isAffine (f : AffineCoordinateRing R X) :
    IsAffine (X.left.basicOpen (U := ⊤) f) :=
  (isAffineOpen_top X.left).basicOpen f

local instance affineOpenCoordinateAlgebra (U : X.left.Opens) [IsAffine U] :
    Algebra (AffineCoordinateRing R X) (AffineCoordinateRing R (openOver R X U)) :=
  inferInstanceAs (Algebra Γ(X.left, ⊤) Γ(U, ⊤))

local instance affineOpenCoordinateTower (U : X.left.Opens) [IsAffine U] :
    IsScalarTower R (AffineCoordinateRing R X)
      (AffineCoordinateRing R (openOver R X U)) :=
  IsScalarTower.of_algebraMap_eq' (affineCoordinateMap_natural R (openOverι R X U)).symm

local instance basicOpenCoordinateLocalization (f : AffineCoordinateRing R X) :
    IsLocalization.Away f
      (AffineCoordinateRing R (openOver R X (X.left.basicOpen (U := ⊤) f))) :=
  Γ_restrict_isLocalization X.left (show Γ(X.left, ⊤) from f)

variable (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S]

private theorem basicOpenPointMap_factor (f : AffineCoordinateRing R X) :
    openPointMap R X S (X.left.basicOpen (U := ⊤) f) =
      (affineSchemePointHomeomorph R X S).symm ∘
        (AlgPoint.precomp (Algebra.algHom R (AffineCoordinateRing R X)
          (AffineCoordinateRing R (openOver R X (X.left.basicOpen (U := ⊤) f))))) ∘
        (affineSchemePointHomeomorph R (openOver R X (X.left.basicOpen (U := ⊤) f)) S) := by
  funext p
  apply (affineSchemePointEquiv R X S).injective
  change affineSchemePointEquiv R X S (p ≫ openOverι R X (X.left.basicOpen (U := ⊤) f)) =
    affineSchemePointEquiv R X S
      ((affineSchemePointEquiv R X S).symm _)
  rw [Equiv.apply_symm_apply, affineSchemePointEquiv_natural]
  rfl

/-- A basic-open point inclusion has the subspace topology when units do. -/
theorem isEmbedding_basicOpenPointMap [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) (f : AffineCoordinateRing R X) :
    IsEmbedding (openPointMap R X S (X.left.basicOpen (U := ⊤) f)) := by
  rw [basicOpenPointMap_factor R X S f]
  exact (affineSchemePointHomeomorph R X S).symm.isEmbedding.comp
    ((AlgPoint.isEmbedding_precomp_localization (R := R) (S := S)
      (L := AffineCoordinateRing R (openOver R X (X.left.basicOpen (U := ⊤) f)))
      (Submonoid.powers f) hS).comp
        (affineSchemePointHomeomorph R (openOver R X (X.left.basicOpen (U := ⊤) f)) S).isEmbedding)

/-- The actual basic-open point carrier is homeomorphic to its image-contained locus. -/
def basicOpenPointHomeomorph [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) (f : AffineCoordinateRing R X) :
    RingPoint R (openOver R X (X.left.basicOpen (U := ⊤) f)) S ≃ₜ
      {p : RingPoint R X S // Set.range p.left ⊆ X.left.basicOpen (U := ⊤) f} :=
  (openPointEquiv R X S (X.left.basicOpen (U := ⊤) f)).toHomeomorphOfIsInducing
    (IsInducing.subtypeVal.of_comp_iff.mp
      (isEmbedding_basicOpenPointMap R X S hS f).isInducing)

@[simp] theorem basicOpenPointHomeomorph_apply [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) (f : AffineCoordinateRing R X)
    (p : RingPoint R (openOver R X (X.left.basicOpen (U := ⊤) f)) S) :
    (basicOpenPointHomeomorph R X S hS f p).val =
      openPointMap R X S (X.left.basicOpen (U := ⊤) f) p := rfl

/-- Basic-open inclusions induce actual open embeddings when units form an open subspace. -/
theorem isOpenEmbedding_basicOpenPointMap [ContinuousMul S] [IsOpenUnits S]
    (f : AffineCoordinateRing R X) :
    IsOpenEmbedding (openPointMap R X S (X.left.basicOpen (U := ⊤) f)) := by
  rw [basicOpenPointMap_factor R X S f]
  exact (affineSchemePointHomeomorph R X S).symm.isOpenEmbedding.comp
    ((AlgPoint.isOpenEmbedding_precomp_away (R := R) (S := S)
      (L := AffineCoordinateRing R (openOver R X (X.left.basicOpen (U := ⊤) f))) f).comp
        (affineSchemePointHomeomorph R (openOver R X (X.left.basicOpen (U := ⊤) f)) S).isOpenEmbedding)

end Langlands.AlgebraicGeometry.PointTopology
