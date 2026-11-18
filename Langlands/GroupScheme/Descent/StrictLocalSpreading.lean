import Langlands.AlgebraicGeometry.StrictLocalEtaleLimit
import Langlands.GroupScheme.Descent.AffineLimitIsomorphism

/-! # Spreading group isomorphisms from a strict-local affine limit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.StrictLocalSpreading

variable {S : Scheme.{u}} {s : S}
  (L : Langlands.AlgebraicGeometry.StrictLocalEtaleLimit S s)

variable [IsAffine S]

/-- A chosen affine etale level with an actual group isomorphism, obtained
by spreading an isomorphism over the supplied strict-local limit. -/
def isomorphismNeighborhood
    (G H : Langlands.GroupScheme S) [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFinitePresentation G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (e : (Langlands.GroupScheme.baseChange L.baseMap).obj G ≅
      (Langlands.GroupScheme.baseChange L.baseMap).obj H) :
    Σ i : L.index,
      ((Langlands.GroupScheme.baseChange (L.structural.app i)).obj G ≅
        (Langlands.GroupScheme.baseChange (L.structural.app i)).obj H) :=
  Langlands.GroupScheme.Descent.AffineLimit.isomorphismModel L.diagram L.structural
    (Cone.mk (Spec (CommRingCat.of L.ring)) L.projection) L.isLimit L.baseMap
    L.compatible G H e

/-- Isomorphism over the strict-local limit gives an affine etale
neighbourhood meeting the prescribed point where the groups are isomorphic. -/
theorem exists_etale_neighbourhood_iso
    (G H : Langlands.GroupScheme S) [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFinitePresentation G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (e : (Langlands.GroupScheme.baseChange L.baseMap).obj G ≅
      (Langlands.GroupScheme.baseChange L.baseMap).obj H) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (b : U ⟶ S), Etale b ∧
      s ∈ Set.range b ∧ Nonempty
        ((Langlands.GroupScheme.baseChange b).obj G ≅
          (Langlands.GroupScheme.baseChange b).obj H) := by
  let m := isomorphismNeighborhood L G H e
  exact ⟨L.diagram.obj m.1, inferInstance, L.structural.app m.1,
    inferInstance, ⟨L.projection.app m.1 (IsLocalRing.closedPoint L.ring),
      L.level_point_image m.1⟩, ⟨m.2⟩⟩

end Langlands.GroupScheme.Descent.StrictLocalSpreading
