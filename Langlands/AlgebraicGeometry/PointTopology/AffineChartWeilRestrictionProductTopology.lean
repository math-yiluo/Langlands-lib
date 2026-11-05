import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionProduct
import Langlands.AlgebraicGeometry.PointTopology.SchemeFiniteProducts

/-! # Independent point topologies for the finite-product Weil decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)] [Finite ι]
variable (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
variable [∀ i, Algebra A (B i)]
variable [∀ i, Module.Finite A (B i)] [∀ i, Module.Projective A (B i)]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]
variable (Y : Over (Spec (CommRingCat.of (∀ j, B j)))) [LocallyOfFiniteType Y.hom]

local instance productTopologyFactorLocallyOfFiniteType (i : ι) :
    LocallyOfFiniteType (finiteProductFactorScheme B Y i).hom :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Y.hom (finiteProductSpecProjection B i)))

variable [IsSeparated Y.hom]

local instance productTopologyFactorIsSeparated (i : ι) :
    IsSeparated (finiteProductFactorScheme B Y i).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (finiteProductSpecProjection B i)))

/-- The canonical finite-product Weil decomposition is a homeomorphism on
actual local-value-ring points with their independent scheme point topologies. -/
def affineChartWeilRestrictionProductPointHomeomorph
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace
        (RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) :=
      schemePointTopology A (affineChartWeilRestriction A (∀ i, B i) Y) S
    letI : ∀ i, TopologicalSpace (RingPoint A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S) :=
      fun i => schemePointTopology A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S
    RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S ≃ₜ
      (∀ i, RingPoint A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S) :=
  schemeFiniteProductPointHomeomorph A S
    (fun i => affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i))
    (affineChartWeilRestrictionProductFan B A Y hY)
    (affineChartWeilRestrictionProductFanIsLimit B A Y hY)

/-- Every component is postcomposition with the original canonical factor map. -/
@[simp]
theorem affineChartWeilRestrictionProductPointHomeomorph_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) (i : ι) :
    affineChartWeilRestrictionProductPointHomeomorph B A S Y hY p i =
      p ≫ affineChartWeilRestrictionProductProjection B A Y hY i :=
  schemeFiniteProductPointHomeomorph_apply A S
    (fun i => affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i))
    (affineChartWeilRestrictionProductFan B A Y hY)
    (affineChartWeilRestrictionProductFanIsLimit B A Y hY) p i

/-- The homeomorphism also agrees componentwise with the actual scheme product
isomorphism, retaining its fixed categorical projections. -/
theorem affineChartWeilRestrictionProductPointHomeomorph_apply_iso
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) (i : ι) :
    affineChartWeilRestrictionProductPointHomeomorph B A S Y hY p i =
      p ≫ (affineChartWeilRestrictionProductIso B A Y hY).hom ≫
        Pi.π (fun j => affineChartWeilRestriction A (B j)
          (finiteProductFactorScheme B Y j)) i := by
  rw [affineChartWeilRestrictionProductPointHomeomorph_apply,
    affineChartWeilRestrictionProductIso_hom_π]

/-- The original counit followed by actual factor pullback is exactly the
factor counit after the product point homeomorphism. -/
@[simp]
theorem affineChartWeilRestrictionProductPointHomeomorph_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) (i : ι) :
    affineChartWeilRestrictionComparison A (B i) (finiteProductFactorScheme B Y i)
        (ringTest A S)
        (affineChartWeilRestrictionProductPointHomeomorph B A S Y hY p i) =
      affineChartWeilRestrictionProductComparison B A Y (ringTest A S) p i := by
  rw [affineChartWeilRestrictionProductPointHomeomorph_apply]
  exact affineChartWeilRestrictionProductProjection_comparison B A Y hY _ p i

omit [IsSeparated Y.hom] in
/-- An actual relative projective immersion supplies the geometric premises
for the same independently topologized finite-product comparison. -/
def projectiveImmersionWeilRestrictionProductPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (∀ i, B i) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (∀ i, B i) n = Y.hom) :
    letI : TopologicalSpace
        (RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) :=
      schemePointTopology A (affineChartWeilRestriction A (∀ i, B i) Y) S
    letI : ∀ i, TopologicalSpace (RingPoint A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S) :=
      fun i => schemePointTopology A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S
    RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S ≃ₜ
      (∀ i, RingPoint A
        (affineChartWeilRestriction A (B i) (finiteProductFactorScheme B Y i)) S) := by
  letI := isSeparated_of_projectiveImmersion (∀ i, B i) Y n j hj
  exact affineChartWeilRestrictionProductPointHomeomorph B A S Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion (∀ i, B i) n j)

omit [IsSeparated Y.hom] in
/-- The projective-immersion specialization retains the exact original
counit component formula. -/
@[simp]
theorem projectiveImmersionWeilRestrictionProductPointHomeomorph_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (∀ i, B i) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (∀ i, B i) n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A (∀ i, B i) Y) S) (i : ι) :
    affineChartWeilRestrictionComparison A (B i) (finiteProductFactorScheme B Y i)
        (ringTest A S)
        (projectiveImmersionWeilRestrictionProductPointHomeomorph B A S Y n j hj p i) =
      affineChartWeilRestrictionProductComparison B A Y (ringTest A S) p i := by
  let := isSeparated_of_projectiveImmersion (∀ i, B i) Y n j hj
  exact affineChartWeilRestrictionProductPointHomeomorph_comparison B A S Y _ p i

end Langlands.AlgebraicGeometry.PointTopology
