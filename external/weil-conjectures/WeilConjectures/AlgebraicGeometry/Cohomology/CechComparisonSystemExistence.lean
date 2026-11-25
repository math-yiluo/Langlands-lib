/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechAlphaQuasiIso
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonMaps
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonBoundary

/-! # Existence of normalized additive Cech comparisons

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Every open cover admits a normalized additive Cech comparison system.

Source: Stacks Project, Tag 01EQ, Lemma 20.11.2; Tag 01FD, Lemma 20.15.1.
(blueprint: lem-pc-cech-comparison-system-existence)

Proof: For each abelian sheaf choose an injective resolution and form the ordered
Cech double complex. The section augmentation is a quasi-isomorphism: the augmented
Cech row of each injective is exact, and totalization has finite diagonals. Compose
the coefficient augmentation on homology with the inverse section augmentation and
the resolution-to-Ext identification. Comparison lifts between resolutions give
commuting augmentation squares. Homotopic lifts induce equal maps on homology, so
the resulting comparisons are independent of choices and natural in the sheaf.
In degree zero both augmentations are restriction of sections, so their quotient is
the gluing isomorphism followed by the sections-to-Ext identification. For a short
exact coefficient sequence surjective on all tuple sections, its Cech complexes
form a short exact sequence. Choose horseshoe resolutions and compare both
augmentations; naturality of homology boundaries gives precisely the connecting
law. Package these natural transformations, their zero law, and their connecting
law as the required system. Infinite covers cause no convergence issue because
total diagonals are finite. An empty cover forces X empty by hcover, and all
complexes and section groups are zero. -/
theorem exists_cechComparisonSystem
    {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    Nonempty (CechComparisonSystem U hcover) := by
  classical
  choose c hc hzero using fun F ↦ exists_abelianCechComparison_maps U hcover F
    (fun I ↦ abelianCechAlpha_quasiIso U hcover I)
  let comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q := fun q ↦
    { app := fun F ↦ c F q
      naturality := fun F G f ↦
        abelianCechComparison_naturality U hcover f q (c F q) (c G q) (hc F q) (hc G q) }
  refine ⟨{ comparison := comparison, zero := ?_, connecting := ?_ }⟩
  · apply NatTrans.ext
    funext F
    exact hzero F
  · intro T hT hg q
    exact abelianCechComparison_boundary U hcover T hT hg q
      (c T.X₁ (q + 1)) (c T.X₃ q) (hc T.X₁ (q + 1)) (hc T.X₃ q)
end AlgebraicGeometry.Scheme.Modules
