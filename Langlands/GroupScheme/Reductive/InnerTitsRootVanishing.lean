import Langlands.GroupScheme.Reductive.InnerTitsObstruction
import Langlands.GroupScheme.Reductive.GroundAdjointExterior

/-! # Vanishing of the inner Tits obstruction on the integral root lattice -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) (hG : IsSimplyConnected G) (hinner : d.IsInnerStarAction)

/-- The constructed inner obstruction vanishes on the integral span of the actual roots. -/
def InnerTitsRootVanishingStatement : Prop :=
  ∀ lam : characterLattice d.toSplitPinning.torus,
    lam ∈ d.toSplitPinning.rootDatum.rootSpan ℤ → d.innerTitsObstruction hG hinner lam = 0

/-- The ground-field adjoint exterior representations discharge the maximal
weight inputs for root-span vanishing. -/
theorem innerTitsRootVanishing : d.InnerTitsRootVanishingStatement hG hinner := by
  let : Fintype d.toSplitPinning.rootIndex := Fintype.ofFinite _
  let δ := IntegralWeylVector.positiveRootSum d.toSplitPinning.rootDatum d.toSplitPinning.base
  have hground (O : Finset d.toSplitPinning.base.support) :
      d.HasGroundMaximalWeight (δ - d.simpleRootSum O) :=
    d.exists_groundRepresentation_positiveRootSum_sub_simpleRoots O
  intro lam hlam
  exact d.titsObstruction_eq_zero_of_mem_rootSpan hG
    (d.isStarFixedWeight_of_inner hG hinner δ) hground (d.fixedWeightOfInner hG hinner lam) hlam

/-- Every actual root has trivial Brauer obstruction. -/
theorem innerTitsObstruction_root (a : d.toSplitPinning.rootIndex) :
    d.innerTitsObstruction hG hinner (d.toSplitPinning.rootDatum.root a) = 0 :=
  d.innerTitsRootVanishing hG hinner _ (Submodule.subset_span (Set.mem_range_self a))

end Langlands.GroupScheme.GaloisPinningData
