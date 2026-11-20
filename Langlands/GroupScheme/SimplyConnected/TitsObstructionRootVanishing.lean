import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.Reductive.GroundAdjointExterior
import Langlands.GroupScheme.Reductive.StarFixedPositiveRootSum

/-! # Unconditional root-span vanishing of the Tits obstruction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

/-- For every finite set `O` of simple roots, the positive-root sum minus `∑_{i ∈ O} α_i` is a
maximal weight of multiplicity one of a representation of `G` over `k` (the exterior powers of
the adjoint representation). -/
theorem hasGroundMaximalWeight_positiveRootSum_sub [Fintype d.toSplitPinning.rootIndex]
    (O : Finset d.toSplitPinning.base.support) :
    d.HasGroundMaximalWeight (IntegralWeylVector.positiveRootSum d.toSplitPinning.rootDatum
      d.toSplitPinning.base - d.simpleRootSum O) :=
  d.exists_groundRepresentation_positiveRootSum_sub_simpleRoots O

variable [IsGalois k K]

/-- The Tits obstruction value vanishes on every star-fixed weight of the integral root span,
with no further hypothesis. -/
theorem titsObstructionValue_eq_zero_of_mem_rootSpan_unconditional
    (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) (hfix : d.IsStarFixedWeight lam) :
    d.titsObstructionValue hspan lam hfix = 0 := by
  classical
  let : Fintype d.toSplitPinning.rootIndex := Fintype.ofFinite _
  exact d.titsObstructionValue_eq_zero_of_mem_rootSpan_of_ground hspan
    d.starFixedPositiveRootSum.property d.hasGroundMaximalWeight_positiveRootSum_sub hlam hfix

variable (hG : IsSimplyConnected G)

/-- Root-span vanishing of the Tits obstruction of a simply connected group: it is zero on every
star-fixed weight in the integral root span. -/
theorem titsObstruction_eq_zero_of_mem_rootSpan_unconditional (lam : d.starFixedWeights)
    (hlam : lam.1 ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) :
    d.titsObstruction hG lam = 0 :=
  d.titsObstructionValue_eq_zero_of_mem_rootSpan_unconditional _ hlam
    (d.isStarFixedWeight_of_mem_starFixedWeights lam.2)

omit [IsGalois k K] in
/-- The star-fixed weights lying in the integral root span, as a subgroup of
`d.starFixedWeights`. -/
def rootSpanStarFixedWeights : AddSubgroup d.starFixedWeights :=
  (d.toSplitPinning.rootDatum.rootSpan ℤ).toAddSubgroup.comap d.starFixedWeights.subtype

omit [IsGalois k K] in
theorem mem_rootSpanStarFixedWeights (lam : d.starFixedWeights) :
    lam ∈ d.rootSpanStarFixedWeights ↔ lam.1 ∈ d.toSplitPinning.rootDatum.rootSpan ℤ :=
  Iff.rfl

/-- The star-fixed weights in the integral root span lie in the kernel of the Tits obstruction. -/
theorem rootSpan_le_ker_titsObstruction :
    d.rootSpanStarFixedWeights ≤ (d.titsObstruction hG).ker := fun lam hlam =>
  d.titsObstruction_eq_zero_of_mem_rootSpan_unconditional hG lam hlam

/-- The Tits obstruction factors through the quotient of the star-fixed weights by the
star-fixed weights of the integral root span. -/
def titsObstructionRootQuotient :
    d.starFixedWeights ⧸ d.rootSpanStarFixedWeights →+ BrauerGroup.{u, u} k :=
  QuotientAddGroup.lift d.rootSpanStarFixedWeights (d.titsObstruction hG)
    (d.rootSpan_le_ker_titsObstruction hG)

theorem titsObstructionRootQuotient_mk (lam : d.starFixedWeights) :
    d.titsObstructionRootQuotient hG (QuotientAddGroup.mk lam) = d.titsObstruction hG lam :=
  rfl

end Langlands.GroupScheme.GaloisPinningData
