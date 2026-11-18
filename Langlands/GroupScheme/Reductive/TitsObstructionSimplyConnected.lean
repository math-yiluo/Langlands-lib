import Langlands.GroupScheme.Reductive.GaloisRationalBaseChange
import Langlands.GroupScheme.SimplyConnected.StarFixedWeights

/-! # The Tits obstruction of a simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [IsGalois k K] (hG : IsSimplyConnected G)

omit [IsGalois k K] in
theorem isStarFixedWeight_of_mem_starFixedWeights {lam : characterLattice d.toSplitPinning.torus}
    (h : lam ∈ d.starFixedWeights) : d.IsStarFixedWeight lam :=
  (d.mem_starFixedWeights lam).mp h

/-- The Tits obstruction of a simply connected group on the subgroup of weights fixed by the
full star action. -/
def titsObstruction : d.starFixedWeights →+ BrauerGroup.{u, u} k :=
  d.titsObstructionOn (d.corootSpan_eq_top_of_simplyConnected hG) d.starFixedWeights
    (fun _ hx => d.isStarFixedWeight_of_mem_starFixedWeights hx)

theorem titsObstruction_apply (lam : d.starFixedWeights) :
    d.titsObstruction hG lam =
      d.titsObstructionValue (d.corootSpan_eq_top_of_simplyConnected hG) lam.1
        (d.isStarFixedWeight_of_mem_starFixedWeights lam.2) :=
  rfl

/-- On a dominant star-fixed weight, the obstruction is the class of the Tits algebra of any
representation of `G_K` of that highest weight. -/
theorem titsObstruction_eq_classOf (lam : d.starFixedWeights)
    (hdom : d.toSplitPinning.IsDominantWeight lam.1) {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam.1) :
    d.titsObstruction hG lam =
      classOf (d.titsCSAOf hρ (d.isStarFixedWeight_of_mem_starFixedWeights lam.2)) :=
  d.titsObstructionValue_eq_classOf _ _ hdom hρ

/-- Independence of the auxiliary decomposition into dominant star-fixed weights. -/
theorem titsObstruction_eq_sub (lam : d.starFixedWeights)
    {a b : characterLattice d.toSplitPinning.torus}
    (ha : d.toSplitPinning.IsDominantWeight a) (hb : d.toSplitPinning.IsDominantWeight b)
    (hfa : d.IsStarFixedWeight a) (hfb : d.IsStarFixedWeight b) (h : lam.1 = a - b) :
    d.titsObstruction hG lam = d.dominantTitsClass a ha hfa - d.dominantTitsClass b hb hfb :=
  d.titsObstructionValue_eq_sub _ (d.isStarFixedWeight_of_mem_starFixedWeights lam.2) ha hb hfa
    hfb h

/-- Root-span vanishing, given representations over `k` realizing `δ - ∑_{i ∈ O} α_i` as maximal
weights of multiplicity one for a star-fixed `δ`. -/
theorem titsObstruction_eq_zero_of_mem_rootSpan {δ : characterLattice d.toSplitPinning.torus}
    (hδ : d.IsStarFixedWeight δ)
    (hground : ∀ O : Finset d.toSplitPinning.base.support,
      d.HasGroundMaximalWeight (δ - d.simpleRootSum O))
    (lam : d.starFixedWeights) (hlam : lam.1 ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) :
    d.titsObstruction hG lam = 0 :=
  d.titsObstructionValue_eq_zero_of_mem_rootSpan_of_ground _ hδ hground hlam
    (d.isStarFixedWeight_of_mem_starFixedWeights lam.2)

end Langlands.GroupScheme.GaloisPinningData
