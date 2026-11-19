import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners

/-! # The Tits obstruction on the integral weight lattice of an inner group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) (hG : IsSimplyConnected G) (hinner : d.IsInnerStarAction)

/-- For the vertex-inner action, every integral weight defines a weight in the actual star-fixed subgroup. -/
def fixedWeightOfInner (lam : characterLattice d.toSplitPinning.torus) : d.starFixedWeights :=
  ⟨lam, (d.mem_starFixedWeights lam).mpr (d.isStarFixedWeight_of_inner hG hinner lam)⟩

variable [IsGalois k K]

/-- The actual Tits obstruction on all integral weights of the inner simply connected group. -/
def innerTitsObstruction : characterLattice d.toSplitPinning.torus →+ BrauerGroup.{u, u} k :=
  (d.titsObstruction hG).comp
    { toFun := d.fixedWeightOfInner hG hinner
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

@[simp] theorem innerTitsObstruction_apply (lam : characterLattice d.toSplitPinning.torus) :
    d.innerTitsObstruction hG hinner lam = d.titsObstruction hG (d.fixedWeightOfInner hG hinner lam) :=
  rfl

/-- A highest-weight representation of the actual split group computes the obstruction. -/
theorem innerTitsObstruction_eq_classOf
    {lam : characterLattice d.toSplitPinning.torus} {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) :
    d.innerTitsObstruction hG hinner lam =
      classOf (d.titsCSAOf hρ (d.isStarFixedWeight_of_inner hG hinner lam)) :=
  d.titsObstruction_eq_classOf hG (d.fixedWeightOfInner hG hinner lam) hρ.isDominantWeight hρ

/-- Any expression of the weight as a difference of dominant integral weights gives the same class. -/
theorem innerTitsObstruction_eq_sub {lam a b : characterLattice d.toSplitPinning.torus}
    (ha : d.toSplitPinning.IsDominantWeight a) (hb : d.toSplitPinning.IsDominantWeight b)
    (h : lam = a - b) :
    d.innerTitsObstruction hG hinner lam =
      d.dominantTitsClass a ha (d.isStarFixedWeight_of_inner hG hinner a) -
        d.dominantTitsClass b hb (d.isStarFixedWeight_of_inner hG hinner b) :=
  d.titsObstruction_eq_sub hG (d.fixedWeightOfInner hG hinner lam) ha hb
    (d.isStarFixedWeight_of_inner hG hinner a) (d.isStarFixedWeight_of_inner hG hinner b) h

/-- Tensoring actual CSA representatives represents the sum of integral weights. -/
theorem innerTitsObstruction_add_eq_classOf_tensor {lam mu : characterLattice d.toSplitPinning.torus}
    {A B : CSA.{u, u} k}
    (hA : d.innerTitsObstruction hG hinner lam = classOf A)
    (hB : d.innerTitsObstruction hG hinner mu = classOf B) :
    d.innerTitsObstruction hG hinner (lam + mu) = classOf (tensor A B) := by
  rw [map_add, hA, hB, classOf_tensor]

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hG : IsSimplyConnected G) (hinner : IsInnerAbsoluteStarAction hG.isSemisimple.isConnectedReductive)

/-- The full integral-weight Tits obstruction for the canonical absolute Galois pinning. -/
def innerAbsoluteTitsObstruction : characterLattice
    (GaloisPinningData.ofSeparableClosure hG.isSemisimple.isConnectedReductive).toSplitPinning.torus
      →+ BrauerGroup.{u, u} k :=
  (GaloisPinningData.ofSeparableClosure hG.isSemisimple.isConnectedReductive).innerTitsObstruction
    hG hinner

end Langlands.GroupScheme
