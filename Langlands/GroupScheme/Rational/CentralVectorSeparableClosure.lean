import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.SplitSeriesBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Central vector subgroups over a separable closure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ)

/-- An actual central closed subgroup with a standard vector-group source. -/
structure StandardCentralVectorSubgroup where
  hom : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G
  closed : IsClosedSubgroup hom
  central : IsCentral hom

variable {G n}

/-- Normalize natural vector coordinates on a central closed subgroup. -/
def standardCentralVectorSubgroup
    {V : GroupScheme (Spec (CommRingCat.of k))} (j : V ⟶ G)
    (hj : IsClosedSubgroup j) (hc : IsCentral j)
    (hV : RelativeRoot.IsVectorGroupOfDimension V n) :
    StandardCentralVectorSubgroup G n where
  hom := hV.iso.inv ≫ j
  closed := hj.iso_comp hV.iso.symm
  central := hc.comp hV.iso.inv

/-- Transport a standard central vector subgroup through an ambient
group-scheme isomorphism. -/
def StandardCentralVectorSubgroup.compIso
    (D : StandardCentralVectorSubgroup G n)
    {G' : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ G') :
    StandardCentralVectorSubgroup G' n where
  hom := D.hom ≫ e.hom
  closed := D.closed.comp_iso e
  central := D.central.comp_iso e

/-- A standard central vector subgroup of the actual separable-closure
scalar extension. -/
abbrev SeparableClosureVectorSubgroup
    (G : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ) :=
  StandardCentralVectorSubgroup
    ((baseChange (algebraBaseMap k (SeparableClosure k))).obj G) n

/-- A central closed vector subgroup over any separable algebraic extension
gives one with standard coordinates over the separable closure. -/
def separableClosureVectorSubgroup
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    {V : GroupScheme (Spec (CommRingCat.of K))}
    (j : V ⟶ (baseChange (algebraBaseMap k K)).obj G)
    (hj : IsClosedSubgroup j) (hc : IsCentral j)
    (hV : RelativeRoot.IsVectorGroupOfDimension V n) :
    SeparableClosureVectorSubgroup G n := by
  let f : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra K (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k K (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let b := algebraBaseMap K (SeparableClosure k)
  let D := standardCentralVectorSubgroup
    ((baseChange b).map j) (hj.baseChange b) (hc.baseChange b)
    (hV.baseChange (SeparableClosure k))
  exact D.compIso (baseChangeFieldTowerIso k K (SeparableClosure k) G).symm

end Langlands.GroupScheme
