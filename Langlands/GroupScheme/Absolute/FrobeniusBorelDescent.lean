import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups

/-! # Descent of a Frobenius-invariant geometric Borel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [Fintype k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {H : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    {i : H ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G}

/-- A Frobenius-invariant algebraic-closure Borel descends as an actual
geometric Borel over the original finite field, with exact pullback recovery. -/
def IsBorelSubgroup.descentOfFrobenius (hi : IsBorelSubgroup i)
    (hF : SubgroupFunctor.range
        (radicalGaloisHom i
          (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))) =
      SubgroupFunctor.range i) : GeometricBorelDescentData i := by
  let : IsGalois k (AlgebraicClosure k) := ⟨⟩
  exact hi.descentOfOverlap
    (Descent.GaloisInvariantClosedSubgroup.overlap_range_eq_of_frobenius
      (k := k) (K := AlgebraicClosure k) (G := G) (i := i)
      hi.isClosedSubgroup hF)

/-- The all-test Frobenius transport formulation supplies the same actual
geometric Borel descent data. -/
def IsBorelSubgroup.descentOfFrobeniusTransport (hi : IsBorelSubgroup i)
    (hF : SubgroupFunctor.galoisTransport k (AlgebraicClosure k) G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))
        (SubgroupFunctor.range i) = SubgroupFunctor.range i) :
    GeometricBorelDescentData i := by
  apply hi.descentOfFrobenius
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _ at hF
  rw [SubgroupFunctor.descentTransport_range] at hF
  exact hF

/-- A connected reductive group with a Frobenius-invariant geometric Borel
is quasi-split over its original finite field. -/
theorem isQuasiSplit_of_borel_frobenius_range_eq
    (hG : IsConnectedReductive G) (hi : IsBorelSubgroup i)
    (hF : SubgroupFunctor.range
        (radicalGaloisHom i
          (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))) =
      SubgroupFunctor.range i) : IsQuasiSplit G := by
  let D := hi.descentOfFrobenius hF
  exact ⟨hG, D.obj, D.inclusion, D.geometricBorel⟩

/-- The canonical Frobenius action on the all-test subgroup functor also
suffices for quasi-splitness. -/
theorem isQuasiSplit_of_borel_frobeniusTransport_eq
    (hG : IsConnectedReductive G) (hi : IsBorelSubgroup i)
    (hF : SubgroupFunctor.galoisTransport k (AlgebraicClosure k) G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))
        (SubgroupFunctor.range i) = SubgroupFunctor.range i) : IsQuasiSplit G := by
  let D := hi.descentOfFrobeniusTransport hF
  exact ⟨hG, D.obj, D.inclusion, D.geometricBorel⟩

end Langlands.GroupScheme
