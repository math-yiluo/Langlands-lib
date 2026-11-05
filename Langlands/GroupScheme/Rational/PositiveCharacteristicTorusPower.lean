import Langlands.GroupScheme.Nilpotent.CentralTorusProof
import Langlands.GroupScheme.Rational.UnipotentPointsExponent

/-! # A torus contains a p-power of a commutative rational point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- All-test commutativity implies nilpotence of geometric points. -/
theorem isNilpotentGroupScheme_of_isCommMonObj {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsCommMonObj G.X] :
    IsNilpotentGroupScheme G := by
  unfold IsNilpotentGroupScheme
  let : IsCommMonObj ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X :=
    Functor.isCommMonObj_obj (F := Over.pullback (toAlgebraicClosure k)) (M := G.X)
  infer_instance

/-- A torus with an actual point mapping to a p-power of the specified point. -/
structure TorusPowerPoint {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : rationalPoints G) (p : ℕ) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  point : rationalPoints torus.toGrp
  powerIndex : ℕ
  isTorus : IsTorus torus.toGrp
  closed : IsClosedSubgroup inclusion
  point_power : x ^ (p ^ powerIndex) = rationalPoints.map inclusion point

/-- The unipotent quotient by a central maximal torus is killed by a uniform
p-power; the represented kernel then supplies the actual torus point. -/
def positiveCharacteristicTorusPower {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsCommMonObj G.X] (x : rationalPoints G)
    (p : ℕ) [Fact p.Prime] [CharP k p] : TorusPowerPoint G x p :=
  Classical.choice (by
    let D := (isNilpotentGroupScheme_of_isCommMonObj G).centralTorusQuotient
    let : Smooth D.quotient.X.hom := D.smooth_quotient
    let : IsAffineHom D.quotient.X.hom := D.affine_quotient
    let : ConnectedSpace D.quotient.X.left := D.connected_quotient
    have hu : IsUnipotent D.quotient :=
      D.nilpotent_quotient.isUnipotent_of_no_torus D.no_tori
    obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hu
    have hm : x ^ (p ^ r) ∈ (SubgroupFunctor.range D.inclusion).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      rw [← D.fppf_quotient.2.2.2, mem_range_kernelι_iff, MonObj.pow_comp]
      exact hr _ (x ≫ D.projection.hom.hom)
    obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.1 hm
    exact ⟨{
      torus := D.torus
      inclusion := D.inclusion
      point := t
      powerIndex := r
      isTorus := D.maximal_torus.1
      closed := D.maximal_torus.2.1
      point_power := ht.symm }⟩)

end Langlands.GroupScheme
