import Langlands.GroupScheme.Rational.GeometricRadicalTorusIntersection
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionProof
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Original-field torus intersections with a supplied geometric radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {P R : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual intersection data for a commutative subgroup and a radical,
including maximality in the specified radical and the full range equality. -/
structure RadicalTorusIntersection (f : T.toGrp ⟶ P) (r : R ⟶ P) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  toT : torus.toGrp ⟶ T.toGrp
  toRadical : torus.toGrp ⟶ R
  isClosedSubgroup_toT : IsClosedSubgroup toT
  isMaximalTorus_toRadical : IsMaximalTorus toRadical
  condition : toT ≫ f = toRadical ≫ r
  range_eq : SubgroupFunctor.range (toT ≫ f) =
    SubgroupFunctor.range f ⊓ SubgroupFunctor.range r

/-- For a smooth geometrically connected closed subgroup of maximal rank, the
canonical intersection is a maximal torus of the supplied geometric radical. -/
theorem isMaximalTorus_solvableRadicalTorusIntersectionSnd
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G)
    (hj : IsClosedSubgroup j) (hP : Smooth P.X.hom)
    (hconnected : ConnectedSpace
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj P).X.left)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (f : T.toGrp ⟶ P) (hfactor : f ≫ j = t)
    (r : R ⟶ P) (hr : IsGeometricSolvableRadical r) :
    IsMaximalTorus (solvableRadicalTorusIntersectionSnd f r hr.1) :=
  isMaximalTorus_solvableRadicalTorusIntersectionSnd_of_geometric
    maximalRankRadicalTorusIntersection maximalTorusBaseChange
    hG j hj hP hconnected t ht f hfactor r hr

/-- The canonical original-field intersection, with its actual maps and
maximality, for a supplied geometric radical in a parabolic. -/
def IsParabolicSubgroup.radicalTorusIntersection
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (f : T.toGrp ⟶ P) (hfactor : f ≫ j = t)
    (r : R ⟶ P) (hr : IsGeometricSolvableRadical r) :
    RadicalTorusIntersection f r := by
  have hmax :
      IsMaximalTorus (solvableRadicalTorusIntersectionSnd f r hr.1) := by
    obtain ⟨S, sT, sR, hsT, hsR, hcomp, hrange⟩ :=
      hj.exists_radicalTorusIntersection_of_structural_inputs
        maximalRankRadicalTorusIntersection maximalTorusBaseChange
        borelContainingSubgroupConnectedStatement hG j t ht f hfactor r hr
    have hf : IsClosedSubgroup f :=
      IsClosedSubgroup.of_comp hj.isClosedSubgroup (by rw [hfactor]; exact ht.2.1)
    let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
    let : Mono r.hom.hom := Over.mono_of_mono_left _
    exact isMaximalTorus_commutativeSubgroupIntersectionSnd_of_representative
      f r sT sR hf hr.1.isClosedSubgroup hsT hsR hcomp hrange
  exact {
    torus := solvableRadicalTorusIntersection f r hr.1
    toT := solvableRadicalTorusIntersectionFst f r hr.1
    toRadical := solvableRadicalTorusIntersectionSnd f r hr.1
    isClosedSubgroup_toT := isClosedSubgroup_solvableRadicalTorusIntersectionFst f r hr.1
    isMaximalTorus_toRadical := hmax
    condition := solvableRadicalTorusIntersection_condition f r hr.1
    range_eq := range_solvableRadicalTorusIntersection f r hr.1
  }

/-- In a parabolic, the full scheme-theoretic intersection of a specified
ambient maximal torus with a supplied geometric radical is a radical maximal
torus. The witnesses and their range equality are over the original field. -/
theorem IsParabolicSubgroup.exists_radicalTorusIntersection
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (f : T.toGrp ⟶ P) (hfactor : f ≫ j = t)
    (r : R ⟶ P) (hr : IsGeometricSolvableRadical r) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R),
      IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
      sT ≫ f = sR ≫ r ∧
      SubgroupFunctor.range (sT ≫ f) =
        SubgroupFunctor.range f ⊓ SubgroupFunctor.range r := by
  let I := hj.radicalTorusIntersection hG j t ht f hfactor r hr
  exact ⟨I.torus, I.toT, I.toRadical, I.isClosedSubgroup_toT,
    I.isMaximalTorus_toRadical, I.condition, I.range_eq⟩

end Langlands.GroupScheme
