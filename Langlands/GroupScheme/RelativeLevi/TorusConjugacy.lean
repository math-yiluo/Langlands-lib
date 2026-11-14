import Langlands.GroupScheme.RelativeLevi.AmbientTransport
import Langlands.GroupScheme.RelativeLevi.LocalConjugacyReduction
import Langlands.GroupScheme.RelativeLevi.TorusLeviStatement
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyStatement
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Local conjugacy of Levi subgroups from supplied maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S S' : Scheme.{u}} {G P L L' : GroupScheme S}

/-- A relative maximal torus of the ambient group whose image is contained
in the specified subgroup. No torus-existence assertion is made. -/
structure MaximalTorusInLevi (l : L ⟶ P) where
  torus : CommGroupScheme S
  hom : torus.toGrp ⟶ P
  isTorus : RelativeTorus.IsTorus torus.toGrp
  isClosed : IsClosedSubgroup hom
  isMaximal : IsFibrewiseMaximalTorus hom
  contains : SubgroupFunctor.range hom ≤ SubgroupFunctor.range l

namespace MaximalTorusInLevi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change retains the actual torus and its inclusion in the pulled-back
subgroup. Smoothness and affineness concern only the ambient group. -/
def baseChange {l : L ⟶ P} (d : MaximalTorusInLevi l)
    [Smooth P.X.hom] [IsAffineHom P.X.hom] (b : S' ⟶ S) :
    MaximalTorusInLevi ((GroupScheme.baseChange b).map l) where
  torus := (CommGroupScheme.baseChange b).obj d.torus
  hom := (GroupScheme.baseChange b).map d.hom
  isTorus := d.isTorus.baseChange b
  isClosed := d.isClosed.baseChange b
  isMaximal := by
    intro s
    exact isMaximalTorus_baseChange_comp b (S'.fromSpecResidueField s) d.torus d.hom
      (d.isMaximal.fieldPoint (S'.fromSpecResidueField s ≫ b))
  contains := by
    change SubgroupFunctor.range ((GroupScheme.baseChange b).map d.hom) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map l)
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    exact SubgroupFunctor.baseChange_mono b d.contains

end MaximalTorusInLevi

/-- If each maximal torus lies in a unique Levi, a conjugator of supplied
maximal tori also conjugates the Levi subgroups containing them. -/
theorem range_eq_of_conjugate_maximalTori
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l')
    (d : MaximalTorusInLevi l) (d' : MaximalTorusInLevi l')
    (g : Over.mk (𝟙 S) ⟶ P.X)
    (hg : SubgroupFunctor.range (d.hom ≫ (P.innerIso g).hom) =
      SubgroupFunctor.range d'.hom) :
    SubgroupFunctor.range l' =
      SubgroupFunctor.range (l ≫ (P.innerIso g).hom) := by
  obtain ⟨M, m, _, _, hm⟩ := hTorusLevi S G P i d'.torus d'.hom
    hG hi d'.isTorus d'.isClosed d'.isMaximal
  have hcontains : SubgroupFunctor.range d'.hom ≤
      SubgroupFunctor.range (l ≫ (P.innerIso g).hom) := by
    rw [← hg]
    exact SubgroupFunctor.range_comp_mono d.contains _
  exact (hm L' l' hl' d'.contains).trans
    (hm L (l ≫ (P.innerIso g).hom) (hl.comp_iso (P.innerIso g)) hcontains).symm

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Supplied ambient maximal tori yield local Levi conjugators once the torus
conjugacy and prescribed-torus Levi statements are supplied. Stability of the
relative parabolic and Levi predicates is an explicit input. -/
theorem etaleLocallyRangeConjugate_of_maximalTori
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (d : MaximalTorusInLevi l) (d' : MaximalTorusInLevi l')
    (hStable : ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
      IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map i) ∧
        IsRelativeLeviSubgroup ((GroupScheme.baseChange b).map l) ∧
        IsRelativeLeviSubgroup ((GroupScheme.baseChange b).map l')) :
    EtaleLocallyRangeConjugate.{u, u} l l' (Over.mk (𝟙 S)) := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := hConjugacy S P d.torus d'.torus d.hom d'.hom
    d.isTorus d.isClosed d.isMaximal d'.isTorus d'.isClosed d'.isMaximal
  refine ⟨𝒰, fun k => ?_⟩
  obtain ⟨g, hg⟩ := h𝒰 k
  obtain ⟨hi', hl, hl'⟩ := hStable (𝒰.X k) (𝒰.f k)
  have hEq := range_eq_of_conjugate_maximalTori hTorusLevi
    ((GroupScheme.baseChange (𝒰.f k)).map i)
    ((GroupScheme.baseChange (𝒰.f k)).map l)
    ((GroupScheme.baseChange (𝒰.f k)).map l')
    (hG.baseChange (𝒰.f k)) hi' hl hl'
    (d.baseChange (𝒰.f k)) (d'.baseChange (𝒰.f k)) g hg
  let x : Over.mk (𝒰.f k) ⟶ P.X := baseChangeBasePointsEquiv (𝒰.f k) P g
  have hx : IsRangeConjugator l l' x := by
    apply (isRangeConjugator_iff_range_baseChange_eq l l' (Over.mk (𝒰.f k)) x).mpr
    change SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f k)).map l') =
      SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f k)).map l ≫
        (((GroupScheme.baseChange (𝒰.f k)).obj P).innerIso
          ((baseChangeBasePointsEquiv (𝒰.f k) P).symm
            (baseChangeBasePointsEquiv (𝒰.f k) P g))).hom)
    rw [MulEquiv.symm_apply_apply]
    exact hEq
  let a : SubgroupFunctor.etaleCoverObj (T := Over.mk (𝟙 S)) 𝒰 k ⟶
      Over.mk (𝒰.f k) :=
    Over.homMk (𝟙 (𝒰.X k)) (by simp)
  exact ⟨a ≫ x, hx.comp a⟩

end Langlands.GroupScheme.RelativeLevi
