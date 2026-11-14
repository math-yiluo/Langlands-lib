import Langlands.GroupScheme.RelativeLevi.TorusConjugacy
import Langlands.GroupScheme.RelativeLevi.BaseChange
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange

/-! # Local conjugacy from supplied maximal tori using etale transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P L L' : GroupScheme S}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Supplied ambient maximal tori yield local Levi conjugators once the torus
conjugacy and prescribed-torus Levi statements are supplied. Only the actual
etale cover maps are used to transport the full relative Levi predicates. -/
theorem etaleLocallyRangeConjugate_of_maximalTori_etale
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l')
    (d : MaximalTorusInLevi l) (d' : MaximalTorusInLevi l') :
    EtaleLocallyRangeConjugate.{u, u} l l' (Over.mk (𝟙 S)) := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := hConjugacy S P d.torus d'.torus d.hom d'.hom
    d.isTorus d.isClosed d.isMaximal d'.isTorus d'.isClosed d'.isMaximal
  refine ⟨𝒰, fun k => ?_⟩
  obtain ⟨g, hg⟩ := h𝒰 k
  have hi' := hi.baseChange hG (𝒰.f k)
  have hlb := hl.baseChange_etale (𝒰.f k)
  have hlb' := hl'.baseChange_etale (𝒰.f k)
  have hEq := range_eq_of_conjugate_maximalTori hTorusLevi
    ((GroupScheme.baseChange (𝒰.f k)).map i)
    ((GroupScheme.baseChange (𝒰.f k)).map l)
    ((GroupScheme.baseChange (𝒰.f k)).map l')
    (hG.baseChange (𝒰.f k)) hi' hlb hlb'
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

/-- An actual etale cover with chosen all-test ambient conjugators for supplied
maximal tori inside two given Levi subgroups. -/
def maximalTorusLeviConjugatorCover
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l')
    (d : MaximalTorusInLevi l) (d' : MaximalTorusInLevi l') :
    Σ 𝒰 : S.Cover.{u} (Scheme.precoverage @Etale),
      ∀ k, {g : SubgroupFunctor.etaleCoverObj (T := Over.mk (𝟙 S)) 𝒰 k ⟶ P.X //
        IsRangeConjugator l l' g} := by
  have h := etaleLocallyRangeConjugate_of_maximalTori_etale
    hConjugacy hTorusLevi i l l' hG hi hl hl' d d'
  let 𝒰 := Classical.choose h
  have h𝒰 := Classical.choose_spec h
  exact ⟨𝒰, fun k => ⟨Classical.choose (h𝒰 k), Classical.choose_spec (h𝒰 k)⟩⟩

end Langlands.GroupScheme.RelativeLevi
