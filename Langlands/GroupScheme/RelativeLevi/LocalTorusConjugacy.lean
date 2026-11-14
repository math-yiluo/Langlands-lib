import Langlands.GroupScheme.RelativeLevi.LocalMaximalTori
import Langlands.GroupScheme.RelativeLevi.EtaleTorusConjugacy
import Langlands.GroupScheme.RelativeLevi.ConjugacyCovers

/-! # Local Levi conjugacy from the relative torus statements -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P L L' : GroupScheme S}

/-- One supplied maximal torus suffices: construct a torus in the other Levi
on a cover, conjugate on a further cover, and compose the covers. -/
theorem etaleLocallyRangeConjugate_of_one_maximalTorus
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l')
    (d : MaximalTorusInLevi l) :
    EtaleLocallyRangeConjugate.{u, u} l l' (Over.mk (𝟙 S)) := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := exists_etaleMaximalTorusCover hExist i l' hG hi hl'
  apply etaleLocallyRangeConjugate_of_cover l l' (Over.mk (𝟙 S)) 𝒰
  intro k
  obtain ⟨T, t, hT, _, _, hcA, htA⟩ := h𝒰 k
  let d' : MaximalTorusInLevi ((GroupScheme.baseChange (𝒰.f k)).map l') :=
    ⟨T, t ≫ (GroupScheme.baseChange (𝒰.f k)).map l', hT, hcA, htA,
      SubgroupFunctor.range_comp_le t _⟩
  have hLocal := etaleLocallyRangeConjugate_of_maximalTori_etale
    hConjugacy hTorusLevi
    ((GroupScheme.baseChange (𝒰.f k)).map i)
    ((GroupScheme.baseChange (𝒰.f k)).map l)
    ((GroupScheme.baseChange (𝒰.f k)).map l')
    (hG.baseChange (𝒰.f k)) (hi.baseChange hG (𝒰.f k))
    (hl.baseChange_etale (𝒰.f k)) (hl'.baseChange_etale (𝒰.f k))
    (d.baseChange (𝒰.f k)) d'
  have hProj := etaleLocallyRangeConjugate_of_baseChange
    (𝒰.f k) l l' (Over.mk (𝟙 (𝒰.X k))) hLocal
  change EtaleLocallyRangeConjugate l l' (Over.mk (𝟙 _ ≫ 𝒰.f k)) at hProj
  change EtaleLocallyRangeConjugate l l' (Over.mk (𝒰.f k ≫ 𝟙 S))
  simpa only [Category.id_comp, Category.comp_id] using hProj

/-- The three complete relative torus statements imply local ambient
conjugacy of relative Levi subgroups, with no supplied maximal tori. -/
theorem etaleLocallyRangeConjugate_of_torusStatements
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l') :
    EtaleLocallyRangeConjugate.{u, u} l l' (Over.mk (𝟙 S)) := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := exists_etaleMaximalTorusCover hExist i l hG hi hl
  apply etaleLocallyRangeConjugate_of_cover l l' (Over.mk (𝟙 S)) 𝒰
  intro k
  obtain ⟨T, t, hT, _, _, hcA, htA⟩ := h𝒰 k
  let d : MaximalTorusInLevi ((GroupScheme.baseChange (𝒰.f k)).map l) :=
    ⟨T, t ≫ (GroupScheme.baseChange (𝒰.f k)).map l, hT, hcA, htA,
      SubgroupFunctor.range_comp_le t _⟩
  have hLocal := etaleLocallyRangeConjugate_of_one_maximalTorus
    hExist hConjugacy hTorusLevi
    ((GroupScheme.baseChange (𝒰.f k)).map i)
    ((GroupScheme.baseChange (𝒰.f k)).map l)
    ((GroupScheme.baseChange (𝒰.f k)).map l')
    (hG.baseChange (𝒰.f k)) (hi.baseChange hG (𝒰.f k))
    (hl.baseChange_etale (𝒰.f k)) (hl'.baseChange_etale (𝒰.f k)) d
  have hProj := etaleLocallyRangeConjugate_of_baseChange
    (𝒰.f k) l l' (Over.mk (𝟙 (𝒰.X k))) hLocal
  change EtaleLocallyRangeConjugate l l' (Over.mk (𝟙 _ ≫ 𝒰.f k)) at hProj
  change EtaleLocallyRangeConjugate l l' (Over.mk (𝒰.f k ≫ 𝟙 S))
  simpa only [Category.id_comp, Category.comp_id] using hProj

/-- Choose the resulting actual cover and certified ambient conjugators. -/
def relativeLeviConjugatorCover
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l') :
    Σ 𝒰 : S.Cover.{u} (Scheme.precoverage @Etale),
      ∀ k, {g : SubgroupFunctor.etaleCoverObj (T := Over.mk (𝟙 S)) 𝒰 k ⟶ P.X //
        IsRangeConjugator l l' g} := by
  have h := etaleLocallyRangeConjugate_of_torusStatements
    hExist hConjugacy hTorusLevi i l l' hG hi hl hl'
  let 𝒰 := Classical.choose h
  have h𝒰 := Classical.choose_spec h
  exact ⟨𝒰, fun k => ⟨Classical.choose (h𝒰 k), Classical.choose_spec (h𝒰 k)⟩⟩

end Langlands.GroupScheme.RelativeLevi
