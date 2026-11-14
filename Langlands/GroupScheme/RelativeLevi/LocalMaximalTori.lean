import Langlands.GroupScheme.RelativeLevi.BaseChange
import Langlands.GroupScheme.RelativeLevi.MaximalTori
import Langlands.GroupScheme.RelativeLevi.Reductivity
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceStatement

/-! # Étale-local maximal tori in relative Levi subgroups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P L : GroupScheme S}

/-- Given étale-local maximal-torus existence for reductive groups, every
relative Levi has such a cover, and its tori are also maximal in the parabolic. -/
theorem exists_etaleMaximalTorusCover
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P)
    (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : 𝒰.I₀, ∃ (T : CommGroupScheme (𝒰.X j))
        (t : T.toGrp ⟶ (GroupScheme.baseChange (𝒰.f j)).obj L),
        RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
          IsFibrewiseMaximalTorus t ∧
          IsClosedSubgroup (t ≫ (GroupScheme.baseChange (𝒰.f j)).map l) ∧
          IsFibrewiseMaximalTorus (t ≫ (GroupScheme.baseChange (𝒰.f j)).map l) := by
  let : IsAffineHom P.X.hom := hp.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := hExist S L (hl.isReductive hp hG)
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨T, t, hT, hc, ht⟩ := h𝒰 j
  let : Etale (𝒰.f j) := 𝒰.map_prop j
  let : IsAffineHom ((GroupScheme.baseChange (𝒰.f j)).obj P).X.hom :=
    MorphismProperty.pullback_snd P.X.hom (𝒰.f j) hp.isAffineHom
  have hlB := hl.baseChange_etale (𝒰.f j)
  exact ⟨T, t, hT, hc, ht, hc.comp hlB.isClosedSubgroup,
    ht.comp_relativeLevi hc hlB⟩

/-- Choose the actual cover, tori, and inclusions supplied by the preceding
existence result, retaining maximality both in the Levi and in the parabolic. -/
def etaleMaximalTorusCover
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (i : P ⟶ G) (l : L ⟶ P)
    (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup i)
    (hl : IsRelativeLeviSubgroup l) :
    Σ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : 𝒰.I₀, Σ T : CommGroupScheme (𝒰.X j),
        {t : T.toGrp ⟶ (GroupScheme.baseChange (𝒰.f j)).obj L //
          RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
            IsFibrewiseMaximalTorus t ∧
            IsClosedSubgroup (t ≫ (GroupScheme.baseChange (𝒰.f j)).map l) ∧
            IsFibrewiseMaximalTorus (t ≫ (GroupScheme.baseChange (𝒰.f j)).map l)} := by
  classical
  let h := exists_etaleMaximalTorusCover hExist i l hG hp hl
  let 𝒰 := Classical.choose h
  have h𝒰 := Classical.choose_spec h
  refine ⟨𝒰, fun j => ?_⟩
  let T := Classical.choose (h𝒰 j)
  let t := Classical.choose (Classical.choose_spec (h𝒰 j))
  exact ⟨T, t, Classical.choose_spec (Classical.choose_spec (h𝒰 j))⟩

end Langlands.GroupScheme.RelativeLevi
