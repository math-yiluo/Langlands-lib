import Langlands.GroupScheme.Reductive.OuterIsomorphismFromPinnedCharts
import Langlands.GroupScheme.OuterIsomorphismParameterGeometry

/-! # Full outer geometry for a supplied reductive automorphism scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Constant pinned charts give the required geometry of any supplied exact
outer quotient of a reductive automorphism representative. -/
theorem automorphismOuterGeometry_of_pinnedCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    {S : Scheme.{u}} {G A : GroupScheme S} (hG : IsReductive G)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q)
    (I : GroupIsomorphismScheme G G) (O : OuterIsomorphismScheme I hq.innerAction)
    (hclassMap : LocallyOfFinitePresentation O.classMap.left :=
      letI := hq.isReductive_target.smooth
      O.locallyOfFinitePresentation)
    (hclassMapAffine : IsAffineHom O.classMap.left :=
      letI := hq.isReductive_target.isAffineHom
      O.affine) :
    Etale O.parameter.hom ∧ IsSeparated O.parameter.hom ∧
      IsAffineHom O.classMap.left ∧
      IsClosedImmersion (I.classify
        ((LocalGroupIso.ofIso (Iso.refl G) A.X).twist hq.innerAction (𝟙 A.X))).left ∧
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ i, ∃ D : Type u, Nonempty ((Over.pullback (𝒰.f i)).obj O.parameter ≅
          GroupIsomorphismScheme.constantParameter (𝒰.X i) D) := by
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  let C := AffinePinnedAtlas.ofReductive hG
  have hlocal : ∀ i : C.cover.I₀, ∃ (D : Type u)
      (s : (Over.map (C.cover.f i)).obj
        (GroupIsomorphismScheme.constantParameter (C.cover.X i) D) ⟶ I.parameter),
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) × (T ⟶ (Over.map (C.cover.f i)).obj
          (GroupIsomorphismScheme.constantParameter (C.cover.X i) D)) =>
          prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom hq.innerAction)
            (z.2 ≫ LocalSectionBase.projection (C.cover.f i)
              (GroupIsomorphismScheme.constantParameter (C.cover.X i) D))) := by
    intro i
    let M := (C.chart i).model
    let e : (GroupScheme.baseChange (C.cover.f i)).obj G ≅ M.groupOver (𝟙 M.base) :=
      (C.chart i).iso ≪≫ (baseChangeIdIso M.group).symm
    obtain ⟨D, s, hs⟩ := hchart.constantSection_of_isomorphisms
      M M (𝟙 M.base) (𝟙 M.base) e e
      ((GroupScheme.baseChange (C.cover.f i)).map q) (hq.baseChange (C.cover.f i))
      (I.baseChange (C.cover.f i))
    have hs' : ∀ (T : Over (C.cover.X i)), Function.Bijective
        (fun z : (T ⟶ ((GroupScheme.baseChange (C.cover.f i)).obj A).X) ×
            (T ⟶ GroupIsomorphismScheme.constantParameter (C.cover.X i) D) =>
          lift z.1 (z.2 ≫ s) ≫ (I.baseChange (C.cover.f i)).actionHom
            (hq.innerAction.baseChange (C.cover.f i))) := by
      rw [hq.innerAction_baseChange]
      exact hs
    exact ⟨D, I.localSection (C.cover.f i) s,
      I.localSection_bijective hq.innerAction (C.cover.f i) s hs'⟩
  obtain ⟨he, hs, hc⟩ := O.geometry_of_localConstants C.cover hlocal hclassMap
  let : IsSeparated O.parameter.hom := hs
  exact ⟨he, hs, hclassMapAffine, O.inner_isClosedImmersion, C.cover, hc⟩

/-- Pinned constant charts construct the outer quotient and all geometry
required by the relative automorphism-scheme target, once I is supplied. -/
theorem exists_automorphismOuterGeometry_of_pinnedCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    {S : Scheme.{u}} {G A : GroupScheme S} (hG : IsReductive G)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q) (I : GroupIsomorphismScheme G G) :
    ∃ O : OuterIsomorphismScheme I hq.innerAction,
      Etale O.parameter.hom ∧ IsSeparated O.parameter.hom ∧
      IsAffineHom O.classMap.left ∧
      IsClosedImmersion (I.classify
        ((LocalGroupIso.ofIso (Iso.refl G) A.X).twist hq.innerAction (𝟙 A.X))).left ∧
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ i, ∃ D : Type u, Nonempty ((Over.pullback (𝒰.f i)).obj O.parameter ≅
          GroupIsomorphismScheme.constantParameter (𝒰.X i) D) := by
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  let : IsAffineHom A.X.hom := hq.isReductive_target.isAffineHom
  have ha : hq.innerAction.IsFaithful :=
    AutomorphicAction.isFaithful_of_isFppfQuotient_center hq.isQuotient
      hq.innerAction hq.innerAction_restrict
  let hfree := I.actionHom_injective_of_isFaithful hq.innerAction ha
  let R := GroupIsomorphismScheme.quotientRepresentationOfPinnedOuterCharts hchart hG hG q hq I
  let O := I.outerOfQuotientRepresentation hq.innerAction ha R
  have hclassMap : LocallyOfFinitePresentation R.classMap.left :=
    R.locallyOfFinitePresentation hfree
  let :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      (@IsAffineHom.{u})
  have hclassMapAffine : IsAffineHom R.classMap.left :=
    R.classMap_property hfree (@IsAffineHom.{u}) inferInstance
  exact ⟨O, automorphismOuterGeometry_of_pinnedCharts hchart hG q hq I O
    hclassMap hclassMapAffine⟩

/-- Select the actual outer quotient constructed from pinned constant charts. -/
def automorphismOuterQuotientOfPinnedCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    {S : Scheme.{u}} {G A : GroupScheme S} (hG : IsReductive G)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q) (I : GroupIsomorphismScheme G G) :
    OuterIsomorphismScheme I hq.innerAction :=
  Classical.choose (exists_automorphismOuterGeometry_of_pinnedCharts hchart hG q hq I)

end Langlands.GroupScheme
