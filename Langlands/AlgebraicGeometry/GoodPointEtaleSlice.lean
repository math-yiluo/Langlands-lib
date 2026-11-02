import Langlands.AlgebraicGeometry.GoodPointEtaleSliceProof

/-! # A chosen etale slice through a good point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation SmoothRelationGoodPoint

/-- A pointed, locally finitely presented preimmersion into the base whose
relation pullback is etale over the base. -/
structure GoodPointEtaleSliceData {U R : Scheme.{u}} (t s : R ⟶ U) (x : U) where
  scheme : Scheme.{u}
  toBase : scheme ⟶ U
  point : scheme
  point_over : toBase point = x
  isPreimmersion : IsPreimmersion toBase
  locallyOfFinitePresentation : LocallyOfFinitePresentation toBase
  etale : Etale (pullback.snd toBase t ≫ s)

/-- Choose an etale relation slice through a supplied good point. -/
def goodPointEtaleSlice
    {U R : Scheme.{u}} (t s : R ⟶ U) (hr : IsEquivRel t s) [Smooth s]
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U)
    (x : U) (hgood : IsGoodPoint t s e x) : GoodPointEtaleSliceData t s x :=
  Classical.choice (by
    obtain ⟨Z, g, hpre, hfp, a, hax, he⟩ :=
      exists_etale_slice_of_isGoodPoint t s hr e het hes x hgood
    exact ⟨⟨Z, g, a, hax, hpre, hfp, he⟩⟩)

end Langlands.AlgebraicGeometry
