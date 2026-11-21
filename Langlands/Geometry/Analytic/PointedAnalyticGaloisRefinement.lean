import Langlands.Geometry.Analytic.AnalyticGaloisCover

/-! # Pointed relative analytic Galois refinements -/

noncomputable section

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory TopologicalSpace

universe u v

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A pointed finite analytic Galois cover over an open of `Y`, with
a map to the source of `f` over `Y` and a singleton fibre over `y`. -/
structure PointedAnalyticGaloisRefinement
    {W Y : LocalizedCategory.{u, v, v} (K := K)} (f : W ⟶ Y)
    (y : localizedSpaceFunctor.obj Y) where
  baseOpen : Opens (localizedSpaceFunctor.obj Y)
  mem_baseOpen : y ∈ baseOpen
  source : LocalizedCategory.{u, v, v} (K := K)
  Γ : Type
  [instGroup : Group Γ]
  [instFinite : Finite Γ]
  p : source ⟶ domainObj Y ((presentationOf Y).openDomain
    (baseOpen : Set (localizedSpaceFunctor.obj Y)) baseOpen.isOpen)
  geometry : AnalyticGaloisCover Γ p
  lift : source ⟶ W
  factors : lift ≫ f =
    p ≫ domainι Y ((presentationOf Y).openDomain
      (baseOpen : Set (localizedSpaceFunctor.obj Y)) baseOpen.isOpen)
  point : localizedSpaceFunctor.obj source
  map_point : localizedSpaceFunctor.map p point = ⟨y, mem_baseOpen⟩
  unique_point : ∀ x : localizedSpaceFunctor.obj source,
    localizedSpaceFunctor.map p x = ⟨y, mem_baseOpen⟩ → x = point

attribute [instance] PointedAnalyticGaloisRefinement.instGroup
  PointedAnalyticGaloisRefinement.instFinite

/-- A pointed étale arrow is dominated, over an open neighbourhood of its
image point, by a pointed finite analytic Galois cover with singleton fibre. -/
def PointedAnalyticGaloisRefinementStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {W Y : LocalizedCategory.{u, v, v} (K := K)} (f : W ⟶ Y), etale f →
    ∀ w : localizedSpaceFunctor.obj W,
      Nonempty (PointedAnalyticGaloisRefinement f (localizedSpaceFunctor.map f w))

end Langlands.Analytic.SaturatedAtlasPresentation
