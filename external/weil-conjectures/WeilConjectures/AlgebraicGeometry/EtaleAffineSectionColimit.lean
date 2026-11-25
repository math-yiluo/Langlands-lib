/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStageSectionCocone
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLiftAffine
import WeilConjectures.AlgebraicGeometry.EtaleAffineSectionSameStageEquality
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The canonical cocone of affine étale section sets
Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09YQ, affine-site argument using Tags 0EYL,
04HR and 09YN (blueprint: lem-weil-pbc-affine-section-cocone-colimit).

Proof: The opposite of the category of stages over i₀ is the directed upper tail,
which is cofinal in I. Restrict the limiting scheme diagram to this tail. Its
projections are affine. The affine étale site presentation of 0EYL identifies its
limit site with the filtered colimit of the affine stage sites. Transport G and
its inverse images along the full/affine restriction equivalences of 04HR. The
unit-compatible inverse-image comparison identifies transition section maps with
the maps in etaleStageSectionDiagram. Pulling these sheaves to the limit gives a
diagram canonically isomorphic to the constant diagram on the inverse image of G;
the composition unit equations supply its compatibility. A nonempty filtered
category is connected, so the constant diagram has that sheaf as colimit. Apply
09YN to the base changes of the affine object W₀: coverings are finite, hence
sections commute with this filtered sheaf colimit. Transport the resulting
colimit cocone back along the restriction equivalences. The same unit equations
identify its legs with etaleStageSectionCocone. This proves the universal property
of the specified cocone, including both existence and uniqueness of its descents.
Empty affine objects cause no exception: their section sets are singletons. -/
theorem etaleStageSectionCocone_isColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    [IsAffine W₀.left] : Nonempty (IsColimit (etaleStageSectionCocone D c i₀ G W₀)) := by
  classical
  let F := etaleStageSectionDiagram D c i₀ G W₀
  let C := etaleStageSectionCocone D c i₀ G W₀
  refine ⟨Types.FilteredColimit.isColimitOf' F C ?_ ?_⟩
  · intro t
    obtain ⟨j, s, hs⟩ := etaleSetSectionLift_affine D c hc i₀ G W₀ t
    exact ⟨op j, s, hs.symm⟩
  · intro j s t hst
    obtain ⟨k, a, ha⟩ := etaleAffineSection_sameStageEquality D c hc i₀ G W₀
      j.unop s t hst
    exact ⟨op k, a.op, ha⟩

end AlgebraicGeometry
