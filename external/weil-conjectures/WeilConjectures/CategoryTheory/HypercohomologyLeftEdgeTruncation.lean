/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.CategoryTheory.RightDerivedSingleDegreeComparison

/-! # Compute the spectral left edge on an object bounded above in its edge degree

Source: Stacks Project, derived.tex, Tag 015J.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

set_option backward.isDefEq.respectTransparency false in
/-- The left edge followed by its coefficient comparison is the image of the canonical
map to the single-degree truncation, followed by the shifted degree-zero comparison.
Source: Stacks Project, derived.tex, Tag 015J.
(blueprint: lem-pc-hypercohomology-left-edge-truncation)

Proof: The left edge is the image of the projection to truncation GE n followed by
the inverse of the image of GE n applied to the inclusion LT(n+1). Since K is LE n,
that inclusion is an isomorphism. Naturality of the GE projection rewrites this composite
as the image of the inverse inclusion followed by the GE projection on LT(n+1) K.
The target comparison factors by definition through the canonical single-degree truncation
isomorphism and the shifted degree-zero comparison. Combine these factorizations. -/
theorem hypercohomologyLeftEdge_truncation (K : DerivedCategory.Plus B) (n : ℕ)
    [DerivedCategory.Plus.TStructure.t.IsGE K 0]
    [DerivedCategory.Plus.TStructure.t.IsLE K n] :
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    letI : IsIso ((t.truncLTι (n + 1)).app K) :=
      (t.isLE_iff_isIso_truncLTι_app (n : ℤ) (n + 1) rfl K).mp inferInstance
    let f := CategoryTheory.inv ((t.truncLTι (n + 1)).app K) ≫
      (t.truncGEπ n).app ((t.truncLT (n + 1)).obj K) ≫
      (DerivedCategory.Plus.eTruncLTCompETruncGEIso (n : ℤ)).hom.app K
    (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge n ≫
        (G.hypercohomologyLeftEdgeTargetIso n).hom.app K =
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map f) ≫
        (G.rightDerivedSingleDegreeComparison n).hom.app
          ((DerivedCategory.Plus.homologyFunctor B n).obj K) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor C n
  let RG := G.rightDerivedFunctorPlus
  let i := (t.truncLTι (n + 1)).app K
  let p := (t.truncGEπ n).app ((t.truncLT (n + 1)).obj K)
  let j := (t.truncGE n).map i
  have hi : IsIso i :=
    (t.isLE_iff_isIso_truncLTι_app (n : ℤ) (n + 1) rfl K).mp inferInstance
  have hj : IsIso j := inferInstance
  have hp : (t.truncGEπ n).app K ≫ CategoryTheory.inv j = CategoryTheory.inv i ≫ p := by
    apply (cancel_epi i).mp
    apply (cancel_mono j).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
    exact (t.truncGEπ n).naturality i
  have he : (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge n =
      H.map (RG.map (CategoryTheory.inv i ≫ p)) := by
    dsimp [hypercohomologySpectralObjectFunctor, Abelian.SpectralObject.leftEdge,
      mapHomologicalSpectralObject, Triangulated.SpectralObject.mapHomologicalFunctor,
      mapTriangulatedSpectralObject, Triangulated.SpectralObject.mapTriangulatedFunctor,
      Triangulated.TStructure.spectralObjectFunctor, Triangulated.TStructure.spectralObject,
      Triangulated.TStructure.ω₁]
    simp only [Functor.map_id, NatTrans.hcomp_app, NatTrans.id_app]
    dsimp
    simp only [Category.id_comp, Functor.map_id, Category.comp_id]
    change H.map (RG.map ((t.truncGEπ n).app K)) ≫
      CategoryTheory.inv (H.map (RG.map j)) = _
    rw [← Functor.map_inv, ← Functor.map_inv, ← Functor.map_comp, ← Functor.map_comp, hp]
  dsimp only
  rw [he]
  simp only [hypercohomologyLeftEdgeTargetIso, rightDerivedSingleDegreeComparison,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    NatTrans.comp_app, Category.assoc]
  rfl

end CategoryTheory.Functor
