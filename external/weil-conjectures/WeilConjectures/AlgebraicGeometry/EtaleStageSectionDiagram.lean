/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonLaws

/-! # Canonical affine étale section system
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Stage section sets and their canonical transition maps over a fixed base stage.
Source: Stacks Project, Tag 09YQ (blueprint: def-weil-pbc-affine-section-diagram). -/
noncomputable def etaleStageSectionDiagram
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) : (Over (op i₀))ᵒᵖ ⥤ Type (u + 1) where
  obj j := ((Scheme.etaleSetPullback (D.map j.unop.hom)).obj G).obj.obj
    (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.unop.hom)).obj W₀))
  map {j k} a := etaleSetSectionComparison (D.map a.unop.left) (D.map j.unop.hom)
    (D.map k.unop.hom)
    ((D.map_comp a.unop.left j.unop.hom).symm.trans
      (congrArg (fun t ↦ D.map t) a.unop.w)) G W₀
  map_id j := (etaleSetSectionComparisonLaws D c i₀ G W₀).1 j.unop
  map_comp a b := ((etaleSetSectionComparisonLaws D c i₀ G W₀).2.1
    _ _ _ a.unop b.unop).symm

end AlgebraicGeometry
