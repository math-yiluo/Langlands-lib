/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStageSectionDiagram

/-! # Canonical affine étale section system
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The limit section comparisons form a cocone.
Source: Stacks Project, Tag 09YQ (blueprint: def-weil-pbc-affine-section-cocone). -/
noncomputable def etaleStageSectionCocone
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) : Cocone (etaleStageSectionDiagram D c i₀ G W₀) where
  pt := ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
    (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))
  ι :=
    { app := fun j ↦ etaleSetSectionComparison (c.π.app j.unop.left)
        (D.map j.unop.hom) (c.π.app (op i₀)) (c.w j.unop.hom) G W₀
      naturality := fun _ _ a ↦ by
        simpa [etaleStageSectionDiagram] using
          (etaleSetSectionComparisonLaws D c i₀ G W₀).2.2 _ _ a.unop }

end AlgebraicGeometry
