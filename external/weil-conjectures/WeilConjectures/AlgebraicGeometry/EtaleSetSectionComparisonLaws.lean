/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition

/-! # An intermediate step in continuity of étale sections
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-section-comparison-laws).
Proof: expand each comparison into its adjunction unit, the unit-compatible composition
isomorphism, and pullback pasting. Naturality of the unit moves restriction maps through
units. For two successive comparisons, associativity of the composition isomorphisms
combines them into the single comparison. The pullback pasting maps agree because their
projections agree. For the identity map, the identity adjunction and uniqueness of the
unit-compatible comparison cancel the identity-base-change isomorphism. Apply the same
composition calculation to a transition followed by a cone projection; cone naturality
identifies the composite with the other projection. These arguments require neither
qcqs hypotheses nor a limit cone. -/
theorem etaleSetSectionComparisonLaws
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale)
    :
    (∀ j : Over (op i₀),
        etaleSetSectionComparison (D.map (𝟙 j : j ⟶ j).left) (D.map j.hom) (D.map j.hom)
          ((D.map_comp (𝟙 j : j ⟶ j).left j.hom).symm.trans
            (congrArg (fun t : j.left ⟶ op i₀ ↦ D.map t) (𝟙 j : j ⟶ j).w)) G W₀ = 𝟙 _) ∧
      (∀ (j k l : Over (op i₀)) (a : k ⟶ j) (b : l ⟶ k),
        (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) ≫
          (etaleSetSectionComparison (D.map b.left) (D.map k.hom) (D.map l.hom)
          ((D.map_comp b.left k.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G W₀) =
          (etaleSetSectionComparison (D.map (b ≫ a).left) (D.map j.hom) (D.map l.hom)
          ((D.map_comp (b ≫ a).left j.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) (b ≫ a).w)) G W₀)) ∧
      (∀ (j k : Over (op i₀)) (a : k ⟶ j),
        (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) ≫
          (etaleSetSectionComparison (c.π.app k.left) (D.map k.hom)
          (c.π.app (op i₀)) (c.w k.hom) G W₀) =
        (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [Over.id_left, D.map_id] using
      etaleSetSectionComparisonIdentity (D.map j.hom) G W₀
  · intro j k l a b
    simpa only [Over.comp_left, D.map_comp] using
      etaleSetSectionComparisonComposition (D.map a.left) (D.map b.left)
        (D.map j.hom) (D.map k.hom) (D.map l.hom)
        ((D.map_comp a.left j.hom).symm.trans
          (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w))
        ((D.map_comp b.left k.hom).symm.trans
          (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G W₀
  · intro j k a
    have h := etaleSetSectionComparisonComposition (D.map a.left) (c.π.app k.left)
      (D.map j.hom) (D.map k.hom) (c.π.app (op i₀))
      ((D.map_comp a.left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) (c.w k.hom) G W₀
    simpa only [c.w a.left] using h

end AlgebraicGeometry
