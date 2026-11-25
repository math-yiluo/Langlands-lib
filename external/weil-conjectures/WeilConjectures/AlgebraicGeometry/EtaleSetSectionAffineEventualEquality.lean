/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleAffineSectionColimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Eventual equality on an affine étale object
Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-sets-section-affine-eventual-equality). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09YQ, affine case of the degree-zero argument using
Tags 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-sets-section-affine-eventual-equality).
Proof: restrict the inverse system to the upper tail of i₀, which is cofinal, and move
j and k to a common stage. Affine transition maps and affine limit projections preserve
objects of the affine étale site. Apply the affine-site colimit presentation (0EYL).
Transport the sheaf and its pullbacks through the full/affine restriction equivalences
(04HR). The unit equations in the affine inverse-image comparison identify the stage
section maps with the specified comparisons. At the limit, composition identifies the
pulled-back system with a constant system; its colimit is the limit inverse image.
The section theorem 09YN identifies its sections on the base change of W₀ with the
filtered colimit of the stage sections. The assumed equality therefore identifies two
representatives in that filtered colimit. The filtered-colimit equality criterion gives
a later stage and arrows where they agree. The comparison composition laws identify
these maps with the two maps displayed below. No finite-cover descent is used here. -/
theorem etaleSetSectionAffineEventualEquality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    [IsAffine W₀.left]
    (j k : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)))
    (t : ((Scheme.etaleSetPullback (D.map k.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj W₀)))
 :
    (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G W₀) s =
      (etaleSetSectionComparison (c.π.app k.left) (D.map k.hom)
        (c.π.app (op i₀)) (c.w k.hom) G W₀) t →
    ∃ (l : Over (op i₀)) (a : l ⟶ j) (b : l ⟶ k),
      (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map l.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) s =
        (etaleSetSectionComparison (D.map b.left) (D.map k.hom) (D.map l.hom)
          ((D.map_comp b.left k.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G W₀) t := by
  classical
  intro hst
  let F := etaleStageSectionDiagram D c i₀ G W₀
  let C := etaleStageSectionCocone D c i₀ G W₀
  obtain ⟨hC⟩ := etaleStageSectionCocone_isColimit D c hc i₀ G W₀
  have he : C.ι.app (op j) s = C.ι.app (op k) t := hst
  obtain ⟨l, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff F hC).mp he
  exact ⟨l.unop, a.unop, b.unop, hab⟩

end AlgebraicGeometry
