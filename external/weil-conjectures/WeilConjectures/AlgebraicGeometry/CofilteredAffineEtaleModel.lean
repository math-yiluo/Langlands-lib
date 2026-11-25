/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final

/-! # Affine etale models over cofiltered scheme limits

Source: Stacks Project, Tags 0EYL and 01ZM.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An affine etale object over a qcqs inverse limit descends to an affine etale
object at a stage, for an arbitrary small cofiltered index.
Source: Stacks Project, Tags 0EYL and 01ZM.
(blueprint: lem-sc-cofiltered-affine-etale-model).

Proof: Choose a final functor from a nonempty directed poset to the opposite
index. Its left opposite is initial, so whiskering the scheme cone preserves
its limiting property. Compactness, quasi-separatedness and affineness of
transition maps are inherited by this reindexing. Apply affineEtale_common_models
to the singleton family consisting of U. The obtained model and pullback square
are already over an object of the original index. Empty U is included in affine
etale descent and requires no separate choice of a point. -/
theorem exists_affineEtale_model_of_cofiltered
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (U : c.pt.Etale) [IsAffine U.left] :
    ∃ (i : I) (V : (D.obj i).Etale) (_ : IsAffine V.left)
      (r : U.left ⟶ V.left), IsPullback r U.hom V.hom (c.π.app i) := by
  classical
  obtain ⟨A, hA, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Iᵒᵖ
  let D' := R.leftOp ⋙ D
  let (i : Aᵒᵖ) : CompactSpace (D'.obj i) := inferInstanceAs
    (CompactSpace (D.obj (R.obj i.unop).unop))
  let (i : Aᵒᵖ) : QuasiSeparatedSpace (D'.obj i) := inferInstanceAs
    (QuasiSeparatedSpace (D.obj (R.obj i.unop).unop))
  let (i j : Aᵒᵖ) (a : i ⟶ j) : IsAffineHom (D'.map a) := inferInstanceAs
    (IsAffineHom (D.map (R.map a.unop).unop))
  let c' := c.whisker R.leftOp
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c).symm hc
  obtain ⟨i, V, hV⟩ := affineEtale_common_models D' c' hc' 1 (fun _ ↦ ⟨U, inferInstance⟩)
  obtain ⟨r, hr⟩ := hV 0
  exact ⟨(R.obj i).unop, (V 0).obj, (V 0).property, r, hr⟩

end AlgebraicGeometry.Scheme
