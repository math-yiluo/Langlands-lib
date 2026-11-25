/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Coproducts and the supported right adjoint

Source: Stacks Project, Tag 09BM; Bhatt--Scholze, Lemma 6.3.14(4)
(blueprint: lem-weil-pbc-supported-right-adjoint-coproducts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c z u vc vz vu s
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory

-- The unbounded derived comparisons require elaborating several functor structures.
/-- The supported right adjoint preserves any coproduct preserved by the open
localization endofunctor.
Source: Stacks Project, Tag 09BM; Bhatt--Scholze, Lemma 6.3.14(4)
(blueprint: lem-weil-pbc-supported-right-adjoint-coproducts).

Proof: closed restriction and open restriction jointly detect isomorphisms.
For an object killed by open restriction, the closed-adjunction unit becomes
invertible after closed restriction, by the triangle identity, and after open
restriction, because both objects are zero. Thus the object lies in the closed
essential image. The recollement theorem gives its supported localization
triangle. Take these triangles on the family and on its coproduct. Naturality
of recollement supplies a morphism from their coproduct triangle to the latter
triangle. The middle component is the identity; the third is the invertible
open-localization coproduct comparison. The triangulated five lemma inverts the
first component, which is the supported-endofunctor comparison. Fully faithful
closed inclusion reflects colimits, giving the right-adjoint conclusion. -/
theorem supportedRightAdjoint_preservesCoproduct
    {C : Type c} [Category.{vc} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {Z : Type z} [Category.{vz} Z]
    {U : Type u} [Category.{vu} U] [Preadditive U] [HasZeroObject U]
    [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
    (i : Z ⥤ C) (pi : C ⥤ Z) (j : C ⥤ U) (rj : U ⥤ C) (G : C ⥤ Z)
    [j.CommShift ℤ] [j.IsTriangulated]
    (ai : pi ⊣ i) [IsIso ai.counit] (aj : j ⊣ rj) [IsIso aj.counit]
    (ag : i ⊣ G)
    (hzero : ∀ P, IsZero (j.obj (i.obj P)))
    (hdet : ∀ {M N : C} (f : M ⟶ N), IsIso (pi.map f) → IsIso (j.map f) → IsIso f)
    (I : Type s) [HasCoproducts.{s} C] (M : I → C)
    [PreservesColimit (Discrete.functor M) (j ⋙ rj)] :
    PreservesColimit (Discrete.functor M) G := by
  classical
  have hi := ai.fullyFaithfulROfIsIsoCounit
  have := hi.full
  have := hi.faithful
  have hess (K : C) (hK : IsZero (j.obj K)) : i.essImage K := by
    have hc : IsIso (pi.map (ai.unit.app K)) := Recollement.isIso_map_unit_app pi ai K
    have ho : IsIso (j.map (ai.unit.app K)) :=
      isIso_of_source_target_iso_zero _ hK.isoZero (hzero (pi.obj K)).isoZero
    have := hdet (ai.unit.app K) hc ho
    exact ⟨pi.obj K, ⟨(asIso (ai.unit.app K)).symm⟩⟩
  have hw (K : C) : ∃ w, Recollement.triangle aj ag K w ∈ distTriang C :=
    (Recollement.existsUnique_distTriang_counit_unit aj ag hi hzero hess K).exists
  choose w hw using hw
  let T (s : I) := Recollement.triangle aj ag (M s) (w (M s))
  have hs (s : I) : ∃ τ : T s ⟶ Recollement.triangle aj ag (∐ M) (w (∐ M)),
      τ.hom₁ = i.map (G.map (Sigma.ι M s)) ∧ τ.hom₂ = Sigma.ι M s ∧
        τ.hom₃ = rj.map (j.map (Sigma.ι M s)) :=
    Recollement.exists_triangleHom aj ag hzero (Sigma.ι M s) (hw (M s)) (hw (∐ M))
  choose τ hτ using hs
  let t := coproductTriangle.desc T τ
  have h₂ : t.hom₂ = 𝟙 (∐ M) := by
    apply Sigma.hom_ext
    intro s
    simp only [t, coproductTriangle.desc_hom₂, Sigma.ι_comp_desc, (hτ s).2.1]
    change Sigma.ι M s = Sigma.ι M s ≫ 𝟙 (∐ M)
    rw [Category.comp_id]
  have h₃ : t.hom₃ = sigmaComparison (j ⋙ rj) M := by
    apply Sigma.hom_ext
    intro s
    simp only [t, coproductTriangle.desc_hom₃, Sigma.ι_comp_desc, (hτ s).2.2]
    change (j ⋙ rj).map (Sigma.ι M s) =
      Sigma.ι (fun s ↦ (j ⋙ rj).obj (M s)) s ≫ sigmaComparison (j ⋙ rj) M
    exact (ι_comp_sigmaComparison (j ⋙ rj) M s).symm
  have h₁ : t.hom₁ = sigmaComparison (G ⋙ i) M := by
    apply Sigma.hom_ext
    intro s
    simp only [t, coproductTriangle.desc_hom₁, Sigma.ι_comp_desc, (hτ s).1]
    change (G ⋙ i).map (Sigma.ι M s) =
      Sigma.ι (fun s ↦ (G ⋙ i).obj (M s)) s ≫ sigmaComparison (G ⋙ i) M
    exact (ι_comp_sigmaComparison (G ⋙ i) M s).symm
  have ht₂ : IsIso t.hom₂ := by rw [h₂]; exact IsIso.id (∐ M)
  have ht₃ : IsIso t.hom₃ := by rw [h₃]; infer_instance
  have ht₁ := isIso₁_of_isIso₂₃ t (coproductTriangle_distinguished T (fun s ↦ hw (M s)))
    (hw (∐ M)) ht₂ ht₃
  have : IsIso (sigmaComparison (G ⋙ i) M) := by rw [← h₁]; exact ht₁
  have : PreservesColimit (Discrete.functor M) (G ⋙ i) :=
    PreservesCoproduct.of_iso_comparison (G ⋙ i) M
  exact preservesColimit_of_reflects_of_preserves G i

end CategoryTheory
