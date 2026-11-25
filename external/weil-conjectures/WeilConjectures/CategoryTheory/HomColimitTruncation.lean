/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.QuasiIso
/-! # Good truncation and canonical Hom continuity -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
  {I : Type v} [SmallCategory I] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]

omit [HasDerivedCategory A] in
private theorem quasiIso_colimMap {D E : I ⥤ CochainComplex A ℤ} (α : D ⟶ E)
    (hα : ∀ i, QuasiIso (α.app i)) : QuasiIso (colimMap α) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (.up ℤ) q
  have (i : I) : IsIso ((Functor.whiskerRight α H).app i) := by
    let := hα i
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (α.app i) q))
  have : IsIso (Functor.whiskerRight α H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    infer_instance
  have heq : colimit.post D H ≫ H.map (colimMap α) =
      colimMap (Functor.whiskerRight α H) ≫ colimit.post E H := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
    rw [← H.map_comp, ι_colimMap, H.map_comp]
    rfl
  have : IsIso (colimit.post D H ≫ H.map (colimMap α)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimit.post D H) (H.map (colimMap α))

private theorem comparison_iso_transfer
    {B : Type*} [Category B] {J : Type*} [Category J]
    {D E : J ⥤ B} [HasColimitsOfShape J B]
    (c : Cocone D) (d : Cocone E) (e : D ≅ E) (v : c.pt ≅ d.pt)
    (hleg : ∀ i, c.ι.app i ≫ v.hom = e.hom.app i ≫ d.ι.app i)
    (hd : IsIso (colimit.desc E d)) : IsIso (colimit.desc D c) := by
  have heq : colimit.desc D c ≫ v.hom = colimMap e.hom ≫ colimit.desc E d := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
    exact hleg i
  have : IsIso (colimit.desc D c ≫ v.hom) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right (colimit.desc D c) v.hom

/-- It suffices to check canonical Hom continuity on termwise bounded-below diagrams.
Source: Bhatt--Scholze, proof of Lemma 6.3.14, and Lemma 6.8.12; exact filtered
colimits and good truncation.
(auxiliary; not a blueprint node)

Proof. Truncate the diagram at its common cohomological lower bound. Each truncation
map is a quasi-isomorphism. Exact colimits preserve these quasi-isomorphisms, since
homology preserves exact colimits and the homology-colimit comparisons are natural.
The original colimit cocone maps canonically to the truncated colimit cocone. Its
vertex map is the composite of the unique colimit isomorphism and the colimit of the
truncation maps, so it too is a quasi-isomorphism. Apply localization, shifting and
additive Hom. The resulting diagrams and vertices are isomorphic with compatible
cocone legs. The colimit universal property identifies the two comparison arrows;
invertibility for the truncated diagram implies invertibility for the original one.
-/
theorem homColimitProperty_of_strictly_bounded [IsFiltered I]
    (K : DerivedCategory A)
    (h : ∀ (N : I ⥤ CochainComplex A ℤ),
      (∃ a : ℤ, ∀ i r, r < a → IsZero ((N.obj i).X r)) →
      homColimitProperty (N ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone (colimit.cocone N)) K)
    (D : I ⥤ CochainComplex A ℤ) (c : Cocone D) (hc : IsColimit c)
    (hD : ∃ a : ℤ, ∀ i, (DerivedCategory.Q.obj (D.obj i)).IsGE a) :
    homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c) K := by
  obtain ⟨a, ha⟩ := hD
  let N := D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A
  let α : D ⟶ N := Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have hα (i : I) : QuasiIso (α.app i) := by
    apply (CochainComplex.quasiIso_πTruncGE_iff _ a).2
    exact (DerivedCategory.isGE_Q_obj_iff _ a).1 (ha i)
  have hN : ∃ a : ℤ, ∀ i r, r < a → IsZero ((N.obj i).X r) := by
    refine ⟨a, fun i r hr ↦ ?_⟩
    exact CochainComplex.isZero_of_isStrictlyGE ((D.obj i).truncGE a) a r hr
  let β := hc.desc ((Cocone.precompose α).obj (colimit.cocone N))
  have hβ : β = (hc.coconePointUniqueUpToIso (colimit.isColimit D)).hom ≫ colimMap α := by
    apply hc.hom_ext
    intro i
    simp only [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    change c.ι.app i ≫ hc.desc ((Cocone.precompose α).obj (colimit.cocone N)) =
      colimit.ι D i ≫ colimMap α
    rw [hc.fac, ι_colimMap]
    rfl
  have : QuasiIso (colimMap α) := quasiIso_colimMap α hα
  have : IsIso (DerivedCategory.Q.map (colimMap α)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have : IsIso (DerivedCategory.Q.map β) := by
    rw [hβ, Functor.map_comp]
    infer_instance
  have (i : I) : IsIso ((Functor.whiskerRight α DerivedCategory.Q).app i) := by
    change IsIso (DerivedCategory.Q.map (α.app i))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hα i
  have : IsIso (Functor.whiskerRight α DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    infer_instance
  intro n
  let H := shiftFunctor (DerivedCategory A) n ⋙ preadditiveCoyoneda.obj (Opposite.op K)
  let e := (asIso (Functor.whiskerRight α DerivedCategory.Q))
  apply comparison_iso_transfer
    (H.mapCocone (DerivedCategory.Q.mapCocone c))
    (H.mapCocone (DerivedCategory.Q.mapCocone (colimit.cocone N)))
    (Functor.isoWhiskerRight e H) (H.mapIso (asIso (DerivedCategory.Q.map β)))
  · intro i
    change H.map (DerivedCategory.Q.map (c.ι.app i)) ≫
        H.map (DerivedCategory.Q.map β) =
      H.map (DerivedCategory.Q.map (α.app i)) ≫
        H.map (DerivedCategory.Q.map (colimit.ι N i))
    rw [← H.map_comp, ← H.map_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp]
    congr 2
    exact hc.fac ((Cocone.precompose α).obj (colimit.cocone N)) i
  · exact h N hN n
end CategoryTheory
