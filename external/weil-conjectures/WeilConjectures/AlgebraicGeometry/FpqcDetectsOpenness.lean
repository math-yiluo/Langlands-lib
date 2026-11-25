/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Basic.Countable.Small

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- An fpqc covering detects openness of a subset of its base.

Source: Stacks Project, Descent, Lemma Tag 03N0, proof after the set construction;
https://stacks.math.columbia.edu/tag/03N0.
(blueprint: lem-weil-pbc-fpqc-detects-openness)

Proof: Work locally on the affine open cover of S and pull back the fpqc family.
The pullback square and continuity preserve the open inverse images. Over Spec R,
use the quasi-compact part of the covering to apply Mathlib's
QuasiCompactCover.exists_hom to its underlying flat cover. This gives a finite
flat affine cover F and a refinement map to the original family. The coproduct
map p from the members of F is flat and surjective. Its source is a finite
coproduct of affine schemes, hence affine, so p is quasi-compact. The preimage of
V under p is open on each coproduct summand, because each structure map factors
through an original covering map. It is therefore open on the coproduct.
Flat.isQuotientMap_of_surjective (Stacks Tag 02JY) now shows that V is open.
The argument permits empty bases and empty finite refinements. -/
theorem isOpen_of_fpqc_preimages
    {S : Scheme.{u}} {I : Type v} {T : I → Scheme.{u}}
    (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (V : Set S) (hV : ∀ i, IsOpen (g i ⁻¹' V)) : IsOpen V := by
  classical
  wlog hS : ∃ R, S = Spec R generalizing S T
  · rw [S.affineCover.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    apply (S.affineCover.f i).isOpenEmbedding.isOpenMap
    let E : S.Cover Scheme.fpqcPrecoverage :=
      { I₀ := I, X := T, f := g, mem₀ := hg }
    let E' := E.pullback₁ (S.affineCover.f i)
    refine this E'.f E'.mem₀ ((S.affineCover.f i) ⁻¹' V) ?_ ⟨_, rfl⟩
    intro j
    change IsOpen (Limits.pullback.fst (S.affineCover.f i) (g j) ⁻¹'
      ((S.affineCover.f i) ⁻¹' V))
    rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      Limits.pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact (hV j).preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hS
  let E : (Spec R).Cover Scheme.fpqcPrecoverage :=
    { I₀ := I, X := T, f := g, mem₀ := hg }
  have : QuasiCompactCover E.forgetQc.toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact hg.1
  obtain ⟨F, e, hfin, _⟩ := QuasiCompactCover.exists_hom E.forgetQc
  have : Finite F.cover.I₀ := hfin
  have : Small.{u} F.cover.I₀ := inferInstance
  have (j : F.I₀) : Flat (F.cover.f j) := F.cover.map_prop j
  let p : (Limits.sigmaObj F.cover.X) ⟶ Spec R := Limits.Sigma.desc F.cover.f
  have : Flat p := inferInstance
  have : Surjective p := Surjective.sigmaDesc_of_union_range_eq_univ F.cover.iUnion_range
  have : QuasiCompact p := inferInstance
  apply (Flat.isQuotientMap_of_surjective p).isOpen_preimage.mp
  rw [(sigmaOpenCover F.cover.X).isOpenCover_opensRange.isOpen_iff_inter]
  intro j
  rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
  apply (Limits.Sigma.ι F.cover.X j).isOpenEmbedding.isOpenMap
  change IsOpen ((Limits.Sigma.ι F.cover.X j) ⁻¹' (p ⁻¹' V))
  rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
  change IsOpen ((Limits.Sigma.ι F.cover.X j ≫ Limits.Sigma.desc F.cover.f) ⁻¹' V)
  rw [Limits.Sigma.ι_comp_desc]
  have he : e.h₀ j ≫ g (e.s₀ j) = F.cover.f j := e.w₀ j
  rw [← he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact (hV (e.s₀ j)).preimage (Scheme.Hom.continuous _)

end AlgebraicGeometry
