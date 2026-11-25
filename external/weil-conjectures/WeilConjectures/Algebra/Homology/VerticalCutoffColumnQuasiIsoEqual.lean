/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The equal-endpoint case of the nested-cutoff comparison; both sides are zero.
Source: Stacks Project, Homology, Section 12.15, tag 0118, canonical cochain
truncations (https://stacks.math.columbia.edu/tag/0118).
(blueprint: lem-sp-vertical-cutoff-column-quasiiso-equal)

Proof: the cutoff inclusion is degreewise monic, so its compatibility with g forces
g to be the identity. Its cokernel is therefore zero. The lower smart truncation
at a is strictly supported in degrees at least a, and upper truncation preserves
this support while making degrees above a-1 zero. Hence every component of the
window vanishes, including after restriction to the naturals. Every map between
these two zero objects is an isomorphism, and thus a quasi-isomorphism. -/
theorem verticalCutoff_column_quasiIso_equal
    (L : CochainComplex C ℕ) (a : ℤ)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff a).obj L)
    (hg : g ≫ (verticalCutoffι a).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a a).obj L)
    (_hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (a - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  have hi : Mono ((verticalCutoffι a).app L) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((HomologicalComplex.ιTruncLE
      (L.extend ComplexShape.embeddingUpNat)
      (ComplexShape.embeddingUpIntLE (a - 1))).f (ComplexShape.embeddingUpNat.f n))
    infer_instance
  have hg' : g = 𝟙 _ := (cancel_mono ((verticalCutoffι a).app L)).1 (by simpa using hg)
  have : Epi g := by rw [hg']; infer_instance
  have hsrc := isZero_cokernel_of_epi g
  have htgt : IsZero ((verticalWindow a a).obj L) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext n
    let T := CochainComplex.truncLE
      (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a) (a - 1)
    have hz : IsZero (T.X (n : ℤ)) := by
      by_cases hn : (n : ℤ) < a
      · exact CochainComplex.isZero_of_isStrictlyGE T a (n : ℤ) hn
      · exact CochainComplex.isZero_of_isStrictlyLE T (a - 1) (n : ℤ) (by omega)
    exact hz.eq_of_src _ _
  have : IsIso q := isIso_of_source_target_iso_zero q hsrc.isoZero htgt.isoZero
  infer_instance


end HomologicalComplex₂
