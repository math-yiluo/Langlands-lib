/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

import all WeilConjectures.Algebra.Homology.LowerTruncationTransitionKernel
import all WeilConjectures.Algebra.Homology.UpperTruncationStepSES

/-!
# Epimorphy of a truncated lower projection

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations and the two-term kernel argument.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma inclusion_f_isIso (K : CochainComplex C ℤ) (t n : ℤ) (hn : n < t) :
    IsIso ((K.ιTruncLE t).f n) := by
  change IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE t).op).f n).unop
  have h : (ComplexShape.embeddingUpIntLE t).op.f (t - n).natAbs = n := by
    change t - ((t - n).natAbs : ℤ) = n
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hb : ¬ (ComplexShape.embeddingUpIntLE t).op.BoundaryGE (t - n).natAbs := by
    simp only [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    omega
  have : IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE t).op).f n) := by
    rw [HomologicalComplex.πTruncGE,
      ComplexShape.Embedding.liftExtend_f _ _ _ h,
      HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ h hb]
    infer_instance
  infer_instance

private lemma cycles_projection_epi (K : CochainComplex C ℤ) (a t : ℤ) (hat : a ≤ t) :
    Epi (HomologicalComplex.cyclesMap (K.πTruncGE a) t) := by
  by_cases h : a = t
  · subst t
    have hprev : (ComplexShape.up ℤ).prev a = a - 1 :=
      ComplexShape.prev_eq' _ (by simp)
    have hd : (K.truncGE a).d (a - 1) a = 0 :=
      ((K.truncGE a).isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _
    have : IsIso ((K.truncGE a).homologyπ a) :=
      (K.truncGE a).isIso_homologyπ (a - 1) a hprev hd
    have : QuasiIsoAt (K.πTruncGE a) a := K.quasiIsoAt_πTruncGE a a (by omega)
    have he : Epi (HomologicalComplex.cyclesMap (K.πTruncGE a) a ≫
        (K.truncGE a).homologyπ a) := by
      rw [← HomologicalComplex.homologyπ_naturality]
      infer_instance
    exact (epi_comp_iff_of_isIso _ _).mp he
  · have hat' : a < t := by omega
    have hpi : IsIso ((K.πTruncGE a).f t) := by
      rw [CochainComplex.pi_f_above K a t hat']
      infer_instance
    have hnext : (ComplexShape.up ℤ).next t = t + 1 :=
      ComplexShape.next_eq' _ (by simp)
    let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) t).map
      (K.πTruncGE a)
    have : IsIso φ.τ₂ := hpi
    have : Mono φ.τ₃ := by
      change Mono ((K.πTruncGE a).f ((ComplexShape.up ℤ).next t))
      rw [hnext, CochainComplex.pi_f_above K a (t + 1) (by omega)]
      infer_instance
    exact inferInstanceAs (Epi (ShortComplex.cyclesMap φ))

/-- The lower truncation projection remains degreewise epic after an upper
truncation whose endpoint is at least the lower endpoint.
Source: Stacks Project, Homology Tag 0118 (homology-section-truncations).
(blueprint: lem-sp-vertical-cutoff-comparison-epi)

Proof: above t the target is zero. Below t the upper truncation inclusions
are invertible, and naturality identifies the map with the epic lower
truncation projection. At t the upper truncations identify with cycles.
If a < t, the projection in degrees t and t + 1 is invertible, hence so is
the cycles map. If a = t, homology of the lower truncation has no incoming
boundaries; its cycles-to-homology map is invertible. Naturality of homology
and the quasi-isomorphism at a then imply that the cycles map is epic.
The conjugating upper-boundary identifications preserve epimorphy. -/
theorem verticalCutoff_comparison_epi
    (K : CochainComplex C ℤ) (a t : ℤ) (hat : a ≤ t) (n : ℤ) :
    Epi ((CochainComplex.truncLEMap (K.πTruncGE a) t).f n) := by
  by_cases hn : t < n
  · exact ((K.truncGE a).truncLE t).isZero_of_isStrictlyLE t n hn |>.epi _
  · by_cases hn' : n < t
    · have : IsIso ((K.ιTruncLE t).f n) := inclusion_f_isIso K t n hn'
      have : IsIso (((K.truncGE a).ιTruncLE t).f n) :=
        inclusion_f_isIso (K.truncGE a) t n hn'
      have : Epi ((K.πTruncGE a).f n) :=
        inferInstanceAs (Epi ((HomologicalComplex.πTruncGE K
          (ComplexShape.embeddingUpIntGE a)).f n))
      have h := congrArg (fun f => f.f n)
        (CochainComplex.ιTruncLE_naturality (K.πTruncGE a) t)
      simp only [HomologicalComplex.comp_f] at h
      have he : Epi ((CochainComplex.truncLEMap (K.πTruncGE a) t).f n ≫
          ((K.truncGE a).ιTruncLE t).f n) := by
        rw [h]
        infer_instance
      exact (epi_comp_iff_of_isIso _ _).mp he
    · have hnt : n = t := by omega
      subst n
      have : Epi (HomologicalComplex.cyclesMap (K.πTruncGE a) t) :=
        cycles_projection_epi K a t hat
      have he : Epi ((CochainComplex.truncLEMap (K.πTruncGE a) t).f t ≫
          ((K.truncGE a).truncLEXIsoCycles t).hom) := by
        rw [CochainComplex.truncLEXIsoCycles_naturality]
        infer_instance
      exact (epi_comp_iff_of_isIso _ _).mp he

end HomologicalComplex₂
