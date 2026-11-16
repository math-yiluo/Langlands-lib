/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs

/-!
# NYLL M076.011: every intermediate coset is closed

Modified by Worker 756, 16 November 2026: extract the proof of M076.011
`FiniteGaloisSubextension.intermediateCoset_isClosed` (lines 165–171) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and state the theorem as the published Statement applied to
the source parameters. The source-private definition M076.005
`representativeIntermediateCoset` is inlined as an explicit image set, and the
source-private helpers M076.007, M076.008 and M076.010 are proved here as
private theorems under their source names. The cited published theorem
`Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed` (M020.008) is
imported. The paired Markdown records every modification. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Source M076.007 with M076.005 inlined: the right translate of `G_L` by a
chosen representative of `q` consists exactly of the elements of class `q`. -/
private theorem mem_representativeIntermediateCoset_iff
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ (fun y : K.toSubgroup =>
        y * Quotient.out (L.extensionQuotientMulEquiv q)) ''
      (extensionSubgroup K L.field L.below : Set K.toSubgroup) ↔
      L.extensionQuotientMk x = q := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    apply L.extensionQuotientMulEquiv.injective
    change (QuotientGroup.mk
        (h * Quotient.out (L.extensionQuotientMulEquiv q)) :
          K.toSubgroup ⧸ extensionSubgroup K L.field L.below) =
      L.extensionQuotientMulEquiv q
    rw [← Quotient.out_eq' (L.extensionQuotientMulEquiv q)]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv, mul_assoc] using hh
  · intro hx
    have hxout :
        (QuotientGroup.mk' (extensionSubgroup K L.field L.below)) x =
          (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below)) x =
              L.extensionQuotientMulEquiv (L.extensionQuotientMk x) := rfl
        _ = L.extensionQuotientMulEquiv q :=
          congrArg L.extensionQuotientMulEquiv hx
        _ = (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) :=
          (Quotient.out_eq' (L.extensionQuotientMulEquiv q)).symm
    have hdiv : x / Quotient.out (L.extensionQuotientMulEquiv q) ∈
        extensionSubgroup K L.field L.below :=
      QuotientGroup.eq_iff_div_mem.mp hxout
    refine ⟨x / Quotient.out (L.extensionQuotientMulEquiv q), hdiv, ?_⟩
    simp [div_eq_mul_inv, mul_assoc]

/-- Source M076.008 with M076.005 inlined: the canonical fiber equals the
representative-based right translate of `G_L`. -/
private theorem intermediateCoset_eq_representativeIntermediateCoset
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) :
    L.intermediateCoset q =
      (fun y : K.toSubgroup =>
          y * Quotient.out (L.extensionQuotientMulEquiv q)) ''
        (extensionSubgroup K L.field L.below : Set K.toSubgroup) := by
  ext x
  exact (mem_representativeIntermediateCoset_iff L q x).symm

/-- Source M076.010 with M076.005 inlined: a right translate of the closed
subgroup `G_L ≤ G_K` is closed. -/
private theorem representativeIntermediateCoset_isClosed [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) :
    IsClosed ((fun y : K.toSubgroup =>
        y * Quotient.out (L.extensionQuotientMulEquiv q)) ''
      (extensionSubgroup K L.field L.below : Set K.toSubgroup)) := by
  exact isClosedMap_mul_right
    (Quotient.out (L.extensionQuotientMulEquiv q)) _
    (Langlands.NYLL.KummerTheory.extensionSubgroup_isClosed K L.field L.below)

/-- Every coset in the preceding union is closed: it is the image of the
closed subgroup `G_L ≤ G_K` under right translation. -/
theorem intermediateCoset_isClosed [IsTopologicalGroup G]
    {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : intermediateCoset_isClosedStatement L q := by
  change IsClosed (L.intermediateCoset q)
  rw [intermediateCoset_eq_representativeIntermediateCoset]
  exact representativeIntermediateCoset_isClosed L q

end FiniteGaloisSubextension

end
end Langlands.NYLL.ClassFormation
