/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.InertiaQuotientImage.Statements
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# NYLL M017.002: the image of `G_L` in the inertia quotient is closed

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.extensionImageInInertiaQuotient_isClosedStatement` (M017.002) by
the source proof of `DegreeData.extensionImageInInertiaQuotient_isClosed` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source imports
by published modules and Mathlib's `Mathlib.Topology.Algebra.OpenSubgroup`,
and omit the rest of the source file.

Modified by Worker 738, 16 November 2026: omit the source's unused first proof
step `let : IsClosed (D.extensionInertiaWithin K.field L hLK : Set _) :=
D.extensionInertiaWithin_isClosed K L hLK` and with it the import of the
M014.022 proof. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `G_L` in `G_K / I_L` is closed.  This is the compact-image
step implicit in the Galois correspondence used. -/
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    extensionImageInInertiaQuotient_isClosedStatement D K L hLK := by
  show IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))
  let E := extensionSubgroup K.field L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)

end DegreeData

end

end Langlands.NYLL.ClassFormation
