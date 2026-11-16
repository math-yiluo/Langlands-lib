/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 15 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement
of M274.006 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709, following the source proof.
Add the Langlands.NYLL namespace prefix and import only the published
statement module. The source proof introduces a local proof hmap of the
subgroup equality by citing the M274.002 theorem
map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField and passes it to
QuotientGroup.congr inside a change; here that argument is a placeholder
solved by unification with the goal, so hmap and the citation are omitted.
Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U006.Statements

/-!
# Embedded extension quotients: the equivalence on transported classes

The proof of the published closed proposition that the ambient embedded
quotient equivalence sends the class of a transported intrinsic automorphism
to the image of its intrinsic class.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- The ambient embedded quotient equivalence sends the class of a transported
intrinsic automorphism to its class in the finite Galois quotient. -/
theorem ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk :
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  change
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI
        ((QuotientGroup.congr
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below)
          (extensionSubgroup H₀ J₀ hJH)
          psi _).symm
          (QuotientGroup.mk
            (psi tau))) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI (QuotientGroup.mk tau)
  congr 1
  change
    QuotientGroup.mk
        (psi.symm (psi tau)) =
      QuotientGroup.mk tau
  rw [psi.symm_apply_apply]

end Langlands.NYLL.LocalClassFieldTheory
