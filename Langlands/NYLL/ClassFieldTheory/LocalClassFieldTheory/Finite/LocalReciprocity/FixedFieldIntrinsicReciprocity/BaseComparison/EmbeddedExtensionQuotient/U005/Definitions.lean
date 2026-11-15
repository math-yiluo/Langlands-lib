/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Port the definition ambientEmbeddedExtensionQuotientEquivGaloisGroup
(M274.005) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and replace the source import by the published modules
supplying the used declarations. In the body, prove the subgroup equality
hmap inline (local facts hmem and hmap, following the source proofs of
M274.001 and M274.002) instead of citing
map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField; the defined
equivalence is unchanged. Omit the open lines LocalFieldTheory,
KummerTheory and ClassFormation and the open scoped ValuativeRel line, which
this definition does not use. Omit all other declarations of the source file.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions

/-!
# The ambient embedded extension quotient is the Galois group

For a tower `K ⊆ F ⊆ E` with `F / K` finite separable, `E / F` finite Galois
and a `K`-embedding `j` of `E` into `SeparableClosure K`, the quotient of the
fixing subgroup of the image of `F` by the fixing subgroup of the image of `E`
is identified with `Gal(E / F)`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- The quotient of ambient fixing subgroups attached to an embedded
finite Galois extension is canonically its actual Galois group. -/
noncomputable def
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
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
      letI hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) ≃*
        Gal(E / F) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  -- Pointwise formula for `psi` (source row M273.008).
  have hval :
      ∀ (tau : (intrinsicAbstractBase F).toSubgroup)
        (x : SeparableClosure K),
        (psi tau).1.1 x = e (tau.1 (e.symm x)) :=
    intrinsicBaseEquivAmbientEmbeddedField_apply_val K F i e
  -- Membership transport (source row M274.001).
  have hmem :
      ∀ tau : (intrinsicAbstractBase F).toSubgroup,
        tau ∈ extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below ↔
          psi tau ∈ extensionSubgroup H₀ J₀ hJH := by
    intro tau
    change
      tau.1 ∈ (AlgHom.fieldRange jI).fixingSubgroup ↔
        (psi tau).1 ∈ (AlgHom.fieldRange j).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff,
      IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro htau x hx
      obtain ⟨y, rfl⟩ := hx
      change (psi tau).1.1 (j y) = j y
      rw [hval]
      change e (tau.1 (jI y)) = j y
      rw [htau (jI y) ⟨y, rfl⟩]
      exact e.apply_symm_apply (j y)
    · intro hpsi x hx
      obtain ⟨y, rfl⟩ := hx
      apply e.injective
      change
        e (tau.1 (e.symm (j y))) =
          e (e.symm (j y))
      rw [e.apply_symm_apply]
      rw [← hval]
      exact hpsi (j y) ⟨y, rfl⟩
  -- Image of the intrinsic extension subgroup (source row M274.002).
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    ext sigma
    constructor
    · rintro ⟨tau, htau, rfl⟩
      exact (hmem tau).1 htau
    · intro hsigma
      refine ⟨psi.symm sigma, ?_, psi.apply_symm_apply sigma⟩
      apply (hmem (psi.symm sigma)).2
      rw [psi.apply_symm_apply sigma]
      exact hsigma
  exact
    (QuotientGroup.congr
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below)
      (extensionSubgroup H₀ J₀ hJH)
      psi hmap).symm.trans
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI)


end Langlands.NYLL.LocalClassFieldTheory
