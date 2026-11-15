/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the statements of M274.006 and M274.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix and
the suffix Statement. Import the Library module that publishes
ambientEmbeddedExtensionQuotientEquivGaloisGroup (M274.005), which imports
the other declarations used, instead of the source imports. Omit the
noncomputable section, the open lines LocalFieldTheory, KummerTheory and
ClassFormation and the open scoped ValuativeRel line, which these statements
do not use, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U005.Definitions

/-!
# Embedded extension quotients: values of the Galois group equivalence

Two closed propositions about the equivalence
`ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e` between the
ambient embedded extension quotient and `Gal(E / F)`. On the class of the
image of an intrinsic automorphism `tau` it agrees with the class of `tau`
under `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`; and the
automorphism of `E` attached to the class of an ambient automorphism `rho`
acts, after applying `j`, as `rho` does on `j(E)`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- The ambient embedded quotient equivalence sends the class of a transported
intrinsic automorphism to its class in the finite Galois quotient. -/
def ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement : Prop :=
  ∀ (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K),
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
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
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e
          (QuotientGroup.mk
            (intrinsicBaseEquivAmbientEmbeddedField
              K F i e tau)) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau)

/-- Evaluating the ambient embedded quotient class on an element of `E`
agrees, after applying the embedding, with the original ambient automorphism. -/
def ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement : Prop :=
  ∀ (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K),
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (rho :
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup)
      (x : E),
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
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨algebraMap F E z, rfl⟩
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      j
          (ambientEmbeddedExtensionQuotientEquivGaloisGroup
            K F E j e (QuotientGroup.mk rho) x) =
        rho.1.1 (j x)

end Langlands.NYLL.LocalClassFieldTheory
