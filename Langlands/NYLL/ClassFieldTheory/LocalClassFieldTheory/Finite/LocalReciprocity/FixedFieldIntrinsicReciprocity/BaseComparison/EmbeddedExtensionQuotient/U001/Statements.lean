/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the statements of M274.001 and M274.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix and
the suffix Statement. Import the Library modules that publish the
declarations used instead of the source imports. Omit the noncomputable
section, the open lines LocalFieldTheory, KummerTheory and ClassFormation
and the open scoped ValuativeRel line, which these statements do not use,
and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions

/-!
# Embedded extension quotients: transport of extension subgroups

Two closed propositions about an embedded finite Galois extension `E / F`,
with `F / K` finite separable and `E` embedded into `SeparableClosure K` by a
`K`-algebra map `j`. Under the intrinsic-to-ambient base equivalence
`intrinsicBaseEquivAmbientEmbeddedField` attached to the restricted embedding
`i` of `F` and a separable-closure equivalence `e`, an element of the
intrinsic base subgroup lies in the intrinsic extension subgroup for `E / F`
exactly when its image lies in the ambient extension subgroup cut out by the
field ranges of `i` and `j`; and the image of the intrinsic extension subgroup
is that ambient extension subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- Under the embedded-field base equivalence, membership in the intrinsic
extension subgroup for `E / F` is equivalent to membership in the ambient
extension subgroup determined by the two field ranges. -/
def intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement : Prop :=
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
      tau ∈ extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below ↔
        intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
          extensionSubgroup H₀ J₀ hJH

/-- The embedded-field base equivalence maps the intrinsic extension subgroup
for `E / F` onto the ambient subgroup fixing the field range of `E`. -/
def map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement : Prop :=
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
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
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
      let psi :=
        intrinsicBaseEquivAmbientEmbeddedField K F i e
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH

end Langlands.NYLL.LocalClassFieldTheory
