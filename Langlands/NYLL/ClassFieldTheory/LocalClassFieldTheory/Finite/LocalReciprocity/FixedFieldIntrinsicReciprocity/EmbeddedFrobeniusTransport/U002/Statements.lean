/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statements of M281.002 and M281.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix and
the suffix Statement. Import the Library module that publishes the two
equivalences instead of the source imports. Omit the noncomputable section,
the open lines, which these statements do not need, and all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions

/-!
# Continuity of the intrinsic-to-ambient base equivalences: statements

Two closed propositions: the multiplicative equivalences
`intrinsicBaseEquivAmbientFixedField` and
`intrinsicBaseEquivAmbientEmbeddedField` are continuous for the subspace
topologies induced by the Krull topologies of the absolute Galois groups.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The equivalence on absolute Galois base subgroups induced by a fixed-field
separable-closure equivalence is continuous. -/
def intrinsicBaseEquivAmbientFixedField_continuousStatement : Prop :=
  ∀ (K : Type) [Field K]
    (H : Langlands.NYLL.ClassFormation.FiniteAbstractField
      Gal(SeparableClosure K/K)),
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K),
      Continuous (intrinsicBaseEquivAmbientFixedField K H e)

/-- The intrinsic absolute Galois equivalence induced by an embedding into the
ambient separable closure is continuous. -/
def intrinsicBaseEquivAmbientEmbeddedField_continuousStatement : Prop :=
  ∀ (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K),
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      Continuous
        (intrinsicBaseEquivAmbientEmbeddedField K F i e)

end Langlands.NYLL.LocalClassFieldTheory
