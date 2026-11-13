/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statements of M274.003 and M274.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix and
the suffix Statement. Write the source abbreviation
CyclicCohomology.extensionSubgroup H₀ J₀ hJH as its body
J₀.toSubgroup.subgroupOf H₀.toSubgroup, which does not use the inclusion
proof hJH, and therefore omit the local proof hJH. In the M274.004 statement,
omit the local instance _hTargetNormal, which the conclusion does not use,
and name the then unused binder _e. Qualify the published name
closedFixingSubgroup, and import its Library module and
Mathlib.FieldTheory.IsSepClosed instead of the source imports. Omit all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Mathlib.FieldTheory.IsSepClosed

/-!
# Embedded extension quotients: normality and finiteness statements

Two closed propositions about an embedded finite Galois extension `E / F`,
with `F / K` finite separable and `E` embedded into `SeparableClosure K` by a
`K`-algebra map `j`. Inside the fixing subgroup of the image of `F`, the fixing
subgroup of the image of `E` is normal, and it has only finitely many left
cosets.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The fixing subgroup cut out by an embedded finite Galois extension is
normal inside the fixing subgroup of its embedded base field. -/
def ambientEmbeddedExtensionSubgroup_normalStatement : Prop :=
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
      let _e := e
      let H₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      (J₀.toSubgroup.subgroupOf H₀.toSubgroup).Normal

/-- The relative quotient of fixing subgroups attached to an embedded
finite Galois extension is finite. -/
def ambientEmbeddedExtensionQuotient_finiteStatement : Prop :=
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
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let H₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      Finite
        (H₀.toSubgroup ⧸ J₀.toSubgroup.subgroupOf H₀.toSubgroup)

end Langlands.NYLL.LocalClassFieldTheory
