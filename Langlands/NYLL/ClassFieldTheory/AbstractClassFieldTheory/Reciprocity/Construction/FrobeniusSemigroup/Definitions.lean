/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions

/-!
# The Frobenius semigroup

Modified by Worker 5264, 15 November 2026: extract M015.001 `frobeniusMul`,
the instance M015.002 `frobeniusElementsMul` and the instance M015.004
`frobeniusElementsSemigroup` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefixing the namespace with
`Langlands.NYLL`. In the body of M015.001, the source applications of the
theorems M014.013 `frobeniusExponent_pos` and M014.014
`extensionNormalizedDegree_frobenius_eq_pow` are replaced by local
hypotheses proved by the source proofs of these theorems. As in the
published sibling modules, `CyclicCohomology.extensionSubgroup (G := G)
K.field L hLK` is expanded to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`, and the then unused
`open CyclicCohomology` is omitted. The source import is replaced by the
published FrobeniusClosure definitions module. The source variable
declaration, docstrings, binders and the remaining bodies are retained. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Multiplication in this construction's Frobenius semigroup. -/
def frobeniusMul (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements K L hLK := by
  let m := D.frobeniusExponent K L hLK σ
  let n := D.frobeniusExponent K L hLK τ
  have hσpos : 0 < D.frobeniusExponent K L hLK σ :=
    (Exists.choose_spec σ.2).1
  have hσpow :
      D.extensionNormalizedDegree K L hLK σ.1 =
        (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ :=
    (Exists.choose_spec σ.2).2
  have hτpow :
      D.extensionNormalizedDegree K L hLK τ.1 =
        (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK τ :=
    (Exists.choose_spec τ.2).2
  refine ⟨σ.1 * τ.1, m + n,
    Nat.add_pos_left hσpos n, ?_⟩
  rw [map_mul,
    hσpow,
    hτpow,
    pow_add]

/--
Multiplication of Frobenius elements is induced by multiplication of their quotient
representatives.
-/
instance frobeniusElementsMul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Mul (D.FrobeniusElements K L hLK) :=
  ⟨D.frobeniusMul K L hLK⟩

/-- The induced multiplication makes the Frobenius elements a semigroup. -/
instance frobeniusElementsSemigroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Semigroup (D.FrobeniusElements K L hLK) where
  mul_assoc σ τ υ := by
    apply Subtype.ext
    change (σ.1 * τ.1) * υ.1 = σ.1 * (τ.1 * υ.1)
    exact mul_assoc σ.1 τ.1 υ.1

end DegreeData

end
end Langlands.NYLL.ClassFormation
