/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions

/-!
# Targets: degree-zero commutation and degrees of Frobenius powers

Modified by Worker 5264, 15 November 2026: state the source theorems
M038.001 `DegreeData.extensionInertia_commutes_of_mem_extensionSubgroup`,
M038.002 `DegreeData.quotientPower_card_commutes_degreeZero` and the private
M038.003 `DegreeData.extensionNormalizedDegree_pow_of_degreeOne` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, name the private theorem's target
`Langlands.NYLL.PortInternal.M038.d003Statement`, replace the source import
by focused published imports, omit the source `open KummerTheory` (no
declaration of that namespace is imported or used), and keep the source
universe, the other opens, section,
variable declaration, namespace, binders and statements (including the
`let` of M038.002) unchanged. The proofs and the rest of the source file are
omitted. The unused-variables linter is switched off for each target, whose
hypotheses `hk`, `hq`, `hPL`, `hPnormal`, `hτ` and `hφ` are not used in the
Prop-valued body. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: an element fixing `L` commutes modulo `G_{\widetilde L}` with every
degree-zero element of `G(\widetilde L/K)`.  Group-theoretically this is
`[G_L,I_K] ⊆ G_L ∩ I_K = G_{\widetilde L}`; it is the reason the
fields fixed by the powers of `φⁿ` in the universal norm-descent lemma are stable under the
elements `τᵢ` occurring in `(*)`. -/
def extensionInertia_commutes_of_mem_extensionSubgroupStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) : Prop :=
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k

set_option linter.unusedVariables false in
/-- Target: let `P/K` be a finite Galois subextension of `\widetilde L/K`
containing `L`.  The `|G(P/K)|`-th power of every element of
`G(\widetilde L/K)` fixes `P`, hence commutes with the degree-zero kernel.
This is the precise finite-stage input behind the choice
`n = [M:K]`, `σ = φⁿ`. -/
def quotientPower_card_commutes_degreeZeroStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) : Prop :=
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n

set_option linter.unusedVariables false in
/-- Target for the private source theorem
`DegreeData.extensionNormalizedDegree_pow_of_degreeOne`: the `n`-th power of a
Frobenius element of exponent one has normalized degree `(ofAdd 1) ^ n`. -/
def _root_.Langlands.NYLL.PortInternal.M038.d003Statement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) : Prop :=
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n

end DegreeData

end degreeOnePowerFields

end

end Langlands.NYLL.ClassFormation
