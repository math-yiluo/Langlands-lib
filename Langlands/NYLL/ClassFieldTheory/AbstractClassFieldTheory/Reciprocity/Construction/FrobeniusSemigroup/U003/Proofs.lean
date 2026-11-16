/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 754 (2026-11-16): extract only the proof of M015.003
`frobeniusMul_coe` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean
(lines 56–65) at commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace ClassFormation with Langlands.NYLL; import only the published
Statements module and state the theorem as its `frobeniusMul_coeStatement`
applied to the source binders, with `CyclicCohomology.extensionSubgroup
(G := G) K.field L hLK` expanded to its Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup` as in that statement. The source
term proof `rfl` is unchanged; the `@[simp]` attribute, the unused
`open CyclicCohomology` and the source `noncomputable section` are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Statements

/-!
# Frobenius multiplication on representatives (NYLL M015.003)

The product of two Frobenius elements in the Frobenius semigroup is
represented by the product of their representatives.
-/

namespace Langlands.NYLL.ClassFormation

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Establishes the identity `(σ * τ).1 = σ.1 * τ.1`. -/
theorem frobeniusMul_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.frobeniusMul_coeStatement K L hLK σ τ :=
  rfl

end DegreeData

end Langlands.NYLL.ClassFormation
