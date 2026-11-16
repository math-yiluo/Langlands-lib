/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M014.029 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusClosureDegree Statements module,
give the theorem the published proposition frobeniusClosureDegree_generatorStatement
as its type, and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. The final source step applies
extensionNormalizedDegree_frobenius_eq_pow (M014.014), whose proof is not yet
published; it is replaced by that theorem's one-line source proof
(Exists.choose_spec σ.2).2. The rest of the proof is the source's.
Omit the @[simp] attribute, open CyclicCohomology, the noncomputable section and
all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Statements

/-!
# The degree of the Frobenius-closure generator
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The degree map sends the canonical Frobenius-closure generator to its expected value. -/
theorem frobeniusClosureDegree_generator (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusClosureDegree_generatorStatement D K L hLK σ := by
  change D.extensionNormalizedDegree K L hLK
      (D.frobeniusInClosure K L hLK σ).1 =
    (Multiplicative.ofAdd (1 : ZHat)) ^
      D.frobeniusExponent K L hLK σ
  have hval :
      (D.frobeniusInClosure K L hLK σ).1 = σ.1 := rfl
  rw [hval]
  -- The source applies M014.014 `extensionNormalizedDegree_frobenius_eq_pow`;
  -- this is its one-line source proof.
  exact (Exists.choose_spec σ.2).2

end DegreeData

end Langlands.NYLL.ClassFormation
