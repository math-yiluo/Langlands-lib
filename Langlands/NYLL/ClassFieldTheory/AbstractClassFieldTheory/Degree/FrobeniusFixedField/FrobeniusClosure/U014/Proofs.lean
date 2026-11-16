/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 752, 16 November 2026, adapting a draft by Worker 5264
of 15 November 2026:
Extract the proof of M014.014 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusClosure Statements module, give the theorem
the published proposition extensionNormalizedDegree_frobenius_eq_powStatement as its type, unfolded by an initial show,
and expand extensionSubgroup K.field L hLK to its abbreviation body
L.toSubgroup.subgroupOf K.field.toSubgroup. The proof term is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements

/-!
# The normalized degree of a Frobenius lift
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The normalized degree of Frobenius is the corresponding natural profinite power. -/
theorem extensionNormalizedDegree_frobenius_eq_pow (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    extensionNormalizedDegree_frobenius_eq_powStatement D K L hLK σ := by
  show D.extensionNormalizedDegree K L hLK σ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ
  exact (Exists.choose_spec σ.2).2

end DegreeData

end Langlands.NYLL.ClassFormation
