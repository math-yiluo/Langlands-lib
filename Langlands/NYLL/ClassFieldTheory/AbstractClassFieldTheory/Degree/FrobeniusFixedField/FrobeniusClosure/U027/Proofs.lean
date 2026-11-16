/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 752, 16 November 2026, adapting a draft by Worker 5264
of 15 November 2026:
Extract the proof of M014.027 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusClosure Statements module and
the published proof of closedSubgroupGeneratedMap_topologicallyGenerates
(M007.005), give the theorem the published proposition
frobeniusInClosure_topologicallyGeneratesStatement as its type, unfolded by an
initial show, and expand extensionSubgroup K.field L hLK to its abbreviation
body L.toSubgroup.subgroupOf K.field.toSubgroup. The proof is the source's.
Omit open CyclicCohomology, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.U005.Proofs

/-!
# A Frobenius lift topologically generates its closed subgroup
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- By construction, `σ` topologically generates `Γ`. -/
theorem frobeniusInClosure_topologicallyGenerates
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusInClosure_topologicallyGeneratesStatement D K L hLK σ := by
  show TopologicallyGenerates
      ({D.frobeniusInClosure K L hLK σ} : Set
        (D.frobeniusClosure K L hLK σ))
  let φ : Unit →
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :=
    fun _ => σ.1
  have hgen := closedSubgroupGeneratedMap_topologicallyGenerates φ
  have hrange : Set.range (closedSubgroupGeneratedMap φ) =
      ({closedSubgroupGeneratedMap φ ()} : Set
        (closedSubgroupGenerated (Set.range φ))) := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      cases u
      rfl
    · intro hx
      exact ⟨(), hx.symm⟩
  rw [hrange] at hgen
  change TopologicallyGenerates
    ({closedSubgroupGeneratedMap φ ()} : Set
      (closedSubgroupGenerated (Set.range φ) : Subgroup _))
  exact hgen

end DegreeData

end Langlands.NYLL.ClassFormation
