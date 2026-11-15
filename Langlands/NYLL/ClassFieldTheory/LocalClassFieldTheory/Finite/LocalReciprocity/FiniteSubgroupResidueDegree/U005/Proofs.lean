/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 127, 15 November 2026:
Extract the proof of M250.005 (lines 80-97) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespace, import the U005 Statements
module and the published M249.010 proof module instead of the source
imports, and prove the published closed proposition by introducing its six
binders (the section variable K, its four instance binders and the
theorem's binder H) and then following the source proof. The unused source
binding `let E := abstractFixedField K (SeparableClosure K) H` is dropped;
all other source steps are unchanged, and the source name
localSeparableDecompositionGroup_eq_top now denotes the published closed
M249.010 theorem, applied to K as in the source. Keep only the source open
lines this proof needs; omit the source noncomputable section and all other
source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U005.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U010.Proofs

/-!
# Full decomposition group over the fixed field of a closed subgroup: proof

Every automorphism of `SeparableClosure K` over the fixed field of a closed
subgroup `H` is, after restricting scalars to `K`, an automorphism over `K`,
and these all preserve the chosen valuation ring by M249.010.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped Pointwise
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- Every automorphism over the fixed field preserves the selected extension
valuation.  This is the base-change form of the full decomposition-group
statement proved for `K`. -/
theorem localAbstractFixedDecompositionGroup_eq_top :
    localAbstractFixedDecompositionGroup_eq_topStatement := by
  intro K _ _ _ _ H
  let A := localSeparableValuationSubring K
  apply top_unique
  intro tau _htau
  let sigma : Gal(SeparableClosure K / K) := tau.restrictScalars K
  have hsigma : sigma • A = A := by
    change sigma ∈ decompositionGroup K A
    rw [localSeparableDecompositionGroup_eq_top K]
    exact Subgroup.mem_top sigma
  change tau • A = A
  exact hsigma

end Langlands.NYLL.LocalClassFieldTheory
