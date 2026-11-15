/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 127, 15 November 2026:
Extract the proof of M250.006 (lines 99-122) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the U006 Statements module instead of the source
imports, and prove the published closed proposition by introducing its
eight binders (the section variable K, its four instance binders and the
theorem's binders H, sigma and x) and then following the source proof
(lines 112-122) unchanged. The source names
localSeparableDecompositionGroup_eq_top and
localAbstractFixedDecompositionGroup_eq_top now denote the published closed
M249.010 and M250.005 theorems, applied as in the source. Omit the source
open lines, which this proof does not need, the source noncomputable
section and all other source declarations. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U006.Statements

/-!
# The local residue action restricted to a closed subgroup: proof

For an element `sigma` of a closed subgroup `H` of the absolute Galois group
of a local field `K`, the local residue action of `sigma` and the residue
action over the fixed field of `H` of the corresponding automorphism agree
on the selected residue field: both send the residue class of `a` to the
residue class of `sigma a`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Restricting the local residue action to `H` gives the same underlying
automorphism of the selected residue field as applying the residue-action map
over the fixed field of `H`. -/
theorem localAbstractFixedResidueAction_apply :
    localAbstractFixedResidueAction_applyStatement := by
  intro K _ _ _ _ H sigma x
  let A := localSeparableValuationSubring K
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop K A
        (localSeparableDecompositionGroup_eq_top K) sigma.1) • a) =
    IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        (abstractFixedField K (SeparableClosure K) H) A
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma)) • a)
  congr 1

end Langlands.NYLL.LocalClassFieldTheory
