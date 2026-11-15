/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract the statement of M250.006 (localAbstractFixedResidueAction_apply,
lines 102–111) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FiniteSubgroupResidueDegree.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. The section variable K and its instance
binders (lines 33–34) become leading universal binders, followed by the
theorem's binders H, sigma and x. Add the Langlands.NYLL namespace prefix and
the suffix Statement. The source term
localAbstractFixedDecompositionGroup_eq_top K H now denotes the published
proof of the M250.005 target. Import the Library modules that publish the
names used instead of the source imports. Omit the noncomputable section, the
open lines and local instances this statement does not need, and all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions

/-!
# The local residue action restricted to a closed subgroup

A closed proposition: for a nonarchimedean local field `K`, a closed
subgroup `H` of `Gal(SeparableClosure K / K)`, an element `sigma` of `H` and
a point `x` of the selected residue field, the local residue action of
`sigma` on `x` equals the residue action over the fixed field of `H` of the
automorphism corresponding to `sigma`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- States the theorem `localAbstractFixedResidueAction_apply`: restricting
the local residue action to `H` gives the same underlying automorphism of the
selected residue field as applying the residue-action map over the fixed
field of `H`. -/
def localAbstractFixedResidueAction_applyStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localSeparableValuationSubring K)),
    localSeparableResidueAlgAction K sigma.1 x =
      residueAlgActionOfEqTop
        (abstractFixedField K (SeparableClosure K) H)
        (localSeparableValuationSubring K)
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma) x

end Langlands.NYLL.LocalClassFieldTheory
