/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum.Initial.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.Index

/-!
# Targets for the finite indices of the residue datum

For every finite Galois residue subextension, the image of its fixing subgroup
under the residue datum is `n ℤ̂`; consequently the abstract residue degree is
the ordinary field degree.

Adapted from NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 67–71 (M238.003) and
112–115 (M238.004), with the section variables of lines 31–33. Worker 59 stated
the two theorem signatures as Prop-valued `Statement` definitions, with every
source section variable written as an explicit binder of each definition so that
none is dropped, prefixed the namespaces by `Langlands.NYLL`, and replaced the
NYLL imports by the Library and Mathlib modules that publish the reused
declarations. The source obtains `IsGalois k Omega` for `closedFixingSubgroup`
from the private instance `residueAlgebraicClosureIsGalois` of
`ResidueAlgebraicClosureDegree.lean` (M236.003); here each target supplies it
locally, after the local `IsAlgClosure k Omega` of M236.002, and no global
instance is added. The private lemma M238.002 is not stated; it will be proved
inside the M238.003 proof. See the paired Markdown and `licenses/NYLL/LICENSE`
and `NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open Langlands.NYLL.RamificationTheory

open Langlands.NYLL.ClassFormation

noncomputable section

/-- Target: the degree image of the subgroup fixing a finite residue extension of
degree `n` is exactly `n ℤ̂`. -/
def residueDatumIn_fieldImage_closedFixingSubgroupStatement
    (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  (residueDatumIn k Omega).fieldImage
      (closedFixingSubgroup k Omega E) =
    (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup

/-- Target for the internal finite-coordinate calculation: the degree image of the
fixing subgroup has natural index equal to the ordinary residue-field degree. Public
residue-degree APIs use `Cardinal` or a finite residue-field bundle. -/
def Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement
    (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois k Omega := {}
  ((residueDatumIn k Omega).fieldImage
      (closedFixingSubgroup k Omega E)).index = Module.finrank k E

end
end Langlands.NYLL.LocalClassFieldTheory
