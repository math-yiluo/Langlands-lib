/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract the statement of M244.005
(residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup, lines 93–103)
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. The section variables k and Omega and their
six instance binders (lines 89–91), which Lean adds to this theorem's
signature, become leading universal binders, followed by the theorem's
binders. Add the Langlands.NYLL namespace prefix and the suffix Statement.
Import the Library module that publishes residueAbsoluteDegreeIn instead of
the source imports. Omit the noncomputable section, the universe and open
lines, which this statement does not need, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions

/-!
# Index of the degree image of a subgroup with a finite residue image

A closed proposition: let `Omega` be an algebraic closure of a finite field
`k`, let `rho` be a group homomorphism from a group `G` to
`Omega ≃ₐ[k] Omega`, and let `E` be a finite Galois subextension of
`Omega / k`. If a subgroup `H` of `G` maps under `rho` onto the subgroup
fixing `E`, then the image of `H` under the composite of `rho` with the
residue degree map `residueAbsoluteDegreeIn k Omega` to `ZHatMul` has index
`[E : k]`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

-- Keep the source hypothesis name `himage`, which the conclusion does not mention.
set_option linter.unusedVariables false in
/-- States the theorem
`residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup`. -/
def residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroupStatement :
    Prop :=
  ∀ (k Omega : Type)
    [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
    [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]
    {G : Type*} [Group G]
    (rho : G →* (Omega ≃ₐ[k] Omega))
    (H : Subgroup G)
    (E : FiniteGaloisIntermediateField k Omega)
    (himage : H.map rho = E.toIntermediateField.fixingSubgroup),
    (H.map ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
      Module.finrank k E

end Langlands.NYLL.LocalClassFieldTheory
