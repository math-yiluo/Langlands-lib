/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M099.011 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FiniteAbstractFixedField Relative
Statements module and the published M099.010 proof module, and open only
RamificationTheory. State the theorem as the published Statement applied to
the source parameters, in which extensionSubgroup K L hLK is written as its
body L.toSubgroup.subgroupOf K.toSubgroup, and write the local hypothesis
hmap with the same body. The proof is otherwise unchanged. The original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.U010.Proofs

/-!
# Normality of the relative fixing subgroup

The proof that relative normality of the abstract subgroups transfers to
normality of the fixing subgroup of the upper fixed field over the lower one.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Relative normality in the abstract class-formation framework is the actual normality of the
subgroup fixing the upper field inside the lower field's absolute Galois group. -/
theorem abstractRelativeFixingSubgroup_normal
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    abstractRelativeFixingSubgroup_normalStatement k Ω K L hLK hnormal := by
  have hmap : ((L.toSubgroup.subgroupOf K.toSubgroup).map
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom).Normal :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap

end Langlands.NYLL.LocalClassFieldTheory
