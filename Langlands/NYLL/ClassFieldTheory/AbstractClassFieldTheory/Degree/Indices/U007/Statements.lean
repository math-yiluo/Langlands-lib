/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Index

/-!
# Targets for saturation and natural relative indices

Modified by Worker 190, 13 November 2026: extract the signatures of M006.007–009
from NYLL Degree/Indices.lean at commit
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with Langlands.NYLL,
append Statement to the theorem names, and replace the proofs by Prop-valued
definition bodies. Preserve all source universes, parameters, binder kinds and
hypotheses. Replace the original import with Mathlib.GroupTheory.Index and omit
the unused Pointwise scope. See the paired Markdown and licenses/NYLL/.
-/

namespace Langlands.NYLL.ClassFormation

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/-- Target identifying the saturated inner index with the kernel-intersection index. -/
def relIndex_saturation_eq_inf_ker_relIndexStatement (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) : Prop :=
  L.relIndex (K ⊓ (L ⊔ d.ker)) =
    (L ⊓ d.ker).relIndex (K ⊓ d.ker)

/-- Target identifying the mapped relative index with the saturated outer index. -/
def map_relIndex_eq_saturation_relIndexStatement (d : G →* D)
    (L K : Subgroup G) : Prop :=
  (L.map d).relIndex (K.map d) =
    (K ⊓ (L ⊔ d.ker)).relIndex K

/-- Target for the natural-valued image–kernel identity of a subgroup inclusion. -/
def relIndex_eq_map_relIndex_mul_inf_ker_relIndexStatement (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) : Prop :=
  L.relIndex K =
    (L.map d).relIndex (K.map d) * (L ⊓ d.ker).relIndex (K ⊓ d.ker)

end Langlands.NYLL.ClassFormation
