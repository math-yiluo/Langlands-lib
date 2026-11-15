/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 15 November 2026 UTC:
Extract only the proof of M020.009 (cyclicFactorSubgroup_isClosed) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean
(lines 131–162) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix and import only the published
KummerAbelianCyclicFactors Statements module. Keep the section name, the two
section variable lines, the noncomputable section, the docstring, the binders
and the tactic proof, and state the theorem as the published Statement
applied to the source parameters. The source proof's call of
extensionSubgroup_isClosed (M020.008, not yet in the Library) is replaced by
a private local copy, extensionSubgroup_isClosed_local, with the source proof
of M020.008 and the source's conclusion as its type, stated over the section
variable G. Open Langlands.NYLL.CyclicCohomology for extensionSubgroup. Omit
the other declarations of the source file. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements

/-!
# Closedness of pulled-back cyclic factor kernels

If `L ≤ K` are closed subgroups of a topological group `G` such that `G_L` is
normal of finite index in `G_K`, then the finite quotient `G_K / G_L` is
discrete, so the preimage in `G_K` of the kernel of any homomorphism
`G_K / G_L →* C` is closed.
-/

namespace Langlands.NYLL.KummerTheory

open Langlands.NYLL.CyclicCohomology

noncomputable section

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Private local copy of M020.008 `extensionSubgroup_isClosed`, with its
source proof: `G_L` is closed in `G_K`. -/
private theorem extensionSubgroup_isClosed_local
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup) := by
  change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))
  exact L.isClosed'.preimage continuous_subtype_val

variable [IsTopologicalGroup G]

/-- A pulled-back cyclic factor kernel is closed inside `G_K`: the finite
quotient by `G_L` is discrete, and the factor kernel is pulled back along the
continuous quotient map. -/
theorem cyclicFactorSubgroup_isClosed
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    cyclicFactorSubgroup_isClosedStatement K L hLK f := by
  let H := extensionSubgroup (G := G) K L hLK
  let : IsClosed (H : Set K.toSubgroup) := extensionSubgroup_isClosed_local K L hLK
  change IsClosed
    ((QuotientGroup.mk' H) ⁻¹' (MonoidHom.ker f : Set (K.toSubgroup ⧸ H)))
  exact (isClosed_discrete _).preimage QuotientGroup.continuous_mk

end ClosedCyclicSubextensions

end

end Langlands.NYLL.KummerTheory
