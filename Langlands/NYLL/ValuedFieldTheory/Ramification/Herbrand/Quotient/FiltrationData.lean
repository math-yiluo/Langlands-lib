/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Subgroup, quotient-image and transported filtration data

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Quotient.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 39–45, 63–71,
157–163 and 231–234 (M314.001, .004, .010 and .017).
Worker 540 extracted these four definitions, prefixed the namespace by
`Langlands.NYLL`, imported the published filtration bundle, reduced the Mathlib
imports to subgroup basics and quotient definitions, and omitted the unused
`noncomputable section`.
The definition binders, constructor fields and proof bodies are unchanged.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u v

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G]

/-- The filtration induced on a subgroup by intersection with every ambient
lower group. -/
def subgroupFiltration (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) :
    AntitoneNormalSubgroupFiltration H where
  lower n := (F.lower n).comap H.subtype
  lower_normal n := (F.lower_normal n).comap H.subtype
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- The pointwise image filtration on a quotient by a normal subgroup.  This
is not asserted to be the actual lower filtration of a valued quotient; that
identification is precisely the content supplied by Herbrand's theorem. -/
def quotientImageFiltration (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] :
    AntitoneNormalSubgroupFiltration (G ⧸ H) where
  lower n := (F.lower n).map (QuotientGroup.mk' H)
  lower_normal n := (F.lower_normal n).map
    (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  antitone := by
    intro m n hmn
    exact Subgroup.map_mono (F.antitone hmn)

variable {G' : Type v} [Group G']

/-- Transport a lower ramification filtration across a group equivalence. -/
def transportEquiv (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') :
    AntitoneNormalSubgroupFiltration G' where
  lower n := (F.lower n).comap e.symm.toMonoidHom
  lower_normal n := (F.lower_normal n).comap e.symm.toMonoidHom
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- The quotient-image filtration, transported to any isomorphic model of
the quotient group. -/
def quotientImageTransport
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') : AntitoneNormalSubgroupFiltration G' :=
  transportEquiv (quotientImageFiltration F H) e

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
