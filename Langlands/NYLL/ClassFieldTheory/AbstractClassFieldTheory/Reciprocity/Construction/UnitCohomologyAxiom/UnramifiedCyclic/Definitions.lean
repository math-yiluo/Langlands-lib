/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.CyclicSubextension.Definitions

/-!
# NYLL M032: finite unramified cyclic extensions

Modified by Worker 5424: extract M032.009, M032.012, M032.013 and M032.015 from
the pinned NYLL UnitCohomologyAxiom.lean, prefix the namespace with
Langlands.NYLL, give the anonymous instances their PortInternal names and use
the focused import of the M032 cyclic-subextension module. The source units
M032.010, M032.011 and M032.014 are not part of this module (see the paired
Markdown). The declarations, binders and bodies are otherwise unchanged. See
the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A finite cyclic extension together with the assertion that it is
unramified for the fixed degree datum. -/
structure FiniteUnramifiedCyclicExtension
    (D : DegreeData G) (K : FiniteAbstractField G)
    extends FiniteCyclicSubextension K where
  /-- The underlying finite cyclic extension is unramified for `D`. -/
  unramified : toFiniteCyclicSubextension.IsUnramified D

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- A finite unramified cyclic extension supplies normality of its representing subgroup. -/
instance _root_.Langlands.NYLL.PortInternal.M032.d012
    (E : FiniteUnramifiedCyclicExtension D K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- The quotient over `K` attached to a finite unramified cyclic extension is finite. -/
instance _root_.Langlands.NYLL.PortInternal.M032.d013
    (E : FiniteUnramifiedCyclicExtension D K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The finite quotient over `K` carries the canonical `Fintype` structure. -/
noncomputable instance _root_.Langlands.NYLL.PortInternal.M032.d015
    (E : FiniteUnramifiedCyclicExtension D K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteUnramifiedCyclicExtension

end
end Langlands.NYLL.ClassFormation
