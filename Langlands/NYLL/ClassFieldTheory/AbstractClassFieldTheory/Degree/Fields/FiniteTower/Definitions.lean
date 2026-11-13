/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions

/-!
# NYLL M010: finite tower data

Modified by Worker 198: extract the source units listed in the paired Markdown,
prefix their namespace with Langlands.NYLL, and use focused published imports.
The Markdown records all statement conversions and construction substitutions.
See licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A finite composable tower of abstract extensions.  The two adjacent
finite quotient proofs belong to the tower object, so downstream norm and
degree laws do not thread subgroup containments and finiteness instances as
independent arguments. -/
structure FiniteTower (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension.Tower G where
  /-- The quotient for the top-to-middle extension is finite. -/
  finiteTopQuotient : Finite toTower.topExtension.quotient
  /-- The quotient for the middle-to-base extension is finite. -/
  finiteBaseQuotient : Finite toTower.baseExtension.quotient

namespace FiniteTower

variable (T : FiniteTower G)

/-- The upper relative quotient in a finite tower is finite. -/
instance topQuotientFinite :
    Finite (T.middle.toSubgroup ⧸
      (T.top.toSubgroup.subgroupOf T.middle.toSubgroup)) :=
  T.finiteTopQuotient

/-- The lower relative quotient in a finite tower is finite. -/
instance baseQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      (T.middle.toSubgroup.subgroupOf T.base.toSubgroup)) :=
  T.finiteBaseQuotient

end FiniteTower

end DegreeData

end
end Langlands.NYLL.ClassFormation
