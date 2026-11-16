/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Unramified.Statements

/-!
# NYLL M040.021: the inertia criterion for unramified finite Galois extensions

Modified by Worker 5264, 15 November 2026: prove the published target
`FiniteGaloisSubextension.isUnramified_iff_inertia_leStatement` (M040.021)
for the source theorem `FiniteGaloisSubextension.isUnramified_iff_inertia_le`
in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and replace the source
term `L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D`, whose
proof M010.075 is not in the Library, by `Iff.rfl`, the source proof of
M010.046 to which M010.075 reduces. Replace the source import by the
published statement module and omit the opens of `KummerTheory` and
`CyclicCohomology` and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement L D := by
  show L.IsUnramified D ↔
    K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
  exact Iff.rfl

end FiniteGaloisSubextension

end GroupOnly

end

end Langlands.NYLL.ClassFormation
