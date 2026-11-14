/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion

/-!
# NYLL M040: a finite Galois subextension as a finite abstract field extension

Modified by Worker 171: extract M040.023 from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
prefix the namespace with `Langlands.NYLL`, and replace the source module import
by the focused published imports this declaration uses. Universes, binders,
the docstring and the body are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Retain the finite-over-base endpoint bundles of a finite Galois
subextension of an abstract field which is finite over the distinguished
base. -/
noncomputable def toFiniteAbstractFieldExtension
    {K : FiniteAbstractField G} (L : FiniteGaloisSubextension K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  exact FiniteAbstractFieldExtension.ofInclusion L.field K L.below

end FiniteGaloisSubextension

end GroupOnly

end
end Langlands.NYLL.ClassFormation
