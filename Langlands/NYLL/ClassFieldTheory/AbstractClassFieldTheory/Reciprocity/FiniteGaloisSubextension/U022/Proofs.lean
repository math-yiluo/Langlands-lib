/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.U076.Proofs

/-!
# NYLL M040.022: total ramification of a finite Galois extension by degree images

Modified by Worker 744, 16 November 2026 UTC: extract only the proof of
M040.022 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(lines 204–210) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with `Langlands.NYLL`, import the published statement module and
the published M010.076 proof module, and give the theorem the published
Statement applied to the source parameters as its type. The source proof term
`L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D` is retained.
The source `noncomputable section`, `open KummerTheory`,
`open CyclicCohomology`, the `GroupOnly` section and all other source
declarations are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    isTotallyRamified_iff_image_leStatement L D :=
  L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
