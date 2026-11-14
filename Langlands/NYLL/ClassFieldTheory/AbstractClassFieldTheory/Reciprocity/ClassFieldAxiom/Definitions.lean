/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.CyclicSubextension.Definitions

/-!
# Abstract reciprocity: the class field axiom

Adapted by Worker 90 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean`,
lines 19–62 (M072.001–M072.002).

Modifications by Worker 90: extract the two data/predicate declarations;
prefix the namespace `ClassFormation` with `Langlands.NYLL`; replace the
source import by the published modules providing `IntegralRepGroupType`,
`FiniteAbstractField`, `FiniteCyclicSubextension` with its instances and
`fixedRepresentation`, and `DegreeData.FiniteAbstractExtension.degree`.
The universe boundary, binders, fields, docstrings and bodies are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The coefficient group for a finite cyclic extension `L / K` is the actual
fixed module `A_L`, descended to the actual quotient `G_K / G_L`.  Thus the
two numbers below are the orders of the Tate groups occurring in the
original statement the class-field axiom, rather than cardinality data attached to an
auxiliary reciprocity map.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

open CategoryTheory

/-! `Representation.Rep` places its coefficient ring and acting group in the
same universe.  The shared `IntegralRepGroupType` boundary records the
universe forced by the coefficient ring `ℤ` without scattering raw
universe-zero declarations through the reciprocity API. -/

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The finite cohomology data asserted at one finite cyclic extension.
Finiteness is stored before either natural-valued cardinality is formed. -/
structure ClassFieldAxiomCohomologyData (A : Rep ℤ G)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop where
  /-- The degree-zero Tate cohomology group is finite. -/
  finiteTateHZero : Finite (tateCohomology (E.fixedRepresentation A) 0)
  /-- The degree-minus-one Tate cohomology group is finite. -/
  finiteTateHMinusOne :
    Finite (tateCohomology (E.fixedRepresentation A) (-1))
  /-- Degree-zero Tate cohomology has cardinality equal to the extension degree. -/
  tateHZero_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- Degree-minus-one Tate cohomology is trivial by cardinality. -/
  tateHMinusOne_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1

/-- **The class-field axiom.**  For every finite cyclic extension `L / K`
with `K` finite over the distinguished base field,
`#H⁰(G(L/K), A_L) = [L : K]` and `#H⁻¹(G(L/K), A_L) = 1`.

Both the base field and the cyclic extension are bundled, so containment,
finiteness, normality, and the chosen generator cannot become detached from
the subgroups to which they belong. -/
def SatisfiesClassFieldAxiom (A : Rep ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomCohomologyData A K E

end
end Langlands.NYLL.ClassFormation
