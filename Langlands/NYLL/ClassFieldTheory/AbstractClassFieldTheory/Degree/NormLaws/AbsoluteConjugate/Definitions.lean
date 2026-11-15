/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U006.Proofs

/-!
# Conjugation of absolute coset spaces

Modified by Worker 5264, 15 November 2026: port the source definition
M026.007 `absoluteConjugateCosetEquiv` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports
(the proved M026.002 `conjugateClosedSubgroup_mem` and M026.006, the private
source theorem `mem_absoluteExtension` published as
`Langlands.NYLL.PortInternal.M026.d006`), and refer to the private source
definition `absoluteConjugationEquiv` (M026.005) by its published name
`Langlands.NYLL.PortInternal.M026.d005`. In the embedded proof, the source
rewrites with `mem_absoluteExtension` and `conjugateClosedSubgroup_mem` are
made with local hypotheses `hext` and `hmem` holding exactly those two
equivalences, because the published theorems have Prop-valued Statement
types, which `rw` cannot use directly. The source opens, variable
declaration, docstring, binders and the construction are otherwise
unchanged; the rest of the source file is omitted. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Conjugation identifies the absolute coset spaces for `K^σ` and `K`. -/
noncomputable def absoluteConjugateCosetEquiv
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) :
    ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) ≃
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K)) :=
  Quotient.congr (Langlands.NYLL.PortInternal.M026.d005 σ) (by
    intro x y
    have hext : ∀ (H : ClosedSubgroup G) (z : (baseField G).toSubgroup),
        z ∈ extensionSubgroup (baseField G) H (le_baseField H) ↔ z.1 ∈ H :=
      fun H z => Langlands.NYLL.PortInternal.M026.d006 H z
    have hmem : ∀ z : G, z ∈ conjugateClosedSubgroup K σ ↔ σ * z * σ⁻¹ ∈ K :=
      fun z => conjugateClosedSubgroup_mem K σ z
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
      hext, hext,
      hmem]
    change σ * (x.1⁻¹ * y.1) * σ⁻¹ ∈ K.toSubgroup ↔
      (σ * x.1 * σ⁻¹)⁻¹ * (σ * y.1 * σ⁻¹) ∈ K.toSubgroup
    simp [mul_assoc])

end

end Langlands.NYLL.ClassFormation
