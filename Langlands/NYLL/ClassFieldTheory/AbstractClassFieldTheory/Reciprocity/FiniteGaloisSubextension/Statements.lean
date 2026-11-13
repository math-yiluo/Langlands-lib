/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions

/-!
# NYLL M040: finite Galois subextension targets

Modified by Worker 4918: state the source theorems listed in the paired
Markdown from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
as Prop-valued definitions ending in `Statement`, with the source binders and
statements, under the namespace prefix `Langlands.NYLL`. Proofs and `simp`
attributes are omitted. The paired Markdown records every modification. See
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

/-- Target M040.012: the named finite Galois quotient projection agrees with
`QuotientGroup.mk`. -/
def extensionQuotientMk_applyStatement (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) : Prop :=
  L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
    (QuotientGroup.mk k :
      K.toSubgroup ⧸ extensionSubgroup K L.field L.below)

/-- Target M040.013: a quotient representative is trivial exactly when it lies
in the extension subgroup. -/
def extensionQuotientMk_eq_one_iffStatement (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) : Prop :=
  L.extensionQuotientMk k = 1 ↔
    k ∈ extensionSubgroup K L.field L.below

/-- Target M040.014: the canonical projection onto the finite Galois quotient
is surjective. -/
def extensionQuotientMk_surjectiveStatement (L : FiniteGaloisSubextension K) :
    Prop :=
  Function.Surjective L.extensionQuotientMk

/-- Target M040.018: bundling a finite Galois extension preserves its
total-ramification predicate. -/
def toGaloisSubextension_isTotallyRamified_iffStatement
    (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toGaloisSubextension.IsTotallyRamified D ↔ L.IsTotallyRamified D

set_option linter.unusedVariables false in
/-- Target M040.020: transport a total-ramification proof through the
finite-to-Galois forgetful map. -/
def isTotallyRamified_toGaloisSubextensionStatement
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsTotallyRamified D) : Prop :=
  L.toGaloisSubextension.IsTotallyRamified D

/-- Target M040.022: total ramification is the canonical equality of degree
images. -/
def isTotallyRamified_iff_image_leStatement (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.IsTotallyRamified D ↔
    K.toSubgroup.map D.degree.toMonoidHom ≤
      L.field.toSubgroup.map D.degree.toMonoidHom

set_option linter.unusedVariables false in
/-- Target M040.024: finiteness is transitive in a tower of abstract fields. -/
def finite_extension_transStatement
    {P L K : ClosedSubgroup G}
    (hPL : P.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hPLfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L P hPL)]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Prop :=
  Finite (K.toSubgroup ⧸ extensionSubgroup K P (hPL.trans hLK))

set_option linter.unusedVariables false in
/-- Target M040.025: a finite extension remains finite over every intermediate
field. -/
def finite_extension_over_intermediateStatement
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P hPK)] : Prop :=
  Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM)

/-- Target M040.030: the constructed Galois compositum satisfies the left
comparison bound. -/
def compositum_le_leftStatement (L₁ L₂ : FiniteGaloisSubextension K) : Prop :=
  (L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup

/-- Target M040.031: the constructed Galois compositum satisfies the right
comparison bound. -/
def compositum_le_rightStatement (L₁ L₂ : FiniteGaloisSubextension K) : Prop :=
  (L₁.compositum L₂).field.toSubgroup ≤ L₂.field.toSubgroup

end FiniteGaloisSubextension

end GroupOnly

end
end Langlands.NYLL.ClassFormation
