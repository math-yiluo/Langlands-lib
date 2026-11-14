/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions

/-!
# The norm to the base field and the valuation data

Modified by Worker 110, 14 November 2026: extract M025.001, M025.012–016
and M025.019 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source's module imports by the published
relative-norm, value-group-reduction and finite-abstract-field modules.
Universes, binders, structure fields, bodies and proof terms are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology



noncomputable section

universe u

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm `N_{K|k}` on the actual fixed modules. -/
def normToBase (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))] :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (baseField G) :=
  relativeNorm A (baseField G) K (le_baseField K)

/-- **the valuation-quotient axiom.** A henselian valuation of `A_k` with respect to `d`.

`integers_mem` and `canonical_value_quotient_bijective` are precisely
condition (i), while `norm_range` is condition (ii). -/
structure ValuationData (D : DegreeData G) (A : Rep ℤ G) where
  /-- The additive valuation on the distinguished base-field fixed module. -/
  toAddMonoidHom : ambientFixedAddSubgroup A (baseField G) →+ ZHat
  /-- Every integral value occurs in the image of the valuation. -/
  integers_mem : ∀ m : ℤ,
    (Int.castRingHom ZHat) m ∈
      toAddMonoidHom.range
  /-- Reduction of the value group modulo every positive integer is bijective. -/
  canonical_value_quotient_bijective : ∀ (n : ℕ) (hn : 0 < n),
    Function.Bijective
      (canonicalValueQuotientMap toAddMonoidHom.range n hn)
  /-- Norms from a finite abstract field have the prescribed value-group image. -/
  norm_range : ∀ K : FiniteAbstractField G,
    (toAddMonoidHom.comp (normToBase A K.field)).range =
      nsmulImage toAddMonoidHom.range (K.residueDegree D : ℕ)

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The value group `Z = v(A_k)`. -/
def valueGroup (v : ValuationData D A) : AddSubgroup ZHat :=
  v.toAddMonoidHom.range

/-- The valuation-quotient axiom's canonical map for a henselian valuation. -/
def canonicalQuotientMap (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  canonicalValueQuotientMap v.valueGroup n hn

/-- The former equivalence API, now derived from the bijectivity of the
canonical inclusion-and-reduction map in the valuation-quotient axiom. -/
def cyclic_value_quotients (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  AddEquiv.ofBijective (v.canonicalQuotientMap n hn)
    (v.canonical_value_quotient_bijective n hn)

/-- Canonical reduction of the value group modulo `n`. -/
def valueModulo (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.valueGroup →+ ZMod n :=
  (v.cyclic_value_quotients n hn).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n))

/-- The norm composite `v ∘ N_{K|k}` before division by the residue degree. -/
def normCompositeAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  v.toAddMonoidHom.comp (normToBase A K.field)

end ValuationData

end

end Langlands.NYLL.ClassFormation
