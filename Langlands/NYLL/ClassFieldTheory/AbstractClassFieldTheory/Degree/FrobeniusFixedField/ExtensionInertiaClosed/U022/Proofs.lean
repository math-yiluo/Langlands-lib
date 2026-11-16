/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.ExtensionInertiaClosed.Statements

/-!
# NYLL M014.022: the relative inertia subgroup is closed

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.extensionInertiaWithin_isClosedStatement` (M014.022) by the
source proof of `DegreeData.extensionInertiaWithin_isClosed` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, write the source's
`extensionSubgroup K.field L hLK` as its Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup` (the form used by the published
`extensionInertiaWithin`), replace the source imports by the published
statement module and omit `open CyclicCohomology` and the rest of the source
file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The extension's inertia subgroup is closed inside its base subgroup. -/
theorem extensionInertiaWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    extensionInertiaWithin_isClosedStatement D K L hLK := by
  show IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup)
  have hE : IsClosed
      (L.toSubgroup.subgroupOf K.field.toSubgroup : Set K.field.toSubgroup) := by
    change IsClosed ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G))
    exact L.isClosed'.preimage continuous_subtype_val
  have hI : IsClosed (D.fieldInertiaWithin K.field : Set K.field.toSubgroup) := by
    let : T2Space ZHatMul := by
      change T2Space ZHat
      infer_instance
    change IsClosed {x : K.field.toSubgroup | D.degree x.1 = 1}
    exact isClosed_eq
      (D.restrictedDegree K.field).continuous_toFun continuous_const
  change IsClosed
    ((L.toSubgroup.subgroupOf K.field.toSubgroup ⊓ D.fieldInertiaWithin K.field) :
      Set K.field.toSubgroup)
  exact hE.inter hI

end DegreeData

end

end Langlands.NYLL.ClassFormation
