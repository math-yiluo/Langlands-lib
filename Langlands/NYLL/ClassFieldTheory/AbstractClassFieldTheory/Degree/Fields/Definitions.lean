/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions

/-!
# The NYLL degree datum and its initial fields and inertia data

Modified by Worker 120: extract the data commands M010.001–003, .006, .008,
.010, .012, .014–015 and .017–018 from the pinned NYLL Fields source.
Prefix the namespace with Langlands.NYLL. Retain the original types, bodies,
universes, field proofs and instance registration. Use the published focused
profinite-integer and cardinal-index data with Mathlib quotient groups.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

/-- The multiplicative presentation of `ℤ̂`; multiplication here is addition
in the profinite integers. -/
abbrev ZHatMul : Type 0 := Multiplicative ZHat

/-- The degree datum on a topological group: a continuous surjection
`d : G → ℤ̂`.  Profinite hypotheses belong to the ambient group and are
requested only by results that use them; they are not duplicated as proof
fields inside this datum. -/
structure DegreeData (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The continuous degree homomorphism to the profinite integers. -/
  degree : G →ₜ* ZHatMul
  /-- The degree homomorphism is surjective. -/
  degree_surjective : Function.Surjective degree

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The distinguished base field, represented contravariantly by the full
ambient group. -/
def baseField (G : Type u) [Group G] [TopologicalSpace G] : ClosedSubgroup G where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

namespace DegreeData

/-- The inertia group `I = ker d`, including its closedness. -/
def inertia (D : DegreeData G) : ClosedSubgroup G where
  toSubgroup := D.degree.toMonoidHom.ker
  isClosed' := by
    change IsClosed {g : G | (D.degree g).toAdd = 0}
    exact isClosed_eq D.degree.continuous_toFun continuous_const

/-- The restriction of `d` to the subgroup representing an abstract field. -/
def restrictedDegree (D : DegreeData G) (K : ClosedSubgroup G) :
    K.toSubgroup →ₜ* ZHatMul where
  toMonoidHom := D.degree.toMonoidHom.comp K.toSubgroup.subtype
  continuous_toFun := D.degree.continuous_toFun.comp continuous_subtype_val

/-- The image `d(G_K)` in `ℤ̂`. -/
def fieldImage (D : DegreeData G) (K : ClosedSubgroup G) : Subgroup ZHatMul :=
  (D.restrictedDegree K).toMonoidHom.range

/-- The inertia group `I_K = G_K ∩ I` over `K`. -/
def fieldInertia (D : DegreeData G) (K : ClosedSubgroup G) : ClosedSubgroup G :=
  K ⊓ D.inertia

/-- `I_K` viewed inside `G_K`; equivalently, the kernel of `d|G_K`. -/
def fieldInertiaWithin (D : DegreeData G) (K : ClosedSubgroup G) :
    Subgroup K.toSubgroup :=
  (D.restrictedDegree K).toMonoidHom.ker

/-- The degree kernel defining inertia inside a field subgroup is normal. -/
instance fieldInertiaWithin_normal (D : DegreeData G) (K : ClosedSubgroup G) :
    (D.fieldInertiaWithin K).Normal := by
  rw [fieldInertiaWithin]
  infer_instance

/-- The absolute residue degree as the cardinality of the actual quotient of
`ZHat` by the degree image. -/
noncomputable def residueDegreeCardinal (D : DegreeData G)
    (K : ClosedSubgroup G) : Cardinal :=
  relativeIndexCardinal
    (show D.fieldImage K ≤ (⊤ : Subgroup ZHatMul) from le_top)

/-- The actual quotient whose cardinality is the absolute residue degree. -/
def residueQuotient (D : DegreeData G) (K : ClosedSubgroup G) : Type :=
  (⊤ : Subgroup ZHatMul) ⧸ (D.fieldImage K).subgroupOf ⊤

end DegreeData

end
end Langlands.NYLL.ClassFormation
