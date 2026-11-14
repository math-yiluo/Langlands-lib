/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions
import Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions

/-!
# Conjugate closed subgroups, normal-extension action and finite-tower data

Modified by Worker 165, 14 November 2026: extract M026.001, .005, .011, .015
and .016 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, name the private source definition
`Langlands.NYLL.PortInternal.M026.d005`, replace the source module imports by
focused Mathlib and published NYLL imports, and inline in M026.015 the
one-term source proof of the theorem `relativeTowerQuotientFinite` (M026.014),
whose proof is separate work. All other constructions and embedded proof terms
are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The subgroup corresponding to the conjugate abstract field `K^σ`.

The construction uses a right exponent, hence `G_{K^σ} = σ⁻¹ G_K σ`. -/
def conjugateClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) : ClosedSubgroup G where
  toSubgroup := ConjAct.toConjAct σ⁻¹ • K.toSubgroup
  isClosed' := by
    convert IsClosed.preimage
      (IsTopologicalGroup.continuous_conj (G := G) σ) K.isClosed' using 1
    ext x
    change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
      σ * x * σ⁻¹ ∈ K.toSubgroup
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/-- Conjugation by `σ` as a permutation of the absolute subgroup
`(baseField G).toSubgroup`.  This is the private source definition
`ClassFormation.absoluteConjugationEquiv`. -/
def _root_.Langlands.NYLL.PortInternal.M026.d005 {G : Type*} [Group G]
    [TopologicalSpace G]
    (σ : G) :
    (baseField G).toSubgroup ≃
      (baseField G).toSubgroup where
  toFun x := ⟨σ * x.1 * σ⁻¹, trivial⟩
  invFun x := ⟨σ⁻¹ * x.1 * σ, trivial⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The action of an element of `G_K` on `A_L`, when `L | K` is Galois.

Normality is used only to prove that the translate is still fixed by `G_L`. -/
def normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  refine ⟨A.ρ k.1 a.1, ?_⟩
  intro l
  let lK : K.toSubgroup := Subgroup.inclusion hLK l
  have hc : k⁻¹ * lK * k ∈ extensionSubgroup K L hLK :=
    by simpa using hnormal.conj_mem lK l.2 k⁻¹
  let l' : L.toSubgroup := ⟨(k⁻¹ * lK * k).1, hc⟩
  have hl'val : (l' : G) = (k⁻¹ * lK * k : K.toSubgroup) :=
    rfl
  calc
    A.ρ l.1 (A.ρ k.1 a.1) = A.ρ (l.1 * k.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ (k.1 * l'.1) a.1 := by rw [hl'val]; simp [lK, mul_assoc]
    _ = A.ρ k.1 (A.ρ l'.1 a.1) := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by rw [a.2 l']

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- The finite composite extension represented by a finite tower. -/
noncomputable def totalExtension : DegreeData.FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.totalExtension
  finiteQuotient :=
    Finite.of_equiv
      ((T.base.toSubgroup ⧸ extensionSubgroup T.base T.middle T.middle_le_base) ×
        (T.middle.toSubgroup ⧸ extensionSubgroup T.middle T.top T.top_le_middle))
      (Subgroup.quotientTowerEquiv T.top_le_middle T.middle_le_base).symm

/-- The quotient from the top to the base of a finite tower is finite. -/
instance totalQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      extensionSubgroup T.base T.top
        (T.top_le_middle.trans T.middle_le_base)) :=
  T.totalExtension.finiteQuotient

end DegreeData.FiniteTower

end
end Langlands.NYLL.ClassFormation
