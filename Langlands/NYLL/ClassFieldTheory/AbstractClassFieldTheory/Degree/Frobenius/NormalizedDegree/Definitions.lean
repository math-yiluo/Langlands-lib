/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.FieldImageIndex.U003.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions

/-!
# The normalized degree map

Modified by Worker 5264: extract M011.004 `restrictedDegreeInMulNatRange` and
M011.006 `normalizedDegree` from the pinned NYLL Frobenius source with the
Langlands.NYLL namespace prefix. The source variable declaration, docstrings,
signatures and construction bodies are retained. The source import of the whole
Fields module is replaced by the published proof of M011.003
`fieldImageAdd_eq_mulNat_range`, which the body of M011.004 uses, and the
published division map M009.016 `zHatDivide`, which the body of M011.006 uses.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The raw value `d(k)` regarded as an element of the subgroup `f_K ℤ̂`. -/
def restrictedDegreeInMulNatRange (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range := by
  refine ⟨(D.degree k.1).toAdd, ?_⟩
  rw [← D.fieldImageAdd_eq_mulNat_range K]
  change D.degree k.1 ∈ D.fieldImage K.field
  exact ⟨k, rfl⟩

/-- The normalized degree map `d_K = (1 / f_K)d`. -/
def normalizedDegree (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup →ₜ* ZHatMul where
  toFun k := Multiplicative.ofAdd
    (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K k))
  map_one' := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K 1) = 0
    rw [show D.restrictedDegreeInMulNatRange K 1 = 0 by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_one D.degree)]
    exact map_zero (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)
  map_mul' x y := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
        (D.restrictedDegreeInMulNatRange K (x * y)) =
      zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K x) +
        zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K y)
    rw [show D.restrictedDegreeInMulNatRange K (x * y) =
        D.restrictedDegreeInMulNatRange K x +
          D.restrictedDegreeInMulNatRange K y by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul D.degree x.1 y.1)]
    exact map_add (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property) _ _
  continuous_toFun := by
    apply (map_continuous
      (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)).comp
    exact Continuous.subtype_mk
      (D.restrictedDegree K.field).continuous_toFun
      (fun k => (D.restrictedDegreeInMulNatRange K k).2)

end DegreeData

end
end Langlands.NYLL.ClassFormation
