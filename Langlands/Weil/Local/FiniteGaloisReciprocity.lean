import Langlands.Weil.Local.FiniteGaloisQuotient
import Langlands.LocalFactor.RankOne
import Langlands.GroupTheory.ExtensionPushout
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Reciprocity on the kernel of a finite Galois Weil quotient -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne

private def continuousNormalConj {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) : N ≃ₜ* N where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun n : N => g * (n : G) * g⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun n : N => ((MulAut.conjNormal g).symm n : G))
    simp only [MulAut.conjNormal_symm_apply]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)
  (hGal : letI := extensionAlgebra F E f; IsGalois F.Carrier E.Carrier)

/-- Inverse geometric reciprocity on the actual quotient kernel. -/
def finiteGaloisKernelReciprocity (e : ReciprocityCandidate E) :
    letI := extensionAlgebra F E f
    letI := E.canonicalTopologicalData.topology
    (finiteGaloisQuotient F E f hGal).toMonoidHom.ker →ₜ* E.Carrierˣ := by
  letI := extensionAlgebra F E f
  letI := E.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.valuativeRel
  letI := E.canonicalTopologicalData.localField
  exact (ContinuousMonoidHom.inv E.Carrierˣ).comp
    ((reciprocityUnits E e).comp (finiteGaloisQuotientKernelEquiv F E f hGal).symm)

@[simp] theorem finiteGaloisKernelReciprocity_apply
    (e : ReciprocityCandidate E) (y : localWeilGroup E) :
    letI := extensionAlgebra F E f
    finiteGaloisKernelReciprocity F E f hGal e
        (finiteGaloisQuotientKernelEquiv F E f hGal y) =
      (reciprocityUnits E e y)⁻¹ := by
  let := extensionAlgebra F E f
  change (reciprocityUnits E e
    ((finiteGaloisQuotientKernelEquiv F E f hGal).symm
      (finiteGaloisQuotientKernelEquiv F E f hGal y)))⁻¹ = _
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem finiteGaloisKernelReciprocity_surjective (e : ReciprocityCandidate E) :
    letI := extensionAlgebra F E f
    Function.Surjective (finiteGaloisKernelReciprocity F E f hGal e) := by
  let := extensionAlgebra F E f
  let := E.canonicalTopologicalData.topology
  intro a
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    ((commutator (localWeilGroup E)).topologicalClosure) (e.symm a⁻¹)
  refine ⟨finiteGaloisQuotientKernelEquiv F E f hGal y, ?_⟩
  rw [finiteGaloisKernelReciprocity_apply]
  change (e (WeilQuotients.projection (localResidueDegree E) y))⁻¹ = a
  change (e (QuotientGroup.mk y))⁻¹ = a
  change QuotientGroup.mk y = e.symm a⁻¹ at hy
  rw [hy, ContinuousMulEquiv.apply_symm_apply, inv_inv]

/-- Conjugation by an element of `W_F`, transported to the actual `W_E`. -/
def finiteGaloisWeilConjugation (g : localWeilGroup F) :
    localWeilGroup E ≃ₜ* localWeilGroup E := by
  letI := extensionAlgebra F E f
  let q := (finiteGaloisQuotient F E f hGal).toMonoidHom
  let c := continuousNormalConj q.ker g
  let j := finiteGaloisQuotientKernelEquiv F E f hGal
  exact (j.trans c).trans j.symm

/-- The conjugation on `W_E` agrees with ordinary conjugation in `W_F`. -/
theorem extensionWeilMap_finiteGaloisWeilConjugation
    (g : localWeilGroup F) (y : localWeilGroup E) :
    extensionWeilMap F E f (finiteGaloisWeilConjugation F E f hGal g y) =
      g * extensionWeilMap F E f y * g⁻¹ := by
  let := extensionAlgebra F E f
  exact extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm F E f hGal _

/-- Conjugation preserves the integer degree on the extension Weil group. -/
theorem localDegree_finiteGaloisWeilConjugation
    (g : localWeilGroup F) (y : localWeilGroup E) :
    localDegree E (finiteGaloisWeilConjugation F E f hGal g y) = localDegree E y := by
  have h := congrArg (localDegree F)
    (extensionWeilMap_finiteGaloisWeilConjugation F E f hGal g y)
  simp only [localDegree_extensionWeilMap, map_mul, map_inv] at h
  have h' : localDegree E (finiteGaloisWeilConjugation F E f hGal g y) ^
      extensionResidueDegree F E f =
      localDegree E y ^ extensionResidueDegree F E f := by
    simpa only [mul_inv_cancel_comm] using h
  apply Multiplicative.toAdd.injective
  have hh := congrArg Multiplicative.toAdd h'
  simp only [toAdd_pow, nsmul_eq_mul] at hh
  exact mul_left_cancel₀
    (by exact_mod_cast (extensionResidueDegree_pos F E f).ne') hh

/-- The reciprocity map has the arithmetic (negative) order convention. -/
theorem finiteGaloisKernelReciprocity_order (e : ReciprocityCandidate E)
    (he : LocalReciprocityCandidateRelation E.canonicalTopologicalData
      (localResidueDegree E) e)
    (n : letI := extensionAlgebra F E f
      (finiteGaloisQuotient F E f hGal).toMonoidHom.ker) :
    E.canonicalTopologicalData.orderHom
        (finiteGaloisKernelReciprocity F E f hGal e n) =
      (localDegree E ((finiteGaloisQuotientKernelEquiv F E f hGal).symm n))⁻¹ := by
  let := extensionAlgebra F E f
  change E.canonicalTopologicalData.orderHom
    ((reciprocityUnits E e
      ((finiteGaloisQuotientKernelEquiv F E f hGal).symm n))⁻¹) = _
  rw [map_inv, reciprocityUnits_order E e he]

/-- The order of inverse geometric reciprocity is invariant under conjugation. -/
theorem finiteGaloisKernelReciprocity_conjugate_order (e : ReciprocityCandidate E)
    (he : LocalReciprocityCandidateRelation E.canonicalTopologicalData
      (localResidueDegree E) e) (g : localWeilGroup F)
    (n : letI := extensionAlgebra F E f
      (finiteGaloisQuotient F E f hGal).toMonoidHom.ker) :
    letI := extensionAlgebra F E f
    E.canonicalTopologicalData.orderHom
        (finiteGaloisKernelReciprocity F E f hGal e
          (GroupExtensionPushout.conjugateKernel
            (finiteGaloisQuotient F E f hGal).toMonoidHom g n)) =
      E.canonicalTopologicalData.orderHom
        (finiteGaloisKernelReciprocity F E f hGal e n) := by
  let := extensionAlgebra F E f
  rw [finiteGaloisKernelReciprocity_order F E f hGal e he,
    finiteGaloisKernelReciprocity_order F E f hGal e he]
  have h := localDegree_finiteGaloisWeilConjugation F E f hGal g
    ((finiteGaloisQuotientKernelEquiv F E f hGal).symm n)
  simp only [finiteGaloisWeilConjugation, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.apply_symm_apply] at h
  exact congrArg Inv.inv h

end Langlands.Weil.Local
