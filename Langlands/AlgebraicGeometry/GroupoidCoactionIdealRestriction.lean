import Langlands.AlgebraicGeometry.GroupoidCoactionScalarChange
import Langlands.AlgebraicGeometry.GroupoidCoactionIdealQuotient
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationQuotient

/-! # Restricting a coaction to the actual quotient rings -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]

lemma rTensor_quotient_injective_of_annihilator (J : Ideal C)
    (hJ : J ≤ Module.annihilator C (C ⊗[B] M)) :
    Function.Injective (LinearMap.rTensor M (Ideal.Quotient.mkₐ B J).toLinearMap) := by
  let q : C →ₗ[B] C ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap
  have hzero : LinearMap.rTensor M q.ker.subtype = 0 := by
    ext c m
    change (c : C) ⊗ₜ[B] m = 0
    have hc : (c : C) ∈ J := (Ideal.Quotient.eq_zero_iff_mem).mp c.property
    have hann := Module.mem_annihilator.mp (hJ hc) ((1 : C) ⊗ₜ[B] m)
    simpa only [smul_tmul', smul_eq_mul, mul_one] using hann
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (LinearMap.rTensor M q) = ⊥
  have hexact : Function.Exact (LinearMap.rTensor M q.ker.subtype)
      (LinearMap.rTensor M q) :=
    _root_.rTensor_exact M (LinearMap.exact_subtype_ker_map q)
      (Ideal.Quotient.mkₐ_surjective B J)
  rw [Function.Exact.linearMap_ker_eq hexact, hzero, LinearMap.range_zero]

lemma quotientModule_scalarTower (I : Ideal B) :
    IsScalarTower B (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) :=
  Module.IsTorsionBySet.isScalarTower
    (Module.isTorsionBySet_quotient_ideal_smul M I)

attribute [local instance] quotientModule_scalarTower

/-- Changing both tensor factors to the quotient rings loses no information
when the module has already been reduced modulo the ideal. -/
lemma idealRestriction_tensor_injective (I : Ideal B) :
    Function.Injective (scalarChangeTensor
      (M := M ⧸ (I • ⊤ : Submodule B M)) (S := B ⧸ I)
      (Ideal.Quotient.mkₐ B (I.map (algebraMap B C)))) := by
  let N := M ⧸ (I • ⊤ : Submodule B M)
  let D := C ⧸ I.map (algebraMap B C)
  let f : C →ₐ[B] D := Ideal.Quotient.mkₐ B (I.map (algebraMap B C))
  let : TensorProduct.CompatibleSMul B (B ⧸ I) D N :=
    ⟨fun s c m => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
      change (algebraMap B (B ⧸ I) b • c) ⊗ₜ[B] m =
        c ⊗ₜ[B] (algebraMap B (B ⧸ I) b • m)
      rw [IsScalarTower.algebraMap_smul (B ⧸ I),
        IsScalarTower.algebraMap_smul (B ⧸ I)]
      exact TensorProduct.smul_tmul b c m⟩
  let e : D ⊗[B] N ≃ₗ[B] D ⊗[B ⧸ I] N :=
    TensorProduct.equivOfCompatibleSMul (B ⧸ I) B B D N
  have hmap (x : C ⊗[B] N) :
      scalarChangeTensor (S := B ⧸ I) f x =
        e (LinearMap.rTensor N f.toLinearMap x) := by
    induction x with
    | tmul c m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply rTensor_quotient_injective_of_annihilator
    (I.map (algebraMap B C)) (map_source_le_annihilator_tensor_quotient (M := M) I)
  apply e.injective
  exact (hmap x).symm.trans (hxy.trans (hmap y))

/-- The ideal quotient coaction, now over the actual restricted relation. -/
def idealRestriction (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) :
    GroupoidCoaction (RingEtaleEquivalenceRelation.quotientTarget I hI)
      (M ⧸ (I • ⊤ : Submodule B M)) :=
  scalarChange (idealQuotient θ I hI.ge)
    (Ideal.Quotient.mkₐ B (I.map (algebraMap B C)))
    Ideal.Quotient.mk_surjective
    (RingEtaleEquivalenceRelation.quotientTarget_comp_mk I hI)

lemma idealRestriction_mem_invariants_iff (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t)
    (m : M ⧸ (I • ⊤ : Submodule B M)) :
    m ∈ (idealRestriction θ I hI).invariants ↔
      m ∈ (idealQuotient θ I hI.ge).invariants :=
  scalarChange_mem_invariants_iff (idealQuotient θ I hI.ge)
    (Ideal.Quotient.mkₐ B (I.map (algebraMap B C)))
    Ideal.Quotient.mk_surjective
    (RingEtaleEquivalenceRelation.quotientTarget_comp_mk I hI)
    (idealRestriction_tensor_injective (M := M) I) m

end Langlands.AlgebraicGeometry.GroupoidCoaction
