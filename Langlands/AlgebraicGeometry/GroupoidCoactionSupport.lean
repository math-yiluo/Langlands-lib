import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Langlands.AlgebraicGeometry.FlatModuleSupport

/-! # Support invariance for actual coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

namespace RingEtaleEquivalenceRelation

/-- Reversal of the universal arrow. -/
noncomputable def reversal (hE : RingEtaleEquivalenceRelation t) : C →+* C :=
  (hE.symm C (RingHom.id C)).choose

@[simp]
lemma reversal_comp_t (hE : RingEtaleEquivalenceRelation t) :
    hE.reversal.comp t = algebraMap B C := by
  simpa only [reversal, RingHom.id_comp] using (hE.symm C (RingHom.id C)).choose_spec.1

@[simp]
lemma reversal_comp_source (hE : RingEtaleEquivalenceRelation t) :
    hE.reversal.comp (algebraMap B C) = t := by
  simpa only [reversal, RingHom.id_comp] using (hE.symm C (RingHom.id C)).choose_spec.2

lemma reversal_comp_self (hE : RingEtaleEquivalenceRelation t) :
    hE.reversal.comp hE.reversal = RingHom.id C := by
  apply hE.hom_ext
  · rw [RingHom.comp_assoc, hE.reversal_comp_t, hE.reversal_comp_source,
      RingHom.id_comp]
  · rw [RingHom.comp_assoc, hE.reversal_comp_source, hE.reversal_comp_t,
      RingHom.id_comp]

lemma reversal_involutive (hE : RingEtaleEquivalenceRelation t) :
    Function.Involutive hE.reversal :=
  fun c => congrArg (fun f : C →+* C => f c) hE.reversal_comp_self

end RingEtaleEquivalenceRelation

namespace GroupoidCoaction

variable {M : Type v} [AddCommGroup M] [Module B M]

/-- Reverse an arrow and then apply its coaction. This acts on the source tensor
module and is semilinear for reversal on the coefficient ring. -/
noncomputable def reverseTensor (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) : C ⊗[B] M →+ C ⊗[B] M :=
  coactionCompose t M θ.coaction θ.map_smul hE.reversal (AlgHom.id B C)
    (by simp)

@[simp]
lemma reverseTensor_tmul (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (c : C) (m : M) :
    reverseTensor hE θ (c ⊗ₜ m) = hE.reversal c • θ.coaction m := by
  simp [reverseTensor, coactionCompose]

lemma reverseTensor_smul (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (c : C) (x : C ⊗[B] M) :
    reverseTensor hE θ (c • x) = hE.reversal c • reverseTensor hE θ x := by
  induction x with
  | tmul d m => simp [smul_tmul', smul_eq_mul, mul_smul]
  | add x y hx hy => simp [smul_add, hx, hy]

lemma reverseTensor_coaction (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (m : M) :
    reverseTensor hE θ (θ.coaction m) = (1 : C) ⊗ₜ m := by
  let φ : C →ₐ[B] C := (Algebra.ofId B C).comp hE.identity
  have hφ : (φ : C →+* C).comp t = algebraMap B C := by
    change (algebraMap B C).comp ((hE.identity : C →+* B).comp t) = _
    rw [hE.identity_comp_t, RingHom.comp_id]
  have hcomp : hE.reversal.comp (algebraMap B C) =
      (AlgHom.id B C : C →+* C).comp t := by
    simp
  have h₃ : (φ : C →+* C).comp t = hE.reversal.comp t := by
    rw [hφ, hE.reversal_comp_t]
  exact (θ.coassoc C hE.reversal (AlgHom.id B C) φ hcomp h₃ m).symm.trans
    (θ.counit C φ hφ m)

lemma reverseTensor_involutive (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) : Function.Involutive (reverseTensor hE θ) := by
  intro x
  induction x with
  | tmul c m =>
    rw [reverseTensor_tmul, reverseTensor_smul, hE.reversal_involutive,
      reverseTensor_coaction, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp [hx, hy]

/-- The involutive additive equivalence on the source tensor module induced by
arrow reversal and the actual coaction. -/
noncomputable def reverseTensorEquiv (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) : C ⊗[B] M ≃+ C ⊗[B] M where
  toFun := reverseTensor hE θ
  invFun := reverseTensor hE θ
  left_inv := reverseTensor_involutive hE θ
  right_inv := reverseTensor_involutive hE θ
  map_add' := (reverseTensor hE θ).map_add

lemma support_reverseTensor (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) :
    Module.support C (C ⊗[B] M) =
      PrimeSpectrum.comap hE.reversal ⁻¹' Module.support C (C ⊗[B] M) := by
  have hforward : ∀ q : PrimeSpectrum C,
      q ∈ Module.support C (C ⊗[B] M) →
        PrimeSpectrum.comap hE.reversal q ∈ Module.support C (C ⊗[B] M) := by
    intro q hq
    obtain ⟨x, hx⟩ := Module.mem_support_iff'.mp hq
    apply Module.mem_support_iff'.mpr
    refine ⟨reverseTensor hE θ x, fun c hc hz => hx (hE.reversal c) hc ?_⟩
    have h := congrArg (reverseTensor hE θ) hz
    simpa only [reverseTensor_smul, reverseTensor_involutive hE θ x, map_zero] using h
  ext q
  constructor
  · exact hforward q
  · intro hq
    have h := hforward (PrimeSpectrum.comap hE.reversal q) hq
    change PrimeSpectrum.comap (hE.reversal.comp hE.reversal) q ∈
      Module.support C (C ⊗[B] M) at h
    simpa only [hE.reversal_comp_self, PrimeSpectrum.comap_id] using h

/-- Source and target inverse images of the support of any actual coaction agree. -/
lemma support_preimage_eq (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) :
    PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M =
      PrimeSpectrum.comap t ⁻¹' Module.support B M := by
  let : Module.Flat B C := (RingHom.flat_algebraMap_iff).mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  have hsupport := FlatModuleSupport.support_tensor_eq B C M
  calc
    PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M =
        Module.support C (C ⊗[B] M) := hsupport.symm
    _ = PrimeSpectrum.comap hE.reversal ⁻¹' Module.support C (C ⊗[B] M) :=
      support_reverseTensor hE θ
    _ = PrimeSpectrum.comap t ⁻¹' Module.support B M := by
      rw [hsupport, ← Set.preimage_comp, ← PrimeSpectrum.comap_comp,
        hE.reversal_comp_source]

end GroupoidCoaction

end Langlands.AlgebraicGeometry
