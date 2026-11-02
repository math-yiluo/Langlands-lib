import Langlands.AlgebraicGeometry.GroupoidCoactionHom
import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleExtension
import Langlands.AlgebraicGeometry.GroupoidCoactionSubmodule
import Langlands.AlgebraicGeometry.GroupoidCoactionIdealQuotient
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComoduleExactness

/-! # Invariant ideals and coaction filtrations -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

/-- Multiplication from the scalar extension of an ideal to the coefficient ring. -/
noncomputable def idealTensorMap (I : Ideal B) : C ⊗[B] I →ₗ[C] C :=
  (AlgebraTensorModule.rid B C C).toLinearMap.comp
    (AlgebraTensorModule.lTensor C C I.subtype)

@[simp]
lemma idealTensorMap_tmul (I : Ideal B) (c : C) (b : I) :
    idealTensorMap (C := C) I (c ⊗ₜ b) = algebraMap B C b * c := by
  simp [idealTensorMap, Algebra.smul_def]

lemma range_idealTensorMap (I : Ideal B) :
    LinearMap.range (idealTensorMap (C := C) I) = I.map (algebraMap B C) := by
  apply le_antisymm
  · rintro c ⟨x, rfl⟩
    induction x with
    | tmul c b =>
      rw [idealTensorMap_tmul]
      exact Ideal.mul_mem_right c _ (Ideal.mem_map_of_mem _ b.property)
    | add x y hx hy =>
      simpa only [map_add] using Ideal.add_mem (I.map (algebraMap B C)) hx hy
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    refine ⟨(1 : C) ⊗ₜ[B] (⟨b, hb⟩ : I), ?_⟩
    simp

/-- Equality of the ideals obtained by the target and source maps. -/
def IsInvariantIdeal (t : B →+* C) (I : Ideal B) : Prop :=
  I.map t = I.map (algebraMap B C)

lemma IsInvariantIdeal.sup {I J : Ideal B}
    (hI : IsInvariantIdeal t I) (hJ : IsInvariantIdeal t J) :
    IsInvariantIdeal t (I ⊔ J) := by
  simp only [IsInvariantIdeal, Ideal.map_sup] at *
  rw [hI, hJ]

lemma IsInvariantIdeal.mul {I J : Ideal B}
    (hI : IsInvariantIdeal t I) (hJ : IsInvariantIdeal t J) :
    IsInvariantIdeal t (I * J) := by
  simp only [IsInvariantIdeal, Ideal.map_mul] at *
  rw [hI, hJ]

lemma IsInvariantIdeal.pow {I : Ideal B} (hI : IsInvariantIdeal t I) (n : ℕ) :
    IsInvariantIdeal t (I ^ n) := by
  simp only [IsInvariantIdeal, Ideal.map_pow] at *
  rw [hI]

lemma map_target_le_iff_isInvariantIdeal (hE : RingEtaleEquivalenceRelation t)
    (I : Ideal B) :
    I.map t ≤ I.map (algebraMap B C) ↔ IsInvariantIdeal t I := by
  constructor
  · intro hI
    apply le_antisymm hI
    have hrev := Ideal.map_mono (f := hE.reversal) hI
    simpa only [Ideal.map_map, hE.reversal_comp_t,
      hE.reversal_comp_source] using hrev
  · exact fun hI => hI.le

/-- Stability of an ideal for the regular coaction is target-source containment. -/
lemma regular_isStableSubmodule_iff (I : Ideal B) :
    (regular t).IsStableSubmodule I ↔ I.map t ≤ I.map (algebraMap B C) := by
  constructor
  · intro hI
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨x, hx⟩ := hI ⟨b, hb⟩
    rw [← range_idealTensorMap]
    refine ⟨x, ?_⟩
    change (AlgebraTensorModule.rid B C C)
      (AlgebraTensorModule.lTensor C C I.subtype x) = t b
    rw [hx, regular_coaction]
    simp
  · intro hI b
    have hb := hI (Ideal.mem_map_of_mem t b.property)
    rw [← range_idealTensorMap] at hb
    obtain ⟨x, hx⟩ := hb
    refine ⟨x, ?_⟩
    apply (AlgebraTensorModule.rid B C C).injective
    change idealTensorMap I x = (AlgebraTensorModule.rid B C C) ((regular t).coaction b)
    rw [hx, regular_coaction]
    simp

lemma isInvariantIdeal_iff_regular_isStableSubmodule
    (hE : RingEtaleEquivalenceRelation t) (I : Ideal B) :
    IsInvariantIdeal t I ↔ (regular t).IsStableSubmodule I :=
  (map_target_le_iff_isInvariantIdeal hE I).symm.trans
    (regular_isStableSubmodule_iff I).symm

variable {M : Type v} [AddCommGroup M] [Module B M]

/-- The scalar endomorphism map commutes with the regular and Hom coactions. -/
lemma hom_coaction_lsmul [Module.FinitePresentation B M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M) (b : B) :
    (hom hE θ θ).coaction (LinearMap.lsmul B M b) =
      AlgebraTensorModule.lTensor C C (LinearMap.lsmul B M)
        ((regular t).coaction b) := by
  have hid : LinearMap.id ∈ (hom hE θ θ).invariants :=
    (mem_hom_invariants_iff hE θ θ LinearMap.id).mpr (IsHom.id θ)
  change (hom hE θ θ).coaction (b • (LinearMap.id : M →ₗ[B] M)) = _
  rw [(hom hE θ θ).map_smul,
    show (hom hE θ θ).coaction LinearMap.id = (1 : C) ⊗ₜ LinearMap.id from hid,
    regular_coaction, AlgebraTensorModule.lTensor_tmul]
  rw [show LinearMap.lsmul B M 1 = LinearMap.id by
    ext m
    exact one_smul B m]
  simp [smul_tmul', smul_eq_mul]

/-- Annihilators of finitely presented coactions are invariant ideals. -/
lemma annihilator_isInvariantIdeal [Module.FinitePresentation B M]
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M) :
    IsInvariantIdeal t (Module.annihilator B M) := by
  apply (isInvariantIdeal_iff_regular_isStableSubmodule hE _).mpr
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  have hker : LinearMap.ker (LinearMap.lsmul B M) = Module.annihilator B M := by
    ext b
    exact Module.mem_annihilator_iff_lsmul_eq_zero.symm
  rw [← hker]
  intro b
  rw [← Module.Flat.ker_lTensor_eq C C (LinearMap.lsmul B M)]
  change AlgebraTensorModule.lTensor C C (LinearMap.lsmul B M)
    ((regular t).coaction b) = 0
  rw [← hom_coaction_lsmul hE θ b, show LinearMap.lsmul B M b = 0 from b.property,
    map_zero]

/-- Flatness identifies stability with vanishing after tensoring the quotient. -/
lemma isStableSubmodule_iff_lTensor_mkQ_eq_zero [Module.Flat B C]
    (θ : GroupoidCoaction t M) (N : Submodule B M) :
    θ.IsStableSubmodule N ↔
      ∀ m ∈ N, LinearMap.lTensor C N.mkQ (θ.coaction m) = 0 := by
  have hker : LinearMap.ker (AlgebraTensorModule.lTensor C C N.mkQ) =
      LinearMap.range (AlgebraTensorModule.lTensor C C N.subtype) := by
    rw [Module.Flat.ker_lTensor_eq, Submodule.ker_mkQ]
  constructor
  · intro h m hm
    have hx := h ⟨m, hm⟩
    rw [← hker] at hx
    exact hx
  · intro h m
    rw [← hker]
    exact h m m.property

/-- Multiplication by an invariant ideal gives a stable submodule. -/
lemma IsInvariantIdeal.isStableSubmodule_smul_top [Module.Flat B C]
    {I : Ideal B} (hI : IsInvariantIdeal t I) (θ : GroupoidCoaction t M) :
    θ.IsStableSubmodule (I • ⊤ : Submodule B M) :=
  (isStableSubmodule_iff_lTensor_mkQ_eq_zero θ _).mpr
    (ideal_smul_top_stable θ I hI.le)

/-- Every term of the invariant ideal-power filtration is stable. -/
lemma IsInvariantIdeal.isStableSubmodule_pow_smul_top [Module.Flat B C]
    {I : Ideal B} (hI : IsInvariantIdeal t I) (θ : GroupoidCoaction t M) (n : ℕ) :
    θ.IsStableSubmodule (I ^ n • ⊤ : Submodule B M) :=
  (hI.pow n).isStableSubmodule_smul_top θ

end Langlands.AlgebraicGeometry.GroupoidCoaction
