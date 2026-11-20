import Langlands.RingTheory.Smooth.SectionJetNoetherianModel
import Langlands.RingTheory.Smooth.SectionJetVanishing

/-! # Finite-jet detection over arbitrary coefficient rings -/

noncomputable section

universe u w

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra.SectionJet

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {ε : B →ₐ[R] R} {J : Ideal B}

namespace NoetherianModel

variable (M : NoetherianModel ε J) (S : Type w) [CommRing S] [Algebra R S]
  [Algebra M.Base S] [IsScalarTower M.Base R S]

/-- The comparison with a smooth augmented model after an arbitrary scalar extension. -/
def scalarExtensionEquiv : S ⊗[M.Base] M.Model ≃ₐ[S] S ⊗[R] B :=
  (Algebra.TensorProduct.cancelBaseChange M.Base R S S M.Model).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) M.comparison)

@[simp]
theorem scalarExtensionEquiv_tmul (s : S) (b : M.Model) :
    M.scalarExtensionEquiv S (s ⊗ₜ[M.Base] b) =
      s ⊗ₜ[R] M.comparison (1 ⊗ₜ[M.Base] b) := by
  simp only [scalarExtensionEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply,
    AlgEquiv.coe_toAlgHom]

/-- The comparison over the test ring preserves the section. -/
theorem scalarExtensionEquiv_augmentation (z : S ⊗[M.Base] M.Model) :
    baseChangeAugmentation ε S (M.scalarExtensionEquiv S z) =
      baseChangeAugmentation M.augmentation S z := by
  induction z using TensorProduct.inductionOn with
  | tmul s b =>
    rw [scalarExtensionEquiv_tmul, baseChangeAugmentation_tmul, M.augmentation_eq,
      baseChangeAugmentation_tmul, baseChangeAugmentation_tmul, one_mul,
      IsScalarTower.algebraMap_apply M.Base R S]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The comparison over the test ring takes the model ideal to the extended ideal. -/
theorem scalarExtensionEquiv_ideal :
    (M.ideal.map
      (Algebra.TensorProduct.includeRight : M.Model →ₐ[M.Base] S ⊗[M.Base] M.Model).toRingHom).map
        (M.scalarExtensionEquiv S).toRingEquiv.toRingHom =
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom := by
  have hi := congrArg (Ideal.map
    (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) M.ideal_map
  rw [← hi, Ideal.map_map, Ideal.map_map]
  congr 1

end NoetherianModel

/-- A finitely generated ideal of a smooth augmented algebra vanishes near the
section after any scalar extension on which a sufficiently large jet vanishes. -/
theorem exists_order_of_finite_ideal_vanishing_near_section [Smooth R B]
    (ε : B →ₐ[R] R) (J : Ideal B) (hJ : J.FG) :
    ∃ n : ℕ, ∀ (S : Type w) [CommRing S] [Algebra R S],
      (∀ b ∈ J, (1 ⊗ₜ[R] Ideal.Quotient.mk _ b : S ⊗[R] Quotient ε n) = 0) →
      ∃ f : S ⊗[R] B, baseChangeAugmentation ε S f = 1 ∧
        ∀ b ∈ J, f * (1 ⊗ₜ[R] b) = 0 := by
  let M := noetherianModel ε J hJ
  obtain ⟨n, hn⟩ := exists_order_of_vanishing_near_section.{u,u,w} M.augmentation M.ideal
  refine ⟨n, fun S _ _ h => ?_⟩
  let : Algebra M.Base S := ((algebraMap R S).comp (algebraMap M.Base R)).toAlgebra
  let : IsScalarTower M.Base R S := IsScalarTower.of_algebraMap_eq' rfl
  let cmp := M.scalarExtensionEquiv S
  let inc := (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom
  let incM := (Algebra.TensorProduct.includeRight :
    M.Model →ₐ[M.Base] S ⊗[M.Base] M.Model).toRingHom
  let I := RingHom.ker (baseChangeAugmentation ε S)
  let IM := RingHom.ker (baseChangeAugmentation M.augmentation S)
  have hker : IM = I.comap cmp.toRingEquiv := by
    ext x
    change baseChangeAugmentation M.augmentation S x = 0 ↔
      baseChangeAugmentation ε S (cmp x) = 0
    rw [M.scalarExtensionEquiv_augmentation]
  have hpow : (IM ^ (n + 1)).map cmp.toRingEquiv = I ^ (n + 1) := by
    rw [Ideal.map_pow, hker, Ideal.map_comap_eq_self_of_equiv]
  have hJet : J.map inc ≤ I ^ (n + 1) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change (1 ⊗ₜ[R] b : S ⊗[R] B) ∈ I ^ (n + 1)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (baseChangeEquiv ε S n) (h b hb)
    simpa only [baseChangeEquiv_tmul_mk, map_zero] using he
  have hM (b : M.Model) (hb : b ∈ M.ideal) :
      (1 ⊗ₜ[M.Base] Ideal.Quotient.mk _ b : S ⊗[M.Base] Quotient M.augmentation n) = 0 := by
    apply (baseChangeEquiv M.augmentation S n).injective
    rw [baseChangeEquiv_tmul_mk, map_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (Ideal.apply_mem_of_equiv_iff (f := cmp.toRingEquiv)).mp
    rw [hpow]
    apply hJet
    rw [← M.scalarExtensionEquiv_ideal S]
    exact Ideal.mem_map_of_mem cmp.toRingEquiv (Ideal.mem_map_of_mem incM hb)
  obtain ⟨f, hf, hfJ⟩ := hn S hM
  refine ⟨cmp f, (M.scalarExtensionEquiv_augmentation S f).trans hf, ?_⟩
  have hc : J.map inc ≤ (Ideal.span {cmp f}).annihilator := by
    rw [← M.scalarExtensionEquiv_ideal S, Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    have hfb : cmp f * cmp (incM b) = 0 := by
      change cmp f * cmp (1 ⊗ₜ[M.Base] b) = 0
      simpa only [map_mul, map_zero] using congrArg cmp (hfJ b hb)
    apply Submodule.mem_annihilator.mpr
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    change cmp (incM b) * (c * cmp f) = 0
    calc
      _ = c * (cmp f * cmp (incM b)) := by ac_rfl
      _ = 0 := by rw [hfb, mul_zero]
  intro b hb
  have hz := Submodule.mem_annihilator.mp (hc (Ideal.mem_map_of_mem inc hb))
    (cmp f) (Ideal.mem_span_singleton_self _)
  exact (mul_comm _ _).trans hz

end Algebra.SectionJet
