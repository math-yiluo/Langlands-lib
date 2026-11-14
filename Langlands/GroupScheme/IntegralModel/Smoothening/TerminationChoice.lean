import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationKrull
import Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Adapted generators of the augmentation ideal

Let `C` be a Noetherian algebra over a local ring `R` with point `ε`, augmentation ideal `I`,
cotangent module `T = I/I²`, and an ideal `J`. Choose elements `z k ∈ J ∩ I` whose differentials
reduce to a basis of the image of `J ∩ I` in `k ⊗ T`, and elements `x j ∈ I` completing it to a
basis of `k ⊗ T`. Choose residue-field-valued forms `l m` on `T` dual to the `z k`. This module
constructs these data and proves the properties used by the defect drop. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} [CommRing R] [IsLocalRing R] {C : Type u} [CommRing C] [Algebra R C]

/-- The data of adapted generators. -/
structure GoodChoice (ε : C →ₐ[R] R) (ϖ : R) (J : Ideal C) where
  c : ℕ
  t : ℕ
  z : Fin c → C
  x : Fin t → C
  l : Fin c → Cot ε →ₗ[R] ResidueField R
  z_mem_J : ∀ k, z k ∈ J
  z_mem_I : ∀ k, z k ∈ augIdeal ε
  x_mem_I : ∀ j, x j ∈ augIdeal ε
  hl : ∀ k m, l m (dif ε (z k)) = if k = m then 1 else 0
  hgen : augIdeal ε ≤
    Ideal.span (Set.range z) ⊔ Ideal.span (Set.range x) ⊔ ptIdeal ε ϖ * augIdeal ε
  hxind : ∀ a : Fin t → R, (∑ j, a j • x j) ∈ J ⊔ augIdeal ε ^ 2 →
    ∀ j, a j ∈ maximalIdeal R

section Rho

variable (ε : C →ₐ[R] R)

/-- The reduction map `T → k ⊗ T`. -/
abbrev rho : Cot ε →ₗ[R] ResidueField R ⊗[R] Cot ε := TensorProduct.mk R _ _ 1

theorem rho_eq_zero_iff (t : Cot ε) :
    rho ε t = 0 ↔ t ∈ maximalIdeal R • (⊤ : Submodule R (Cot ε)) :=
  one_tmul_eq_zero_iff t

theorem exists_rho_dif (v : ResidueField R ⊗[R] Cot ε) :
    ∃ i ∈ augIdeal ε, rho ε (dif ε i) = v := by
  obtain ⟨t, rfl⟩ := exists_one_tmul_eq v
  obtain ⟨⟨i, hi⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
  exact ⟨i, hi, by rw [dif_of_mem ε hi]; rfl⟩

/-- The image of `J ∩ I` in `k ⊗ T`. -/
def imageJ (J : Ideal C) : Submodule (ResidueField R) (ResidueField R ⊗[R] Cot ε) where
  carrier := {v | ∃ j ∈ J ⊓ augIdeal ε, rho ε (dif ε j) = v}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [map_add, map_add]⟩
  zero_mem' := ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
  smul_mem' := by
    rintro r _ ⟨a, ha, rfl⟩
    obtain ⟨s, rfl⟩ := residue_surjective r
    refine ⟨algebraMap R C s * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [← Algebra.smul_def, map_smul, map_smul, ← IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul]

theorem mem_imageJ {J : Ideal C} {v} :
    v ∈ imageJ ε J ↔ ∃ j ∈ J ⊓ augIdeal ε, rho ε (dif ε j) = v := Iff.rfl

end Rho

section Lemmas

variable (ε : C →ₐ[R] R)

omit [IsLocalRing R] in
theorem dif_mul_of_mem (c : C) {y : C} (hy : y ∈ augIdeal ε) :
    dif ε (c * y) = ε c • dif ε y := by
  rw [dif_mul, RingHom.mem_ker.mp hy, zero_smul, add_zero]

omit [IsLocalRing R] in
/-- The cotangent module of a Noetherian algebra is finitely generated over the base. -/
theorem cot_finite [IsNoetherianRing C] : Module.Finite R (Cot ε) := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (augIdeal ε) : (augIdeal ε).FG)
  classical
  refine ⟨⟨s.image (dif ε), ?_⟩⟩
  rw [eq_top_iff]
  rintro t -
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [← dif_of_mem ε hy]
  have hy' : y ∈ Submodule.span C (s : Set C) := hs ▸ hy
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.mp hy'
  rw [map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hgI : g ∈ augIdeal ε := hs ▸ Submodule.subset_span hg
  rw [smul_eq_mul, dif_mul_of_mem ε _ hgI]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hg))

/-- An element of the augmentation ideal whose class in `k ⊗ T` vanishes lies in `𝔪 I`, where
`𝔪 = ε⁻¹(ϖ R)`. -/
theorem mem_of_rho_dif_eq_zero {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) {y : C}
    (hy : y ∈ augIdeal ε) (h0 : rho ε (dif ε y) = 0) :
    y ∈ ptIdeal ε ϖ * augIdeal ε := by
  set P : Ideal C := ptIdeal ε ϖ * augIdeal ε
  set Q : Submodule R (Cot ε) :=
    ((Submodule.comap (augIdeal ε).subtype P).map (augIdeal ε).toCotangent).restrictScalars R
  have hQ : maximalIdeal R • (⊤ : Submodule R (Cot ε)) ≤ Q := by
    rw [Submodule.smul_le]
    intro r hr t _
    obtain ⟨⟨i, hi⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
    rw [Submodule.restrictScalars_mem, Submodule.mem_map]
    refine ⟨⟨algebraMap R C r * i, Ideal.mul_mem_left _ _ hi⟩, ?_, ?_⟩
    · rw [Submodule.mem_comap, Submodule.subtype_apply]
      refine Ideal.mul_mem_mul ?_ hi
      rw [ptIdeal, Ideal.mem_comap, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← hϖ]
      exact hr
    · rw [← LinearMap.map_smul_of_tower]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
  rw [dif_of_mem ε hy, rho_eq_zero_iff] at h0
  obtain ⟨⟨y', hy'⟩, hy'P, hyy⟩ := (Submodule.mem_map.mp (hQ h0))
  rw [Submodule.mem_comap, Submodule.subtype_apply] at hy'P
  rw [Ideal.toCotangent_eq] at hyy
  have hIP : augIdeal ε ^ 2 ≤ P := by
    rw [pow_two]
    exact Ideal.mul_mono_left (augIdeal_le_ptIdeal ε ϖ)
  have : y = y' - (y' - y) := by ring
  rw [this]
  exact Submodule.sub_mem _ hy'P (hIP hyy)

end Lemmas

section Existence

variable (ε : C →ₐ[R] R)

theorem rho_dif_algebraMap_mul (r : R) (y : C) :
    rho ε (dif ε (algebraMap R C r * y)) = residue R r • rho ε (dif ε y) := by
  rw [← Algebra.smul_def, map_smul, map_smul, ← IsLocalRing.ResidueField.algebraMap_eq,
    algebraMap_smul]

/-- **Existence of adapted generators.** -/
theorem exists_goodChoice [IsNoetherianRing C] {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (J : Ideal C) : Nonempty (GoodChoice ε ϖ J) := by
  classical
  have := cot_finite ε
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl (imageJ ε J)
  have : Module.Free (ResidueField R) (imageJ ε J) :=
    Module.Free.of_divisionRing (ResidueField R) (imageJ ε J)
  have : Module.Free (ResidueField R) W' := Module.Free.of_divisionRing (ResidueField R) W'
  have : Module.Finite (ResidueField R) (ResidueField R ⊗[R] Cot ε) :=
    Module.Finite.base_change R (ResidueField R) (Cot ε)
  have : Module.Finite (ResidueField R) (imageJ ε J) :=
    Module.Finite.of_injective (imageJ ε J).subtype Subtype.val_injective
  have : Module.Finite (ResidueField R) W' :=
    Module.Finite.of_injective W'.subtype Subtype.val_injective
  let bW := Module.finBasis (ResidueField R) (imageJ ε J)
  let bW' := Module.finBasis (ResidueField R) W'
  let e := Submodule.prodEquivOfIsCompl (imageJ ε J) W' hW
  let bV := (bW.prod bW').map e
  have hbV_inl : ∀ i, bV (Sum.inl i) = (bW i : ResidueField R ⊗[R] Cot ε) := by
    intro i
    simp only [bV, Module.Basis.map_apply, e, Submodule.coe_prodEquivOfIsCompl',
      Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd, Submodule.coe_zero,
      add_zero]
  have hbV_inr : ∀ j, bV (Sum.inr j) = (bW' j : ResidueField R ⊗[R] Cot ε) := by
    intro j
    simp only [bV, Module.Basis.map_apply, e, Submodule.coe_prodEquivOfIsCompl',
      Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd, Submodule.coe_zero,
      zero_add]
  have hW0 : ∀ w ∈ imageJ ε J, ∀ j, bV.repr w (Sum.inr j) = 0 := by
    intro w hw j
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply,
      show e.symm w = ((⟨w, hw⟩ : imageJ ε J), (0 : W')) from
        Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hW ⟨w, hw⟩]
    simp
  choose z hzJI hzv using fun i => (bW i).2
  choose x hxI hxv using fun j => exists_rho_dif ε (bW' j : ResidueField R ⊗[R] Cot ε)
  choose lift hlift using fun a : ResidueField R => residue_surjective a
  refine ⟨⟨_, _, z, x, fun m => ((bV.coord (Sum.inl m)).restrictScalars R) ∘ₗ rho ε,
    fun k => (hzJI k).1, fun k => (hzJI k).2, hxI, ?_, ?_, ?_⟩⟩
  · intro k m
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hzv, ← hbV_inl,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Sum.inl.injEq]
  · intro i hi
    set v := rho ε (dif ε i)
    set y := i - ∑ k, algebraMap R C (lift (bV.repr v (Sum.inl k))) * z k -
      ∑ j, algebraMap R C (lift (bV.repr v (Sum.inr j))) * x j
    have hyI : y ∈ augIdeal ε :=
      Submodule.sub_mem _ (Submodule.sub_mem _ hi (Ideal.sum_mem _ fun k _ =>
        Ideal.mul_mem_left _ _ (hzJI k).2)) (Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (hxI j))
    have hy0 : rho ε (dif ε y) = 0 := by
      have hsum := bV.sum_repr v
      rw [Fintype.sum_sum_type] at hsum
      simp only [y, map_sub, map_sum, rho_dif_algebraMap_mul, hlift, hzv, hxv, ← hbV_inl,
        ← hbV_inr]
      rw [sub_sub, hsum, sub_self]
    have hyP := mem_of_rho_dif_eq_zero ε hϖ hyI hy0
    have hi_eq : i = y + ∑ k, algebraMap R C (lift (bV.repr v (Sum.inl k))) * z k +
        ∑ j, algebraMap R C (lift (bV.repr v (Sum.inr j))) * x j := by
      simp only [y]
      ring
    rw [hi_eq]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_right hyP
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Ideal.sum_mem _ fun k _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k))))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))))
  · intro a ha j1
    obtain ⟨j0, hj0, q, hq, hjq⟩ := Submodule.mem_sup.mp ha
    have hqI : q ∈ augIdeal ε := Ideal.pow_le_self two_ne_zero hq
    have hsumI : (∑ j, a j • x j) ∈ augIdeal ε :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hxI j)
    have hj0I : j0 ∈ augIdeal ε := by
      have : j0 = (∑ j, a j • x j) - q := by rw [← hjq]; ring
      rw [this]
      exact Submodule.sub_mem _ hsumI hqI
    have hw : rho ε (dif ε j0) ∈ imageJ ε J := ⟨j0, ⟨hj0, hj0I⟩, rfl⟩
    have heq : rho ε (dif ε j0) = ∑ j, residue R (a j) • bV (Sum.inr j) := by
      have h1 : dif ε j0 = dif ε (∑ j, a j • x j) := by
        rw [← hjq, map_add, dif_eq_zero_of_mem_sq ε hq, add_zero]
      rw [h1, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, hbV_inr, ← hxv j, ← IsLocalRing.ResidueField.algebraMap_eq,
        algebraMap_smul]
    have hc := hW0 _ hw j1
    rw [heq, map_sum] at hc
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, Sum.inr.injEq, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    rw [← residue_eq_zero_iff]
    exact hc

end Existence

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
