import Langlands.AlgebraicGeometry.PointTopology.HenselianFiniteEtaleProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianIffSeparablyClosedProof
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite separable extensions of the completion come from `K` (non-archimedean case)

Let `K` be a non-archimedean nontrivially normed field that is separably closed in its
completion `K̂`, and let `E/K̂` be finite separable with primitive element `β` and minimal
polynomial `h` of degree `n`. Inside an algebraic closure `Ω` of `K̂` with the spectral norm:

* `r > 0` bounds the distance from `β` to its other conjugates;
* a monic `g₀ ∈ K[X]` of degree `n` with coefficients close to those of `h` has `‖g₀(β)‖ < r ^ n`,
  so some root `γ` of `g₀` satisfies `‖β - γ‖ < r`;
* Krasner's lemma gives `β ∈ K̂(γ)`, hence `K̂(γ) = K̂(β)` by degrees.

So `γ` lies in `E`, and `L = K(γ)` is a finite separable extension of degree `n` with
`K̂ ⊗_K L ≅ E`.
-/

noncomputable section

universe u

open Polynomial IntermediateField
open scoped TensorProduct NNReal

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianFiniteEtale

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "K̂" => UniformSpace.Completion K

/-- **Non-archimedean case.** Every finite separable extension of `K̂` is `K̂ ⊗_K L` for a finite
separable extension `L` of `K`. -/
theorem exists_field_of_isUltrametricDist (hsep : separableClosure K K̂ = ⊥) (E : Type u)
    [Field E] [Algebra K̂ E] [FiniteDimensional K̂ E] [Algebra.IsSeparable K̂ E] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      Algebra.IsSeparable K L ∧ Nonempty (K̂ ⊗[K] L ≃ₐ[K̂] E) := by
  classical
  let _ := HenselianIffSeparablyClosed.completionNormedField K
  have : IsUltrametricDist K̂ :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n => by
      rw [show ((n : K̂)) = ((n : K) : K̂) from
        (map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n).symm,
        UniformSpace.Completion.norm_coe]
      exact IsUltrametricDist.norm_natCast_le_one K n
  let Ω := AlgebraicClosure K̂
  let _ : NormedField Ω := spectralNorm.normedField K̂ Ω
  let _ : NormedAlgebra K̂ Ω := spectralNorm.normedAlgebra K̂ Ω
  have : IsKrasner K̂ Ω := IsKrasner.of_completeSpace_of_normal K̂ Ω
  -- the primitive element and its minimal polynomial
  set n := Module.finrank K̂ E with hn
  obtain ⟨β', hβ'⟩ := Field.exists_primitive_element K̂ E
  have hβ'int : IsIntegral K̂ β' := .of_finite K̂ β'
  set h := minpoly K̂ β' with hh
  have hhsep : h.Separable := Algebra.IsSeparable.isSeparable K̂ β'
  have hhm : h.Monic := minpoly.monic hβ'int
  have hhdeg : h.natDegree = n := by
    rw [hh, ← IntermediateField.adjoin.finrank hβ'int, hβ', IntermediateField.finrank_top']
  let ι : E →ₐ[K̂] Ω := IsAlgClosed.lift
  set β := ι β' with hβ
  have hβh : minpoly K̂ β = h := minpoly.algHom_eq ι ι.injective β'
  -- the distance to the other conjugates
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x : Ω, aeval x h = 0 → x ≠ β → r ≤ ‖β - x‖ := by
    let S := (h.map (algebraMap K̂ Ω)).roots.toFinset.erase β
    have hmemS : ∀ x : Ω, aeval x h = 0 → x ≠ β → x ∈ S := fun x hx hxβ => by
      rw [Finset.mem_erase, Multiset.mem_toFinset, mem_roots (hhm.map _).ne_zero, IsRoot,
        eval_map_algebraMap]
      exact ⟨hxβ, hx⟩
    by_cases hS : S.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := S.exists_min_image (fun x => ‖β - x‖) hS
      refine ⟨‖β - x0‖, norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hx0).symm),
        fun x hx hxβ => hmin x (hmemS x hx hxβ)⟩
    · exact ⟨1, one_pos, fun x hx hxβ => absurd ⟨x, hmemS x hx hxβ⟩ hS⟩
  -- approximate `h` by a monic polynomial over `K`
  set Cb : ℝ := max 1 ‖β‖ ^ n with hCb
  have hCb1 : 1 ≤ Cb := one_le_pow₀ (le_max_left _ _)
  set δ : ℝ := r ^ n / ((n + 1) * Cb) with hδ
  have hδ0 : 0 < δ := by positivity
  have happrox : ∀ k : Fin n, ∃ a : K, ‖((a : K̂)) - h.coeff k‖ < δ := fun k => by
    obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe
      (h.coeff k) δ hδ0
    exact ⟨a, by rw [← dist_eq_norm, dist_comm]; exact ha⟩
  choose a ha using happrox
  let g₀ : K[X] := X ^ n + ∑ k : Fin n, C (a k) * X ^ (k : ℕ)
  have hsumdeg : (∑ k : Fin n, C (a k) * X ^ (k : ℕ)).degree < (X ^ n : K[X]).degree := by
    rw [degree_X_pow]
    exact degree_sum_fin_lt a
  have hg₀m : g₀.Monic := monic_X_pow_add (degree_sum_fin_lt a)
  have hg₀deg : g₀.natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt hsumdeg, natDegree_X_pow]
  -- `g₀(β)` is small
  have hhsum : h = X ^ n + ∑ k : Fin n, C (h.coeff k) * X ^ (k : ℕ) := by
    conv_lhs => rw [hhm.as_sum, hhdeg]
    rw [Fin.sum_univ_eq_sum_range (fun k => C (h.coeff k) * X ^ k) n]
  have hβroot : aeval β h = 0 := by rw [← hβh]; exact minpoly.aeval K̂ β
  have hgβ : aeval β g₀ = ∑ k : Fin n, algebraMap K̂ Ω ((a k : K̂) - h.coeff k) * β ^ (k : ℕ) := by
    have h1 : aeval β h = β ^ n + ∑ k : Fin n, algebraMap K̂ Ω (h.coeff k) * β ^ (k : ℕ) := by
      conv_lhs => rw [hhsum]
      simp [map_sum]
    have h2 : aeval β g₀ = β ^ n + ∑ k : Fin n, algebraMap K̂ Ω (a k : K̂) * β ^ (k : ℕ) := by
      simp only [g₀, map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C]
      congr 1
    rw [h2, ← sub_zero (β ^ n + _), ← hβroot, h1]
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hgβsmall : ‖aeval β g₀‖ < r ^ n := by
    rw [hgβ]
    have hterm : ∀ k : Fin n, ‖algebraMap K̂ Ω ((a k : K̂) - h.coeff k) * β ^ (k : ℕ)‖ ≤ δ * Cb := by
      intro k
      rw [norm_mul, norm_algebraMap', norm_pow]
      refine mul_le_mul (ha k).le ?_ (by positivity) hδ0.le
      calc ‖β‖ ^ (k : ℕ) ≤ (max 1 ‖β‖) ^ (k : ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
        _ ≤ (max 1 ‖β‖) ^ n := pow_le_pow_right₀ (le_max_left _ _) k.is_lt.le
    calc ‖∑ k : Fin n, algebraMap K̂ Ω ((a k : K̂) - h.coeff k) * β ^ (k : ℕ)‖
        ≤ ∑ k : Fin n, ‖algebraMap K̂ Ω ((a k : K̂) - h.coeff k) * β ^ (k : ℕ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, δ * Cb := Finset.sum_le_sum fun k _ => hterm k
      _ = n * (δ * Cb) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < r ^ n := by
        rw [hδ]
        have hpos : 0 < (n + 1 : ℝ) * Cb := by positivity
        rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_mul_inv]
        rw [show (n : ℝ) * (r ^ n * Cb) * ((n + 1 : ℝ) * Cb)⁻¹ = r ^ n * (n / (n + 1)) by
          field_simp]
        have : (n : ℝ) / (n + 1) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        nlinarith [pow_pos hr0 n]
  -- a root of `g₀` close to `β`
  have hsplit : (g₀.map (algebraMap K Ω)).Splits := IsAlgClosed.splits _
  obtain ⟨γ, hγroot, hγβ⟩ : ∃ γ ∈ g₀.aroots Ω, ‖β - γ‖ < r := by
    by_contra hcon
    push Not at hcon
    have hprod := hsplit.aeval_eq_prod_aroots_of_monic hg₀m β
    have hcard : (g₀.aroots Ω).card = n := by
      rw [aroots, ← hsplit.natDegree_eq_card_roots, natDegree_map, hg₀deg]
    have hle : (⟨r, hr0.le⟩ : ℝ≥0) ^ ((g₀.aroots Ω).map (β - ·)).card ≤
        (((g₀.aroots Ω).map (β - ·)).map nnnormHom).prod := by
      rw [← Multiset.card_map nnnormHom]
      apply Multiset.pow_card_le_prod
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
      exact hcon z hz
    rw [← map_multiset_prod, ← hprod, Multiset.card_map, hcard] at hle
    have : r ^ n ≤ ‖aeval β g₀‖ := by
      have h3 : ((⟨r, hr0.le⟩ : ℝ≥0) ^ n : ℝ≥0) ≤ ‖aeval β g₀‖₊ := hle
      have h4 := NNReal.coe_le_coe.mpr h3
      convert h4 using 1
      · exact (NNReal.coe_pow (⟨r, hr0.le⟩ : ℝ≥0) n).symm
      · exact (coe_nnnorm _).symm
    linarith
  have hγ : aeval γ g₀ = 0 := by
    rw [mem_aroots] at hγroot
    exact hγroot.2
  -- Krasner's lemma
  have hγint : IsIntegral K̂ γ := Algebra.IsIntegral.isIntegral γ
  have hβγ : β ∈ K̂⟮γ⟯ := IsKrasner.krasner (by rw [hβh]; exact hhsep) (IsAlgClosed.splits _)
    hγint fun x hconj hne => by
      have hx : aeval x h = 0 := by
        rw [← hβh, show minpoly K̂ β = minpoly K̂ x from hconj]
        exact minpoly.aeval K̂ x
      exact hγβ.trans_le (hr x hx (Ne.symm hne))
  -- degrees
  have hβint : IsIntegral K̂ β := hβ'int.map ι
  have hfinβ : Module.finrank K̂ K̂⟮β⟯ = n := by
    rw [IntermediateField.adjoin.finrank hβint, hβh, hhdeg]
  have hγdvd : minpoly K̂ γ ∣ g₀.map (algebraMap K K̂) :=
    minpoly.dvd K̂ γ (by rw [aeval_map_algebraMap]; exact hγ)
  have hγdeg : (minpoly K̂ γ).natDegree ≤ n := by
    have := natDegree_le_of_dvd hγdvd ((hg₀m.map _).ne_zero)
    rwa [natDegree_map, hg₀deg] at this
  have : FiniteDimensional K̂ K̂⟮γ⟯ := IntermediateField.adjoin.finiteDimensional hγint
  have hle : K̂⟮β⟯ ≤ K̂⟮γ⟯ := (IntermediateField.adjoin_simple_le_iff).mpr hβγ
  have heq : K̂⟮β⟯ = K̂⟮γ⟯ := IntermediateField.eq_of_le_of_finrank_le hle (by
    rw [IntermediateField.adjoin.finrank hγint, hfinβ]
    exact hγdeg)
  have hγmem : γ ∈ ι.fieldRange := by
    have h1 : K̂⟮β⟯ ≤ ι.fieldRange :=
      (IntermediateField.adjoin_simple_le_iff).mpr ⟨β', rfl⟩
    exact h1 (heq ▸ IntermediateField.mem_adjoin_simple_self K̂ γ)
  obtain ⟨γ', hγ'⟩ := hγmem
  have hγ'' : ι γ' = γ := hγ'
  have hγdegeq : (minpoly K̂ γ).natDegree = n := by
    rw [← IntermediateField.adjoin.finrank hγint, ← heq, hfinβ]
  -- the field `L = K(γ')` inside `E`
  let _ : Algebra K E := ((algebraMap K̂ E).comp (algebraMap K K̂)).toAlgebra
  have : IsScalarTower K K̂ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hγ'root : aeval γ' g₀ = 0 := by
    apply ι.injective
    have h1 := aeval_algHom_apply (ι.restrictScalars K) γ' g₀
    change aeval (ι γ') g₀ = ι (aeval γ' g₀) at h1
    rw [hγ''] at h1
    rw [map_zero]
    exact h1.symm.trans hγ
  have hγ'int : IsIntegral K γ' := ⟨g₀, hg₀m, hγ'root⟩
  have hmin' : minpoly K̂ γ' = minpoly K̂ γ := by
    rw [← hγ'']
    exact (minpoly.algHom_eq ι ι.injective γ').symm
  have hdvdK : minpoly K̂ γ' ∣ (minpoly K γ').map (algebraMap K K̂) :=
    minpoly.dvd_map_of_isScalarTower K K̂ γ'
  have hKdeg : (minpoly K γ').natDegree = n := by
    apply le_antisymm
    · have := natDegree_le_of_dvd (minpoly.dvd K γ' hγ'root) hg₀m.ne_zero
      rwa [hg₀deg] at this
    · have := natDegree_le_of_dvd hdvdK ((minpoly.monic hγ'int).map _).ne_zero
      rwa [natDegree_map, hmin', hγdegeq] at this
  have hmapeq : (minpoly K γ').map (algebraMap K K̂) = minpoly K̂ γ' := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hγ'int.tower_top))
      ((minpoly.monic hγ'int).map _) hdvdK ?_
    rw [natDegree_map, hKdeg, hmin', hγdegeq]
  have hsepK : IsSeparable K γ' := by
    have h1 : (minpoly K̂ γ').Separable := Algebra.IsSeparable.isSeparable K̂ γ'
    rw [← hmapeq] at h1
    exact (Polynomial.separable_map (algebraMap K K̂)).mp h1
  have : FiniteDimensional K K⟮γ'⟯ := IntermediateField.adjoin.finiteDimensional hγ'int
  have : Algebra.IsSeparable K K⟮γ'⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K E).2 hsepK
  have hdim : Module.finrank K K⟮γ'⟯ = Module.finrank K̂ E := by
    rw [IntermediateField.adjoin.finrank hγ'int, hKdeg]
  exact ⟨K⟮γ'⟯, inferInstance, inferInstance, inferInstance, inferInstance,
    nonempty_algEquiv_of_algHom hsep (K⟮γ'⟯).val hdim⟩

end HenselianFiniteEtale

end Langlands.AlgebraicGeometry.PointTopology
