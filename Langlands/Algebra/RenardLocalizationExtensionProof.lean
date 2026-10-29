import Langlands.Algebra.RenardLocalizationExtensionStatements

/-! # Inverse-power extension converse for the actual localization -/

set_option autoImplicit false

universe u v x w

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization

section Comparison

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {M : Type x} [AddCommGroup M] [Module R M]

/-- The published factor map into an extension with an actual automorphism. -/
def extensionFactor (a : Module.End R V) (β : M ≃ₗ[R] M) (j : V →ₗ[R] M)
    (hj : ∀ z, j (a z) = β (j z)) : Localized a →ₗ[R] M :=
  factor a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj

/-- The factor map sends a fraction to the corresponding inverse iterate in the extension. -/
theorem extensionFactor_frac (a : Module.End R V) (β : M ≃ₗ[R] M) (j : V →ₗ[R] M)
    (hj : ∀ z, j (a z) = β (j z)) (v : V) (n : ℕ) :
    extensionFactor a β j hj (frac a v n) = (β.symm.toLinearMap ^ n) (j v) := by
  induction n with
  | zero =>
    change extensionFactor a β j hj (frac a v 0) = j v
    rw [frac_zero]
    exact LinearMap.congr_fun
      (factor_comp_iota a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj) v
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih]
    apply β.injective
    rw [LinearEquiv.coe_coe, β.apply_symm_apply]
    have h := factor_intertwines a β.toLinearMap
      ((Module.End.isUnit_iff _).mpr β.bijective) j hj (frac a v (n + 1))
    change extensionFactor a β j hj (localizedEnd a (frac a v (n + 1))) =
      β (extensionFactor a β j hj (frac a v (n + 1))) at h
    rw [localizedEnd_frac_succ] at h
    exact h.symm

/-- Injectivity of the embedded source makes the factor map injective. -/
theorem extensionFactor_injective (a : Module.End R V) (β : M ≃ₗ[R] M)
    (j : V →ₗ[R] M) (hj : ∀ z, j (a z) = β (j z)) (hjinj : Function.Injective j) :
    Function.Injective (extensionFactor a β j hj) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨v, n, rfl⟩ := frac_surjective a z
  rw [extensionFactor_frac] at hz
  have hpow : Function.Injective (β.symm.toLinearMap ^ n) := by
    rw [Module.End.coe_pow]
    exact β.symm.injective.iterate n
  have hjv : j v = 0 := hpow (hz.trans (map_zero _).symm)
  have hv : v = 0 := hjinj (hjv.trans (map_zero j).symm)
  rw [hv, frac_eq_localizedInv_pow, map_zero, map_zero]

/-- The literal inverse-power exhaustion makes the factor map surjective. -/
theorem extensionFactor_surjective (a : Module.End R V) (β : M ≃ₗ[R] M)
    (j : V →ₗ[R] M) (hj : ∀ z, j (a z) = β (j z))
    (hexhaust : (Set.univ : Set M) =
      ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j)) :
    Function.Surjective (extensionFactor a β j hj) := by
  intro m
  have hm : m ∈ ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j) := by
    rw [← hexhaust]
    exact Set.mem_univ m
  obtain ⟨n, v, hv⟩ := Set.mem_iUnion.mp hm
  exact ⟨frac a v n, (extensionFactor_frac a β j hj v n).trans hv⟩

end Comparison

/-- Unique comparison of an inverse-power extension with the actual localization. -/
theorem extensionComparison : ExtensionComparisonStatement.{u, v, x} := by
  intro R _ V _ _ a M _ _ β j hjinj hj hexhaust
  let e : Localized a ≃ₗ[R] M :=
    LinearEquiv.ofBijective (extensionFactor a β j hj)
      ⟨extensionFactor_injective a β j hj hjinj,
        extensionFactor_surjective a β j hj hexhaust⟩
  have he : e.toLinearMap.comp (iota a) = j ∧
      ∀ z, e (localizedEnd a z) = β (e z) :=
    ⟨factor_comp_iota a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj,
      factor_intertwines a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj⟩
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hmaps : e'.toLinearMap = e.toLinearMap :=
    eq_of_intertwines a β.toLinearMap β.injective e'.toLinearMap e.toLinearMap
      he'.2 he.2 (he'.1.trans he.1.symm)
  exact LinearEquiv.toLinearMap_injective hmaps

/-- The comparison transports the universal property to the extension, with an independent
target universe. -/
theorem extensionConverse : ExtensionConverseStatement.{u, v, x, w} := by
  intro R _ V _ _ a M _ _ β j hjinj hj hexhaust
  obtain ⟨e, he, _⟩ := extensionComparison R V a M β j hjinj hj hexhaust
  have hinv : ∀ m, e.symm (β m) = localizedEnd a (e.symm m) := by
    intro m
    apply e.injective
    rw [e.apply_symm_apply, he.2, e.apply_symm_apply]
  intro W _ _ b hb f hf
  let g : M →ₗ[R] W := (factor a b hb f hf).comp e.symm.toLinearMap
  have hg : (∀ m, g (β m) = b (g m)) ∧ g.comp j = f := by
    constructor
    · intro m
      change factor a b hb f hf (e.symm (β m)) =
        b (factor a b hb f hf (e.symm m))
      rw [hinv, factor_intertwines]
    · ext v
      change factor a b hb f hf (e.symm (j v)) = f v
      have hi : e (iota a v) = j v := LinearMap.congr_fun he.1 v
      rw [← hi, e.symm_apply_apply]
      exact LinearMap.congr_fun (factor_comp_iota a b hb f hf) v
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  have hpre : g'.comp e.toLinearMap = factor a b hb f hf := by
    apply factor_unique a b hb f hf
    · intro z
      change g' (e (localizedEnd a z)) = b (g' (e z))
      rw [he.2]
      exact hg'.1 (e z)
    · rw [LinearMap.comp_assoc, he.1, hg'.2]
  ext m
  calc
    g' m = (g'.comp e.toLinearMap) (e.symm m) := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply]
    _ = factor a b hb f hf (e.symm m) := LinearMap.congr_fun hpre (e.symm m)
    _ = g m := rfl

/-- The field case specializes the two commutative-ring results. -/
theorem fieldExtension : FieldExtensionStatement.{u, v, x, w} := by
  intro k _ V _ _ a M _ _ β j hjinj hj hexhaust
  exact ⟨extensionConverse k V a M β j hjinj hj hexhaust,
    extensionComparison k V a M β j hjinj hj hexhaust⟩

/-- The exact closed published aggregate, with four independent universes. -/
theorem localizationExtensionStatements : LocalizationExtensionStatements.{u, v, x, w} :=
  ⟨extensionConverse, extensionComparison, fieldExtension⟩

end Langlands.Renard.EndomorphismLocalization
