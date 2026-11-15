import Langlands.CommutativeAlgebra.Popescu.EnlargementTools

/-! # Differentials of a simple purely transcendental field extension -/

namespace Langlands.CommutativeAlgebra.Popescu

namespace Enlargement

open Polynomial KaehlerDifferential

/-- Let `F'/F` be a field extension generated (as a fraction field) by an element `T`
transcendental over `F`. A differential basis `dx_i` of `Ω_{F/k}` together with `dT` gives a
differential basis of `Ω_{F'/k}`. -/
theorem kaehler_basis_adjoin_transcendental {k F F' : Type*} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] (T : F')
    (hT : Transcendental F T)
    (hfrac : ∀ z : F', ∃ f g : F[X], z = aeval T f / aeval T g) {t : ℕ} (x : Fin t → F)
    (hli : LinearIndependent F (fun i => D k F (x i)))
    (hsp : Submodule.span F (Set.range fun i => D k F (x i)) = ⊤) :
    LinearIndependent F' (Sum.elim (fun i => D k F' (algebraMap F F' (x i)))
        (fun _ : Fin 1 => D k F' T)) ∧
      Submodule.span F' (Set.range (Sum.elim (fun i => D k F' (algebraMap F F' (x i)))
        (fun _ : Fin 1 => D k F' T))) = ⊤ := by
  classical
  -- `F'` is the fraction field of `F[X]` via `X ↦ T`
  let _ : Algebra F[X] F' := (aeval T : F[X] →ₐ[F] F').toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap F[X] F') := transcendental_iff_injective.mp hT
  have : FaithfulSMul F[X] F' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsScalarTower F F[X] F' := .of_algebraMap_eq fun c => by
    show algebraMap F F' c = aeval T (algebraMap F F[X] c)
    rw [Polynomial.algebraMap_eq, aeval_C]
  have : IsFractionRing F[X] F' := IsFractionRing.of_field F[X] F' fun z => by
    obtain ⟨f, g, h⟩ := hfrac z
    exact ⟨f, g, h⟩
  have : Algebra.FormallyEtale F[X] F' := .of_isLocalization (nonZeroDivisors F[X])
  have : Algebra.FormallySmooth F[X] F' := inferInstance
  have : Algebra.FormallySmooth F F' := .comp F F[X] F'
  -- `Ω_{F'/F}` is free on `dT`
  have hX : D F F[X] X = (polynomialEquiv F).symm 1 := by
    rw [LinearEquiv.eq_symm_apply, polynomialEquiv_D, derivative_X]
  let bX : Module.Basis (Fin 1) F[X] Ω[F[X]⁄F] :=
    (Module.Basis.singleton (Fin 1) F[X]).map (polynomialEquiv F).symm
  let bT : Module.Basis (Fin 1) F' Ω[F'⁄F] :=
    (bX.baseChange F').map (tensorKaehlerEquivOfFormallyEtale F F[X] F')
  have hbT : bT 0 = D F F' T := by
    simp only [bT, bX, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      Module.Basis.singleton_apply, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
      one_smul, ← hX, map_D]
    exact congrArg (D F F') (Polynomial.aeval_X T)
  have hDT0 : D F F' T ≠ 0 := by
    rw [← hbT]
    exact bT.ne_zero 0
  have hDTspan : ∀ ω : Ω[F'⁄F], ∃ c : F', ω = c • D F F' T := by
    intro ω
    refine ⟨bT.repr ω 0, ?_⟩
    rw [← hbT]
    conv_lhs => rw [← bT.sum_repr ω]
    simp
  -- the exact sequence `0 → F' ⊗ Ω_{F/k} → Ω_{F'/k} → Ω_{F'/F} → 0`
  have hmbinj : Function.Injective (mapBaseChange k F F') := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k F F' y).mp hy
    rw [Subsingleton.elim z 0, map_zero]
  have hexact := exact_mapBaseChange_map k F F'
  let bF := Module.Basis.mk hli hsp.ge
  let bF' := bF.baseChange F'
  have ha : ∀ i, mapBaseChange k F F' (bF' i) = D k F' (algebraMap F F' (x i)) := by
    intro i
    simp [bF', bF, Module.Basis.baseChange_apply, mapBaseChange_tmul]
  have hπa : ∀ i, map k F F' F' (D k F' (algebraMap F F' (x i))) = 0 := by
    intro i
    rw [← ha]
    exact hexact.apply_apply_eq_zero _
  have hπT : map k F F' F' (D k F' T) = D F F' T := by
    rw [map_D, Algebra.algebraMap_self_apply]
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg z
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one] at hg
    have h0 : g (Sum.inr 0) = 0 := by
      have := congrArg (map k F F' F') hg
      rw [map_add, map_sum, map_smul, hπT, map_zero] at this
      simp only [map_smul, hπa, smul_zero, Finset.sum_const_zero, zero_add] at this
      exact (smul_eq_zero.mp this).resolve_right hDT0
    rw [h0, zero_smul, add_zero] at hg
    have h1 : ∑ i, g (Sum.inl i) • bF' i = 0 := by
      apply hmbinj
      rw [map_sum, map_zero]
      simp only [map_smul, ha]
      exact hg
    have h2 := Fintype.linearIndependent_iff.mp bF'.linearIndependent _ h1
    rcases z with i | j
    · exact h2 i
    · rw [Subsingleton.elim j 0]
      exact h0
  · rw [eq_top_iff]
    intro ω _
    obtain ⟨c, hc⟩ := hDTspan (map k F F' F' ω)
    have hker : ω - c • D k F' T ∈ LinearMap.range (mapBaseChange k F F') := by
      rw [← hexact.linearMap_ker_eq, LinearMap.mem_ker, map_sub, map_smul, hπT, hc, sub_self]
    obtain ⟨y, hy⟩ := hker
    have hyspan : mapBaseChange k F F' y ∈ Submodule.span F' (Set.range (Sum.elim
        (fun i => D k F' (algebraMap F F' (x i))) (fun _ : Fin 1 => D k F' T))) := by
      rw [← bF'.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul, ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    have hT' : D k F' T ∈ Submodule.span F' (Set.range (Sum.elim
        (fun i => D k F' (algebraMap F F' (x i))) (fun _ : Fin 1 => D k F' T))) :=
      Submodule.subset_span ⟨Sum.inr 0, rfl⟩
    have : ω = mapBaseChange k F F' y + c • D k F' T := by rw [hy, sub_add_cancel]
    rw [this]
    exact add_mem hyspan (Submodule.smul_mem _ _ hT')

end Enlargement

end Langlands.CommutativeAlgebra.Popescu
