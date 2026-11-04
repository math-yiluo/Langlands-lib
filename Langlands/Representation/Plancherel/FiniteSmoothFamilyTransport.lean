import Langlands.Representation.Plancherel.RationalOrbitBasisInvariance
import Langlands.Representation.Plancherel.SmoothTensorFamilies

/-! # Coordinate and coefficient changes of finite smooth families -/

noncomputable section

namespace Langlands.Plancherel

universe uJ uK uL uV uW

variable {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Finite scalar-smooth sums remain such sums after an integer monomial
change of parameters. -/
theorem mem_finiteSmoothFamilies_comp_monomial
    {F : (J → Circle) → V} (hF : F ∈ finiteSmoothFamilies J V)
    (a : J → K → ℤ) :
    F ∘ finiteTorusMonomial a ∈ finiteSmoothFamilies K V := by
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J V F).mp hF
  exact (mem_finiteSmoothFamilies_iff K V _).mpr
    ⟨n, fun i => ⟨(f i).val ∘ finiteTorusMonomial a, (f i).property.comp_monomial a⟩,
      v, fun z => hF (finiteTorusMonomial a z)⟩

variable {L : Type uL} [AddCommGroup L] [Module ℤ L]

/-- The existing reconstruction of a lattice character is a group
isomorphism of coordinate tori. -/
def finiteTorusBasisChangeMulEquiv (b : Module.Basis J ℤ L)
    (c : Module.Basis K ℤ L) : (J → Circle) ≃* (K → Circle) where
  toFun := finiteTorusBasisChange b c
  invFun := finiteTorusBasisChange c b
  left_inv := finiteTorusBasisChange_inverse b c
  right_inv := finiteTorusBasisChange_inverse c b
  map_mul' z w := by
    funext k
    simp only [finiteTorusBasisChange_eq_monomial, finiteTorusMonomial,
      Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

@[simp]
theorem finiteTorusBasisChangeMulEquiv_apply (b : Module.Basis J ℤ L)
    (c : Module.Basis K ℤ L) (z : J → Circle) :
    finiteTorusBasisChangeMulEquiv b c z = finiteTorusBasisChange b c z := rfl

@[simp]
theorem finiteTorusBasisChangeMulEquiv_symm_apply (b : Module.Basis J ℤ L)
    (c : Module.Basis K ℤ L) (z : K → Circle) :
    (finiteTorusBasisChangeMulEquiv b c).symm z = finiteTorusBasisChange c b z := rfl

/-- The finite-sum smoothness condition is independent of a finite integer
basis, without a topology or finite-dimensionality premise on the coefficients. -/
theorem mem_finiteSmoothFamilies_comp_basisChange_iff
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L)
    (F : (K → Circle) → V) :
    F ∘ finiteTorusBasisChange b c ∈ finiteSmoothFamilies J V ↔
      F ∈ finiteSmoothFamilies K V := by
  constructor
  · intro hF
    have hh := mem_finiteSmoothFamilies_comp_monomial hF (fun j k => c.repr (b j) k)
    rw [← finiteTorusBasisChange_eq_monomial c b] at hh
    simpa only [Function.comp_def, finiteTorusBasisChange_inverse] using hh
  · intro hF
    rw [finiteTorusBasisChange_eq_monomial]
    exact mem_finiteSmoothFamilies_comp_monomial hF _

/-- Translation of the parameter torus preserves finite scalar-smooth sums
in both directions. -/
theorem mem_finiteSmoothFamilies_mul_const_iff (F : (J → Circle) → V)
    (c : J → Circle) :
    (fun z => F (z * c)) ∈ finiteSmoothFamilies J V ↔
      F ∈ finiteSmoothFamilies J V := by
  have translate {H : (J → Circle) → V} (hH : H ∈ finiteSmoothFamilies J V)
      (d : J → Circle) :
      (fun z => H (z * d)) ∈ finiteSmoothFamilies J V := by
    obtain ⟨n, f, v, hH⟩ := (mem_finiteSmoothFamilies_iff J V H).mp hH
    exact (mem_finiteSmoothFamilies_iff J V _).mpr
      ⟨n, fun i => ⟨fun z => (f i).val (z * d),
        (isSmoothFiniteTorusFunction_mul_const_iff _ d).mpr (f i).property⟩,
        v, fun z => hH (z * d)⟩
  constructor
  · intro hF
    simpa only [inv_mul_cancel_right] using translate hF c⁻¹
  · exact fun hF => translate hF c

/-- A fixed linear map acts on the constant coefficient vectors of each
finite scalar-smooth expansion. -/
theorem mem_finiteSmoothFamilies_linearMap
    {F : (J → Circle) → V} (hF : F ∈ finiteSmoothFamilies J V)
    (T : V →ₗ[ℂ] W) :
    (fun z => T (F z)) ∈ finiteSmoothFamilies J W := by
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J V F).mp hF
  apply (mem_finiteSmoothFamilies_iff J W _).mpr
  refine ⟨n, f, fun i => T (v i), fun z => ?_⟩
  rw [hF z, map_sum]
  simp only [map_smul]

/-- Fixed coefficient equivalences preserve and reflect the actual
finite-sum smoothness condition. -/
theorem mem_finiteSmoothFamilies_linearEquiv_iff
    (F : (J → Circle) → V) (T : V ≃ₗ[ℂ] W) :
    (fun z => T (F z)) ∈ finiteSmoothFamilies J W ↔
      F ∈ finiteSmoothFamilies J V := by
  constructor
  · intro hF
    have hh := mem_finiteSmoothFamilies_linearMap hF T.symm.toLinearMap
    change (fun z => T.symm (T (F z))) ∈ finiteSmoothFamilies J V at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · exact fun hF => mem_finiteSmoothFamilies_linearMap hF T.toLinearMap

end Langlands.Plancherel
