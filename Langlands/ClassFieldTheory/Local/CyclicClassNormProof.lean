import Langlands.ClassFieldTheory.Local.CyclicClassNormStatement
import Langlands.Cohomology.CyclicH2.Proof

noncomputable section
open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

private theorem sum_cyclicCarry_one {n : ℕ} [NeZero n] (hn : 1 < n) :
    ∑ i ∈ Finset.range n, cyclicCarry (i : ZMod n) 1 = 1 := by
  classical
  rw [Finset.sum_eq_single (n - 1)]
  · simp only [cyclicCarry, ZMod.val_natCast_of_lt (show n - 1 < n by omega),
      ZMod.val_one'' (by omega : n ≠ 1)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.div_self (NeZero.pos n)]
  · intro i hi hne
    simp only [Finset.mem_range] at hi
    simp only [cyclicCarry, ZMod.val_natCast_of_lt hi,
      ZMod.val_one'' (by omega : n ≠ 1)]
    exact Nat.div_eq_of_lt (by omega)
  · simp only [Finset.mem_range]
    omega

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem cyclicUnitCocycle_sum [Fintype Gal(L/K)]
    (n : ℕ) [NeZero n] (χ : Gal(L/K) ≃* Multiplicative (ZMod n))
    (σ : Gal(L/K)) (hχ : χ σ = Multiplicative.ofAdd (1 : ZMod n))
    (hn : 1 < n) (a : Kˣ) :
    ∑ i ∈ Finset.range (Fintype.card Gal(L/K)),
      cyclicUnitCocycle K L χ.toMonoidHom a (σ ^ i, σ) = baseUnit K L a := by
  have hcard : Fintype.card Gal(L/K) = n := by
    simpa using Fintype.card_congr χ.toEquiv
  rw [hcard]
  simp only [cyclicUnitCocycle, groupCohomology.cocycles₂.coe_mk,
    MulEquiv.coe_toMonoidHom, map_pow, hχ, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
    mul_one]
  rw [← Finset.sum_smul, sum_cyclicCarry_one hn, one_nsmul]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem cyclicClassNormNormalization : CyclicClassNormNormalization.{u,v} := by
  intro K L _ _ _ _ _ n _ χ σ hσ hχ a
  let : Fintype Gal(L/K) := Fintype.ofFinite _
  let : IsCyclic Gal(L/K) := ⟨σ, hσ⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A := unitsRepresentation K L
  let x : LinearMap.ker (Rep.applyAsHom A σ - 𝟙 A).hom.toLinearMap :=
    ⟨baseUnit K L a, by
      change A.ρ σ (baseUnit K L a) - baseUnit K L a = 0
      rw [baseUnit_fixed, sub_self]⟩
  have hcard : Fintype.card Gal(L/K) = n := by
    simpa using Fintype.card_congr χ.toEquiv
  by_cases hn : n = 1
  · have hval (z : ZMod n) : z.val = 0 := by
      have hz := ZMod.val_lt z
      omega
    have hc : cyclicUnitCocycle K L χ.toMonoidHom a = 0 := by
      ext g h
      change cyclicCarry _ _ • baseUnit K L a = 0
      simp [cyclicCarry, hval]
    have hclass : cyclicClass K L χ.toMonoidHom a = 0 := by
      rw [cyclicClass, hc, map_zero]
    rw [hclass, map_zero]
    apply (invariantsModNormEquiv K L).symm.injective
    change _ = (invariantsModNormEquiv K L).symm
      ((Langlands.LocalClassField.normQuotientProjection K L).toAdditive (Additive.ofMul a))
    rw [map_zero, invariantsModNormEquiv_symm_projection]
    symm
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨baseUnit K L a, ?_⟩
    apply Subtype.ext
    change A.ρ.norm (baseUnit K L a) = baseUnit K L a
    simp [Representation.norm, LinearMap.sum_apply, baseUnit_fixed, A, hcard, hn]
  · have hn' : 1 < n := by have := NeZero.pos n; omega
    have hc := Langlands.Cohomology.CyclicH2.cocycleSumComparison.{v}
      IntegerScalars Gal(L/K) A σ hσ
      (cyclicUnitCocycle K L χ.toMonoidHom a) x
      (cyclicUnitCocycle_sum K L n χ σ hχ hn' a).symm
    change invariantsModNormEquiv K L
      (cyclicH2InvariantsEquiv K L σ hσ
        (groupCohomology.H2π A (cyclicUnitCocycle K L χ.toMonoidHom a))) = _
    rw [hc]
    apply (invariantsModNormEquiv K L).symm.injective
    rw [AddEquiv.symm_apply_apply]
    change _ = (invariantsModNormEquiv K L).symm
      ((Langlands.LocalClassField.normQuotientProjection K L).toAdditive (Additive.ofMul a))
    rw [invariantsModNormEquiv_symm_projection]
    simp only [cyclicH2InvariantsEquiv, Rep.FiniteCyclicGroup.groupCohomologyπEven,
      LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, Iso.trans_hom,
      ModuleCat.comp_apply]
    dsimp only [A]
    simp only [← ConcreteCategory.comp_apply, Category.assoc,
      ShortComplex.moduleCatCyclesIso_inv_π_assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl

end Langlands.ClassFieldTheory.Local
