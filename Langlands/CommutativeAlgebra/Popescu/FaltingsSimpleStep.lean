import Langlands.MathlibBase

/-! # `H₁` and `Ω` of a simple extension `L = M(α)` with `α^p ∈ M` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open Polynomial

open scoped TensorProduct

/-- If `L = M(α)` with `α^p = c ∈ M`, `α ∉ M`, then `X^p - c` is the minimal polynomial of `α`. -/
theorem minpoly_eq_X_pow_sub_C {M L : Type*} [Field M] [Field L] [Algebra M L] (p : ℕ)
    [hp : Fact p.Prime] [CharP M p] (α : L) (hα : α ∉ Set.range (algebraMap M L)) (c : M)
    (hc : α ^ p = algebraMap M L c) : minpoly M α = X ^ p - C c := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap M L).injective p
  have hirr : Irreducible (X ^ p - C c : M[X]) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hα ⟨b, ?_⟩
    have h0 : (α - algebraMap M L b) ^ p = 0 := by
      rw [sub_pow_char, hc, ← map_pow, hb, sub_self]
    exact (sub_eq_zero.mp (pow_eq_zero_iff hp.out.ne_zero |>.mp h0)).symm
  have hmon : (X ^ p - C c : M[X]).Monic := monic_X_pow_sub_C c hp.out.ne_zero
  have haev : aeval α (X ^ p - C c : M[X]) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C, hc, sub_self]
  exact (minpoly.eq_of_irreducible_of_monic hirr haev hmon).symm

/-- The extension `M[X] → L`, `X ↦ α`, with underlying ring `M[X]`. -/
noncomputable abbrev simpleExtension {M L : Type u} [Field M] [Field L] [Algebra M L] (α : L)
    (hsurj : Function.Surjective (aeval α : M[X] →ₐ[M] L)) : Algebra.Extension M L :=
  @Algebra.Extension.mk M L _ _ _ M[X] _ _ (aeval α : M[X] →ₐ[M] L).toRingHom.toAlgebra
    (@IsScalarTower.of_algebraMap_eq' M M[X] L _ _ _ _
      (aeval α : M[X] →ₐ[M] L).toRingHom.toAlgebra _ (aeval α).comp_algebraMap.symm)
    (fun x => (hsurj x).choose) (fun x => (hsurj x).choose_spec)

/-- `H₁(L_{L/M})` is identified with `H₁` of the extension `M[X] → L`. -/
noncomputable def simpleExtensionH1Equiv {M L : Type u} [Field M] [Field L] [Algebra M L]
    (α : L) (hsurj : Function.Surjective (aeval α : M[X] →ₐ[M] L)) :
    (simpleExtension α hsurj).H1Cotangent ≃ₗ[L] Algebra.H1Cotangent M L := by
  let P := simpleExtension α hsurj
  let g : P.Hom (Algebra.Generators.self M L).toExtension := by
    refine Algebra.Extension.Hom.ofAlgHom (aeval (MvPolynomial.X α : MvPolynomial L M)) ?_
    apply Polynomial.algHom_ext
    exact (congrArg (IsScalarTower.toAlgHom M (Algebra.Generators.self M L).toExtension.Ring L)
      (aeval_X (MvPolynomial.X α : MvPolynomial L M))).trans
      (((Algebra.Generators.algebraMap_apply (P := Algebra.Generators.self M L) _).trans
        (MvPolynomial.aeval_X _ α)).trans (aeval_X α).symm)
  exact Algebra.Extension.H1Cotangent.equiv g (Algebra.Extension.defaultHom _ _ _)

/-- **Simple step.** If `L = M(α)` with `α^p = c ∈ M` and `α ∉ M`, then `H₁(L_{L/M})` and
`Ω_{L/M}` are both one-dimensional over `L`. -/
theorem rank_simple_step {M L : Type u} [Field M] [Field L] [Algebra M L] (p : ℕ)
    [hp : Fact p.Prime] [CharP M p] (α : L) (hgen : Algebra.adjoin M {α} = ⊤)
    (hα : α ∉ Set.range (algebraMap M L)) (c : M) (hc : α ^ p = algebraMap M L c) :
    Module.rank L (Algebra.H1Cotangent M L) = 1 ∧ Module.rank L Ω[L⁄M] = 1 := by
  classical
  have hsurj : Function.Surjective (aeval α : M[X] →ₐ[M] L) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, hgen]
  let _ : Algebra M[X] L := (aeval α : M[X] →ₐ[M] L).toRingHom.toAlgebra
  let P := simpleExtension α hsurj
  have hmin := minpoly_eq_X_pow_sub_C p α hα c hc
  have hker : P.ker = Ideal.span {(X ^ p - C c : M[X])} := by
    have : P.ker = RingHom.ker (aeval α : M[X] →ₐ[M] L) := rfl
    rw [this, minpoly.ker_aeval_eq_span_minpoly, hmin]
  have hfmem : (X ^ p - C c : M[X]) ∈ P.ker := hker ▸ Ideal.subset_span rfl
  have hspan : Submodule.span L {Algebra.Extension.Cotangent.mk (P := P) ⟨_, hfmem⟩} = ⊤ := by
    have := Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P)
      (fun _ : Unit => (X ^ p - C c : M[X])) (by rw [hker, Set.range_const])
    rw [eq_top_iff, ← this]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    rfl
  have hf0 : (X ^ p - C c : M[X]) ≠ 0 := (monic_X_pow_sub_C c hp.out.ne_zero).ne_zero
  have hne : Algebra.Extension.Cotangent.mk (P := P) ⟨_, hfmem⟩ ≠ 0 := by
    rw [Ne, Algebra.Extension.Cotangent.mk_eq_zero_iff]
    show ¬ (X ^ p - C c : M[X]) ∈ P.ker ^ 2
    rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have h1 : (X ^ p - C c : M[X]) * (X ^ p - C c) ∣ (X ^ p - C c) * 1 := by
      rw [mul_one, ← sq]
      exact h
    have hu := isUnit_of_dvd_one ((mul_dvd_mul_iff_left hf0).mp h1)
    have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_pow_sub_C] at this
    exact hp.out.ne_zero this
  have hD : KaehlerDifferential.D M M[X] (X ^ p - C c) = 0 := by
    rw [map_sub, Derivation.leibniz_pow, ← Polynomial.algebraMap_eq, Derivation.map_algebraMap,
      sub_zero, ← Nat.cast_smul_eq_nsmul M, CharP.cast_eq_zero, zero_smul]
  have hcc : P.cotangentComplex = 0 := by
    refine LinearMap.ext_on hspan ?_
    rintro _ rfl
    rw [Algebra.Extension.cotangentComplex_mk, LinearMap.zero_apply]
    show (1 : L) ⊗ₜ[M[X]] KaehlerDifferential.D M M[X] (X ^ p - C c) = 0
    rw [hD, TensorProduct.tmul_zero]
  have hrankCot : Module.rank L P.Cotangent = 1 := by
    rw [← rank_top, ← hspan, ← Module.finrank_eq_rank, finrank_span_singleton hne, Nat.cast_one]
  have hrankH1 : Module.rank L P.H1Cotangent = 1 := by
    show Module.rank L (LinearMap.ker P.cotangentComplex) = 1
    rw [hcc, LinearMap.ker_zero, rank_top, hrankCot]
  refine ⟨(simpleExtensionH1Equiv α hsurj).rank_eq.symm.trans hrankH1, ?_⟩
  -- `Ω_{L/M}` is the cotangent space `L ⊗ Ω_{M[X]/M}`
  have hinj : Function.Injective P.toKaehler := by
    rw [← LinearMap.ker_eq_bot, P.exact_cotangentComplex_toKaehler.linearMap_ker_eq, hcc,
      LinearMap.range_zero]
  let e := LinearEquiv.ofBijective P.toKaehler ⟨hinj, P.toKaehler_surjective⟩
  rw [← e.rank_eq]
  have : Module.Free M[X] Ω[M[X]⁄M] :=
    Module.Free.of_equiv (KaehlerDifferential.polynomialEquiv M).symm
  show Module.rank L (L ⊗[M[X]] Ω[M[X]⁄M]) = 1
  rw [Module.rank_baseChange, (KaehlerDifferential.polynomialEquiv M).rank_eq, Module.rank_self,
    Cardinal.lift_one]

end Faltings

end Langlands.CommutativeAlgebra.Popescu
