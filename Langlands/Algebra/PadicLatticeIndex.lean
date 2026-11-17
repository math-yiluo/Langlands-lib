import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.NumberTheory.Padics.RingHoms

/-! # The index of the image of a `p`-adic endomorphism

For an endomorphism `φ` of a free module of finite rank over `ℤ_[p]` with nonzero determinant,
the number of elements of `M ⧸ range φ` has the same `p`-adic norm as `det φ`.
-/

noncomputable section

namespace Langlands.Algebra.PadicLattice

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_[p] ⧸ (a)` has `p ^ v(a)` elements, which has the same `p`-adic norm as `a`. -/
theorem norm_card_quotient_span (a : ℤ_[p]) (ha : a ≠ 0) :
    ‖((Nat.card (ℤ_[p] ⧸ Ideal.span {a}) : ℕ) : ℚ_[p])‖ = ‖(a : ℚ_[p])‖ := by
  have hspan : Ideal.span {a} = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have hcard : Nat.card (ℤ_[p] ⧸ Ideal.span {a}) = p ^ a.valuation := by
    rw [hspan, ← PadicInt.ker_toZModPow,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow a.valuation))).toEquiv, Nat.card_zmod]
  rw [hcard, PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_eq_zpow_neg_valuation ha]
  push_cast
  rw [norm_pow, Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]

/-- The index of the image of an endomorphism with nonzero determinant of a free module of
finite rank over `ℤ_[p]` has the `p`-adic norm of the determinant. -/
theorem norm_card_quotient_range {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] (φ : M →ₗ[ℤ_[p]] M)
    (hφ : LinearMap.det φ ≠ 0) :
    ‖((Nat.card (M ⧸ LinearMap.range φ) : ℕ) : ℚ_[p])‖ =
      ‖((LinearMap.det φ : ℤ_[p]) : ℚ_[p])‖ := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] M
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h : ⇑(b.repr (φ x)) = ⇑(b.repr (φ y)) := by rw [hxy]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ, ← LinearMap.toMatrix_mulVec_repr b b φ] at h
    have hdet : (LinearMap.toMatrix b b φ).det ≠ 0 := by rwa [LinearMap.det_toMatrix]
    have := Matrix.mulVec_injective_of_det_ne_zero hdet h
    exact b.repr.injective (Finsupp.ext fun i => congrFun this i)
  let N := LinearMap.range φ
  let e : M ≃ₗ[ℤ_[p]] N := LinearEquiv.ofInjective φ hinj
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M := e.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ_[p]] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ_[p]] M := N.subtype.comp (e' : M →ₗ[ℤ_[p]] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change (b'.equiv ab (Equiv.refl _) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (LinearMap.det φ) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have hdetf0 : LinearMap.det f ≠ 0 := fun h0 => hφ (hassoc.eq_zero_iff.mpr h0)
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hi
    apply hdetf0
    rw [hdetf]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hnorm_assoc : ‖((LinearMap.det φ : ℤ_[p]) : ℚ_[p])‖ =
      ‖((LinearMap.det f : ℤ_[p]) : ℚ_[p])‖ := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, PadicInt.coe_mul, norm_mul, PadicInt.padic_norm_e_of_padicInt (u : ℤ_[p]),
      PadicInt.isUnit_iff.mp u.isUnit, mul_one]
  rw [hnorm_assoc, hdetf,
    Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [Nat.cast_prod, show ((∏ i, a i : ℤ_[p]) : ℚ_[p]) = ∏ i, ((a i : ℤ_[p]) : ℚ_[p]) from
    map_prod PadicInt.Coe.ringHom a Finset.univ, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_card_quotient_span (a i) (ha0 i)

/-- For `N` at least the valuation of `det φ`, `p ^ N • m` lies in the image of `φ`. -/
theorem pow_smul_mem_range {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] (φ : M →ₗ[ℤ_[p]] M)
    (hφ : LinearMap.det φ ≠ 0) (N : ℕ) (hN : (LinearMap.det φ).valuation ≤ N) (m : M) :
    ((p : ℤ_[p]) ^ N) • m ∈ LinearMap.range φ := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] M
  let A := LinearMap.toMatrix b b φ
  let ψ : M →ₗ[ℤ_[p]] M := Matrix.toLin b b A.adjugate
  have hφψ : ∀ x, φ (ψ x) = LinearMap.det φ • x := by
    intro x
    have h : φ.comp ψ = Matrix.toLin b b (A * A.adjugate) := by
      rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix]
    have h2 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply] at h2
    rw [h2, Matrix.mul_adjugate, LinearMap.det_toMatrix, map_smul, Matrix.toLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hdet := PadicInt.unitCoeff_spec hφ
  set v := (LinearMap.det φ).valuation with hv
  set u := PadicInt.unitCoeff hφ
  have hpN : (p : ℤ_[p]) ^ N =
      LinearMap.det φ * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (N - v)) := by
    rw [hdet, mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hN]
  refine ⟨(((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (N - v)) • ψ m, ?_⟩
  rw [map_smul, hφψ, smul_smul, mul_comm, ← hpN]

/-- An injective endomorphism of a free module of finite rank over `ℤ_[p]` has nonzero
determinant. -/
theorem det_ne_zero_of_injective {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] (φ : M →ₗ[ℤ_[p]] M)
    (hφ : Function.Injective φ) : LinearMap.det φ ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis ℤ_[p] M
  have hdet : (LinearMap.toMatrix b b φ).det = 0 := by rwa [LinearMap.det_toMatrix]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let x : M := b.equivFun.symm v
  have hx0 : x ≠ 0 := by
    intro hx
    apply hv0
    have := congrArg b.equivFun hx
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  have hφx : φ x = 0 := by
    apply b.equivFun.injective
    rw [map_zero]
    have h := LinearMap.toMatrix_mulVec_repr b b φ x
    have hrx : ⇑(b.repr x) = v := by
      change b.equivFun x = v
      exact LinearEquiv.apply_symm_apply _ _
    rw [hrx, hv] at h
    funext i
    exact (congrFun h i).symm
  exact hx0 (hφ (hφx.trans (map_zero φ).symm))

end Langlands.Algebra.PadicLattice
