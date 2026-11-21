import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.ExtensionInvariants
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalFactor.Abelian.Padic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! # Rank-one unramified factors under cyclic norm pullback -/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField
open LocalFactor.PadicAbelian (lPolynomial)

universe u v

private theorem prod_rootsOfUnity_eulerLinear (m : ℕ) [NeZero m] (a : ℂ) :
    letI := Fintype.ofFinite (rootsOfUnity m ℂ)
    ∏ ζ : rootsOfUnity m ℂ, (1 - C (a * ((ζ : ℂˣ) : ℂ)) * X) =
      1 - C (a ^ m) * X ^ m := by
  classical
  let := Fintype.ofFinite (rootsOfUnity m ℂ)
  have hm : 0 < m := NeZero.pos m
  let R := nthRootsFinset m (1 : ℂ)
  let e : rootsOfUnity m ℂ ≃ R :=
    (rootsOfUnityEquivNthRoots ℂ m).trans
      (Equiv.subtypeEquivRight fun x =>
        (mem_nthRoots hm).trans (mem_nthRootsFinset hm (1 : ℂ)).symm)
  have he (ζ : rootsOfUnity m ℂ) : ((e ζ : R) : ℂ) = ((ζ : ℂˣ) : ℂ) := rfl
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  have hfact := X_pow_sub_one_eq_prod hm hζ
  change (X : ℂ[X]) ^ m - 1 = ∏ b ∈ R, (X - C b) at hfact
  have hcard : R.card = m := hζ.card_nthRootsFinset
  calc
    _ = ∏ b : R, (1 - C (a * b.val) * X) :=
      Fintype.prod_equiv e _ _ (fun ζ => by rw [he])
    _ = _ := by
      rw [Finset.prod_coe_sort R (fun b => 1 - C (a * b) * X)]
      apply Polynomial.funext
      intro x
      simp only [eval_prod, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one,
        ← mul_pow]
      let t := a * x
      have hprod (b : ℂ) : 1 - (a * b) * x = 1 - b * t := by dsimp [t]; ring
      simp_rw [hprod]
      change ∏ b ∈ R, (1 - b * t) = 1 - t ^ m
      by_cases ht : t = 0
      · simp [ht, zero_pow hm.ne']
      · have h := congrArg (Polynomial.eval t⁻¹) hfact
        simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one, eval_C] at h
        calc
          _ = ∏ b ∈ R, t * (t⁻¹ - b) := by
            apply Finset.prod_congr rfl
            intro b _
            rw [mul_sub, mul_inv_cancel₀ ht, mul_comm t b]
          _ = t ^ m * ((t⁻¹) ^ m - 1) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, ← h]
          _ = _ := by
            rw [mul_sub, ← mul_pow, mul_inv_cancel₀ ht, one_pow, mul_one]

section NormOrder

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- The order of the determinant norm is the upper order times the residue degree. -/
theorem ord_localNorm_eq_residueDegree_mul {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f)
    (x : E.Carrierˣ) :
    T.ord (localNorm T S x : F.Carrier) = (f : ℤ) * S.ord (x : E.Carrier) := by
  have hq : S.residueCardinality = T.residueCardinality ^ f := hf
  rw [S.residueCardinality_eq_pow, T.residueCardinality_eq_pow, ← pow_mul] at hq
  have hdeg := Nat.pow_right_injective (Fact.out : p.Prime).one_lt hq
  have h := residueDegree_mul_ord_relative_norm F E T S (x : E.Carrier)
  rw [hdeg, Nat.cast_mul, mul_assoc] at h
  exact mul_left_cancel₀ (show (T.residueDegree : ℤ) ≠ 0 by
    exact_mod_cast T.residueDegree_pos.ne') h

/-- The unramified character of a given uniformizer value is norm-trivial
precisely when that value is a root of unity of order dividing the residue degree. -/
theorem isNormTrivial_unramifiedCharacter_iff {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f)
    (a : ℂˣ) :
    IsNormTrivial E.Carrier (T.unramifiedCharacter a) ↔ a ^ f = 1 := by
  change (∀ x : E.Carrierˣ, T.unramifiedCharacter a (localNorm T S x) = 1) ↔ _
  simp only [T.unramifiedCharacter_apply, ord_localNorm_eq_residueDegree_mul T S hf,
    zpow_mul, zpow_natCast]
  constructor
  · intro h
    simpa only [S.uniformizerUnit_val, S.ord_uniformizer, zpow_one] using h S.uniformizerUnit
  · intro h x
    simp only [h, one_zpow]

end NormOrder

section Euler

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

private theorem unramifiedQuasicharacter_iff {K : PadicField p} (U : K.TopologicalData) :
    letI := U.topology
    ∀ (χ : Quasicharacter K.Carrier),
      U.multiplicativeConductor χ = 0 ↔ U.IsUnramifiedCharacter χ.toMonoidHom := by
  let := U.topology
  intro χ
  rw [U.multiplicativeConductor_eq_zero_iff, PadicField.TopologicalData.IsUnramifiedCharacter,
    ← U.ker_ordUnits]
  constructor
  · intro h a ha
    change U.ord (a : K.Carrier) = 0 at ha
    exact h a ((U.normalizedAbs_eq_one_iff_discreteValuation _).mp
      ((U.ord_eq_zero_iff_normalizedAbs a).mp ha))
  · intro h a ha
    apply h
    change U.ord (a : K.Carrier) = 0
    exact (U.ord_eq_zero_iff_normalizedAbs a).mpr
      ((U.normalizedAbs_eq_one_iff_discreteValuation _).mpr ha)

private theorem unramifiedCharacter_mul_iff {K : PadicField p} (U : K.TopologicalData)
    {χ κ : K.Carrierˣ →* ℂˣ} (hχ : U.IsUnramifiedCharacter χ) :
    U.IsUnramifiedCharacter (κ * χ) ↔ U.IsUnramifiedCharacter κ := by
  constructor
  · intro h a ha
    change κ a = 1
    have h1 : (κ * χ) a = 1 := h ha
    have h2 : χ a = 1 := hχ ha
    simpa only [MonoidHom.mul_apply, h2, mul_one] using h1
  · intro h a ha
    change κ a * χ a = 1
    have h1 : κ a = 1 := h ha
    have h2 : χ a = 1 := hχ ha
    rw [h1, h2, mul_one]

/-- The product of the actual rank-one Euler denominators of the norm-trivial
twists of an unramified character equals that of its norm pullback, with the
residue-degree substitution. Ramified twists contribute the factor one. -/
theorem prod_lPolynomial_unramifiedNormTwists {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f) :
    letI := T.topology
    letI := S.topology
    ∀ (χ : Quasicharacter F.Carrier), T.IsUnramifiedCharacter χ.toMonoidHom →
    ∀ (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (ξ : A → Quasicharacter F.Carrier),
    (∀ κ, (ξ κ).toMonoidHom = κ.val * χ.toMonoidHom) →
    (∏ κ : A, lPolynomial T (ξ κ)) =
      expand ℂ f (lPolynomial S (χ.comp (localNorm T S))) := by
  classical
  let := T.topology
  let := S.topology
  intro χ hχ A hA ξ hξ
  have hq : S.residueCardinality = T.residueCardinality ^ f := hf
  have hf₀ : f ≠ 0 := fun h => S.residueCardinality_gt_one.ne' (by simpa [h] using hq)
  let : NeZero f := ⟨hf₀⟩
  let := Fintype.ofFinite (rootsOfUnity f ℂ)
  let U := (Finset.univ : Finset A).filter (fun κ => T.IsUnramifiedCharacter κ.val)
  let e : U ≃ rootsOfUnity f ℂ := {
    toFun := fun κ => ⟨κ.val.val T.uniformizerUnit,
      (isNormTrivial_unramifiedCharacter_iff T S hf _).mp
        ((T.eq_unramifiedCharacter κ.val.val (Finset.mem_filter.mp κ.property).2) ▸
          (hA κ.val.val).mp κ.val.property)⟩
    invFun := fun z => ⟨⟨T.unramifiedCharacter z.val,
      (hA _).mpr ((isNormTrivial_unramifiedCharacter_iff T S hf _).mpr z.property)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.isUnramifiedCharacter z.val⟩⟩
    left_inv := fun κ => Subtype.ext (Subtype.ext
      (T.eq_unramifiedCharacter κ.val.val (Finset.mem_filter.mp κ.property).2).symm)
    right_inv := fun z => Subtype.ext (T.unramifiedCharacter_uniformizer z.val) }
  let a := χ T.uniformizerUnit
  let linear := fun κ : A => 1 - C ((a * κ.val T.uniformizerUnit : ℂˣ) : ℂ) * X
  have hcond (κ : A) : T.multiplicativeConductor (ξ κ) = 0 ↔ T.IsUnramifiedCharacter κ.val := by
    rw [unramifiedQuasicharacter_iff, hξ κ]
    exact unramifiedCharacter_mul_iff T hχ
  have hpoly (κ : A) : lPolynomial T (ξ κ) =
      if T.IsUnramifiedCharacter κ.val then linear κ else 1 := by
    rw [lPolynomial]
    split_ifs with hcond0 hu hu
    · have h := DFunLike.congr_fun (hξ κ) T.uniformizerUnit
      change ξ κ T.uniformizerUnit = κ.val T.uniformizerUnit * a at h
      rw [h, mul_comm (κ.val T.uniformizerUnit) a]
    · exact (hu ((hcond κ).mp hcond0)).elim
    · exact (hcond0 ((hcond κ).mpr hu)).elim
    · rfl
  have hupper : (χ.comp (localNorm T S)).toMonoidHom = S.unramifiedCharacter (a ^ f) := by
    ext x : 1
    change χ (localNorm T S x) = S.unramifiedCharacter (a ^ f) x
    have h := DFunLike.congr_fun (T.eq_unramifiedCharacter χ.toMonoidHom hχ) (localNorm T S x)
    change χ (localNorm T S x) = T.unramifiedCharacter a (localNorm T S x) at h
    rw [h, T.unramifiedCharacter_apply, S.unramifiedCharacter_apply,
      ord_localNorm_eq_residueDegree_mul T S hf, zpow_mul, zpow_natCast]
  have hupper0 : S.multiplicativeConductor (χ.comp (localNorm T S)) = 0 :=
    (unramifiedQuasicharacter_iff S _).mpr (hupper ▸ S.isUnramifiedCharacter (a ^ f))
  have hvalue : (χ.comp (localNorm T S)) S.uniformizerUnit = a ^ f :=
    (DFunLike.congr_fun hupper S.uniformizerUnit).trans (S.unramifiedCharacter_uniformizer _)
  calc
    _ = ∏ κ : U, linear κ.val := by simp_rw [hpoly, Finset.prod_coe_sort, U, Finset.prod_filter]
    _ = ∏ ζ : rootsOfUnity f ℂ, (1 - C ((a : ℂ) * ((ζ.val : ℂˣ) : ℂ)) * X) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [prod_rootsOfUnity_eulerLinear, lPolynomial, ite_eq_left hupper0, hvalue]
      simp [expand_X, expand_C]

end Euler

end Langlands.BaseChange
