import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity

/-! # Separating two Laurent monomials on a nonzero principal open -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

section Torus

variable {Ix : Type v} [Fintype Ix]

/-- The exponent `e + m`, truncated to a natural number, as a monomial degree. -/
private def shiftedDegree (e : Ix → ℤ) (m : Ix → ℕ) : Ix →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i + m i).toNat

/-- A monomial in shifted degree evaluates to the Laurent monomial times the shift. -/
private theorem eval_monomial_shiftedDegree (e : Ix → ℤ) (m : Ix → ℕ)
    (he : ∀ i, 0 ≤ e i + m i) (z : Ix → ℂˣ) :
    MvPolynomial.eval (fun i => (z i : ℂ)) (MvPolynomial.monomial (shiftedDegree e m) 1) =
      ((∏ i, z i ^ e i : ℂˣ) : ℂ) * ((∏ i, z i ^ (m i : ℤ) : ℂˣ) : ℂ) := by
  rw [MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  rw [← Units.val_mul, ← Finset.prod_mul_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add, shiftedDegree, Finsupp.coe_equivFunOnFinite_symm,
    ← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg (he i)]

/-- Two distinct Laurent monomials on a complex torus are separated, up to any fixed
scalar `c`, on a nonzero polynomial principal open: the polynomial is
`X^(α + m) - c X^(β + m)` for a shift `m` clearing the negative exponents. -/
theorem exists_ne_zero_complexTorusPrincipalOpen_monomial_ne (α β : Ix → ℤ) (hαβ : α ≠ β)
    (c : ℂ) :
    ∃ p : MvPolynomial Ix ℂ, p ≠ 0 ∧ ∀ z ∈ complexTorusPrincipalOpen p,
      ((∏ i, z i ^ α i : ℂˣ) : ℂ) ≠ c * ((∏ i, z i ^ β i : ℂˣ) : ℂ) := by
  classical
  let m : Ix → ℕ := fun i => (α i).natAbs + (β i).natAbs
  have hα : ∀ i, 0 ≤ α i + m i := fun i => by
    simp only [m, Nat.cast_add]
    omega
  have hβ : ∀ i, 0 ≤ β i + m i := fun i => by
    simp only [m, Nat.cast_add]
    omega
  have hdeg : shiftedDegree α m ≠ shiftedDegree β m := by
    intro h
    apply hαβ
    funext i
    have hi := congrArg (fun d : Ix →₀ ℕ => (d i : ℤ)) h
    simp only [shiftedDegree, Finsupp.coe_equivFunOnFinite_symm,
      Int.toNat_of_nonneg (hα i), Int.toNat_of_nonneg (hβ i)] at hi
    omega
  refine ⟨MvPolynomial.monomial (shiftedDegree α m) 1 -
      MvPolynomial.C c * MvPolynomial.monomial (shiftedDegree β m) 1, ?_, ?_⟩
  · intro h0
    have h := congrArg (fun q : MvPolynomial Ix ℂ => q.coeff (shiftedDegree α m)) h0
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
      hdeg.symm, ↓reduceIte, mul_zero, sub_zero, AddMonoidAlgebra.coeff_zero] at h
    exact one_ne_zero h
  · intro z hz heq
    apply hz
    rw [map_sub, map_mul, MvPolynomial.eval_C, eval_monomial_shiftedDegree α m hα,
      eval_monomial_shiftedDegree β m hβ, heq]
    ring

end Torus

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Two actual rational points with distinct images in the valuation lattice are separated,
up to any fixed scalar `c`, by every unramified character on one nonzero principal open in the
published finite coordinates. -/
theorem exists_ne_zero_rationalUnramifiedPrincipalOpen_apply_ne
    (hG : GroupScheme.IsConnectedReductive G) (x y : GroupScheme.rationalPoints G)
    (hxy : rationalValuationImageProjection G x ≠ rationalValuationImageProjection G y)
    (c : ℂ) :
    letI : IsAffine G.X.left := by
      have := hG.isAffineHom
      exact isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∃ p : MvPolynomial (Fin (rationalImageRank G)) ℂ, p ≠ 0 ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen G hG p,
        ((χ.val x : ℂˣ) : ℂ) ≠ c * ((χ.val y : ℂˣ) : ℂ) := by
  let : IsAffine G.X.left := by
    have := hG.isAffineHom
    exact isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  set b := rationalReductiveValuationBasis G hG
  have hαβ : (⇑(b.repr (Additive.ofMul (rationalValuationImageProjection G x))) : _ → ℤ) ≠
      ⇑(b.repr (Additive.ofMul (rationalValuationImageProjection G y))) := by
    intro h
    exact hxy (Additive.ofMul.injective (b.repr.injective (DFunLike.coe_injective h)))
  obtain ⟨p, hp, hsep⟩ := exists_ne_zero_complexTorusPrincipalOpen_monomial_ne _ _ hαβ c
  refine ⟨p, hp, fun χ hχ => ?_⟩
  set e := rationalCanonicalUnramifiedCharacterCoordinates G hG
  have hx := rationalCanonicalUnramifiedCharacterCoordinates_symm_apply G hG (e χ) x
  have hy := rationalCanonicalUnramifiedCharacterCoordinates_symm_apply G hG (e χ) y
  rw [e.symm_apply_apply] at hx hy
  rw [hx, hy]
  exact hsep (e χ) hχ

end Rational

end Langlands.Plancherel
