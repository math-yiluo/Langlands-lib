import Langlands.Representation.Plancherel.LaurentBlockInvariants
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Polynomial presentations for zero or one Laurent coordinate -/

noncomputable section

open scoped nonZeroDivisors

namespace Langlands.Plancherel.LaurentBlockInvariants

open AddMonoidAlgebra

variable {n : ℕ}

/-- The inclusion of the univariate polynomial algebra by the first Laurent
coordinate in a product with a one-dimensional first block. -/
def firstPolynomialMap :
    Polynomial ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ)) :=
  Polynomial.aeval (single (Pi.single (0 : Fin 1) 1, 0) 1)

private def oneVariableLaurentEquiv :
    LaurentPolynomial ℂ ≃ₐ[ℂ] AddMonoidAlgebra ℂ (Fin 1 → ℤ) :=
  AddMonoidAlgebra.domCongr ℂ ℂ (AddEquiv.piUnique (fun _ : Fin 1 => ℤ)).symm

private theorem firstPolynomialMap_apply (p : Polynomial ℂ) :
    firstPolynomialMap (n := n) p =
      firstBlock (oneVariableLaurentEquiv (Polynomial.toLaurent p)) := by
  have he : firstPolynomialMap (n := n) =
      firstBlock.comp (oneVariableLaurentEquiv.toAlgHom.comp Polynomial.toLaurentAlg) := by
    apply Polynomial.algHom_ext
    simp only [firstPolynomialMap, Polynomial.aeval_X, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, Polynomial.coe_toLaurentAlg, Polynomial.toLaurent_X,
      LaurentPolynomial.T, oneVariableLaurentEquiv, AddMonoidAlgebra.domCongr_single,
      firstBlock_single]
    congr 1
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  exact DFunLike.congr_fun he p

/-- A fraction supported on the first block of rank one admits coprime
polynomial numerator and denominator in that first coordinate. -/
theorem exists_coprime_firstPolynomial_fraction
    (p q : AddMonoidAlgebra ℂ (Fin 1 → ℤ))
    (f : FractionRing (AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ))))
    (hf : f = algebraMap _ _ (firstBlock (n := n) p) /
      algebraMap _ _ (firstBlock (n := n) q)) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ IsCoprime P Q ∧
      f = algebraMap _ _ (firstPolynomialMap (n := n) P) /
        algebraMap _ _ (firstPolynomialMap (n := n) Q) := by
  let ι := algebraMap (AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ)))
    (FractionRing (AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ))))
  let l : LaurentPolynomial ℂ →+* _ :=
    ι.comp (firstBlock.comp oneVariableLaurentEquiv.toAlgHom).toRingHom
  have hl : Function.Injective l := by
    change Function.Injective (ι ∘ firstBlock (n := n) ∘ oneVariableLaurentEquiv)
    exact (IsFractionRing.injective _ _).comp
      ((firstBlock_injective (n := n)).comp oneVariableLaurentEquiv.injective)
  let φ := l.comp Polynomial.toLaurent
  have hφ : (Polynomial ℂ)⁰ ≤ (FractionRing
      (AddMonoidAlgebra ℂ ((Fin 1 → ℤ) × (Fin n → ℤ))))⁰.comap φ := by
    intro a ha
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff φ (hl.comp Polynomial.toLaurent_injective)).mpr
        (nonZeroDivisors.ne_zero ha))
  obtain ⟨i, P, hP⟩ := LaurentPolynomial.exists_T_pow (oneVariableLaurentEquiv.symm p)
  obtain ⟨j, Q, hQ⟩ := LaurentPolynomial.exists_T_pow (oneVariableLaurentEquiv.symm q)
  let t : RatFunc ℂ :=
    algebraMap _ _ (P * Polynomial.X ^ j) / algebraMap _ _ (Q * Polynomial.X ^ i)
  have ht : f = RatFunc.liftRingHom φ hφ t := by
    dsimp only [t]
    rw [RatFunc.liftRingHom_apply_div]
    change f = l (Polynomial.toLaurent (P * Polynomial.X ^ j)) /
      l (Polynomial.toLaurent (Q * Polynomial.X ^ i))
    simp only [map_mul Polynomial.toLaurent, Polynomial.toLaurent_X_pow, hP, hQ,
      mul_assoc, ← LaurentPolynomial.T_add, Int.add_comm (j : ℤ) i]
    rw [map_mul l, map_mul l, mul_div_mul_right _ _
      ((LaurentPolynomial.isUnit_T ((i : ℤ) + j)).map l).ne_zero]
    simpa only [l, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hf
  refine ⟨t.num, t.denom, RatFunc.denom_ne_zero t, RatFunc.isCoprime_num_denom t, ?_⟩
  rw [ht, RatFunc.liftRingHom_apply]
  simp only [φ, l, ι, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, firstPolynomialMap_apply]

/-- A fraction supported on the first block of rank zero is constant. -/
theorem exists_constant_of_firstBlock_fraction
    (p q : AddMonoidAlgebra ℂ (Fin 0 → ℤ))
    (f : FractionRing (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ))))
    (hf : f = algebraMap _ _ (firstBlock (n := n) p) /
      algebraMap _ _ (firstBlock (n := n) q)) :
    ∃ c : ℂ, f = algebraMap _ _ (algebraMap ℂ
      (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ))) c) := by
  let e := AddMonoidAlgebra.uniqueRingEquiv (R := ℂ) (Fin 0 → ℤ)
  have he (w : AddMonoidAlgebra ℂ (Fin 0 → ℤ)) :
      firstBlock (n := n) w =
        algebraMap ℂ (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ))) (e w) := by
    conv_lhs => rw [← e.symm_apply_apply w]
    simp only [e, AddMonoidAlgebra.uniqueRingEquiv_symm_apply, firstBlock_single]
    rfl
  refine ⟨e p / e q, ?_⟩
  rw [hf, he, he]
  exact (map_div₀ ((algebraMap
    (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ)))
    (FractionRing (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ))))).comp
      (algebraMap ℂ (AddMonoidAlgebra ℂ ((Fin 0 → ℤ) × (Fin n → ℤ))))) _ _).symm

end Langlands.Plancherel.LaurentBlockInvariants
