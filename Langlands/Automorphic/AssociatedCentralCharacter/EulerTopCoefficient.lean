import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # The top coefficient of an Euler polynomial

The coefficient of `X^n` in `det(1 - X A)` on an `n`-dimensional space is `(-1)^n det A`, and
the coefficient of `X^n` in `∏ (1 - z_i X)` over `n` nonzero numbers is `(-1)^n ∏ z_i`. So an
unramified match of a relative Weil representation of rank `n` with the Euler polynomial of
`n` eigenvalues identifies the determinant at the Frobenius image with their product.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uV

namespace Langlands.LocalFactor

/-- The coefficient of `X^n` in `det(1 - X A)`, for `A` on a space of dimension `n`, is
`(-1)^n det A`. -/
theorem eulerPolynomial_coeff_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    (eulerPolynomial A).coeff (Module.finrank ℂ V) =
      (-1) ^ Module.finrank ℂ V * LinearMap.det A := by
  rw [eulerPolynomial, coeff_reverse, A.charpoly_natDegree, revAt_le le_rfl, Nat.sub_self,
    LinearMap.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]

end Langlands.LocalFactor

namespace Langlands.Unramified.Eigenvalues

/-- The coefficient of `X^n` in `∏ (1 - z_i X)` is `(-1)^n ∏ z_i`. -/
theorem eulerPolynomial_coeff_rank {n : ℕ} (s : Eigenvalues n) :
    s.eulerPolynomial.coeff n = (-1) ^ n * (((s : Multiset ℂˣ).prod : ℂˣ) : ℂ) := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  rw [eulerPolynomial_ofTuple]
  have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (1 - C ((z i : ℂˣ) : ℂ) * X).natDegree ≤ 1 := by
    intro i _
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have h := coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun i : Fin n => 1 - C ((z i : ℂˣ) : ℂ) * X) 1 hdeg
  rw [Finset.card_univ, Fintype.card_fin, mul_one] at h
  rw [h]
  simp only [coeff_sub, coeff_one, coeff_C_mul_X, ite_true, one_ne_zero, ite_false, zero_sub]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  congr 1
  simp [ofTuple, List.prod_ofFn]

end Langlands.Unramified.Eigenvalues

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- If `S` has rank `n` and `det(1 - X S(ι Fr))` is the Euler polynomial `∏ (1 - z_i X)` of
`n` eigenvalues, then `det S(ι Fr) = ∏ z_i`. -/
theorem determinantCharacter_eq_prod_of_localEulerPolynomial {n : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) (hn : S.rank = n)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (s : Eigenvalues n) (h : localEulerPolynomial S ι = s.eulerPolynomial) :
    FiniteRepresentation.determinantCharacter S
        (ι (Weil.Local.localGeometricFrobenius (padicField v))) =
      (s : Multiset ℂˣ).prod := by
  subst hn
  apply Units.ext
  let g := ι (Weil.Local.localGeometricFrobenius (padicField v))
  have hA : (LocalFactor.eulerPolynomial (S.representation g)).coeff S.rank =
      (-1) ^ S.rank * LinearMap.det (S.representation g) :=
    LocalFactor.eulerPolynomial_coeff_finrank _
  have hc : (LocalFactor.eulerPolynomial (S.representation g)).coeff S.rank =
      s.eulerPolynomial.coeff S.rank :=
    congrArg (fun P : Polynomial ℂ => P.coeff S.rank) h
  rw [hA, Eigenvalues.eulerPolynomial_coeff_rank] at hc
  rw [FiniteRepresentation.determinantCharacter_apply]
  have h1 : ((-1 : ℂ) ^ S.rank) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h1 hc

/-- At a place where `S` of rank `n` matches the Euler polynomial of `n` eigenvalues, every
local relative Weil map `ι` gives `det S(ι Fr) = ∏ z_i`. -/
theorem IsUnramifiedMatchAt.determinantCharacter_eq_prod {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)} (hn : S.rank = n)
    {s : Eigenvalues n} (h : IsUnramifiedMatchAt S v s.eulerPolynomial)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap v w.1 e ι) :
    FiniteRepresentation.determinantCharacter S
        (ι (Weil.Local.localGeometricFrobenius (padicField v))) =
      (s : Multiset ℂˣ).prod :=
  determinantCharacter_eq_prod_of_localEulerPolynomial S hn ι s ((h w).2 e ι hι).2

end Langlands.ClassField.Global.RelativeWeilGroup
