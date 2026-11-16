import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction
import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-! # Representative-free evaluation and integrability of the equal-rank Whittaker integrand

Auxiliary lemmas for the partial Euler factorization of the equal-rank global Whittaker
integral (Cogdell 2004, §2.3). See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualEulerIntegrand

local instance equalEulerIntegrandSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalEulerIntegrandSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- Left multiplication by `N_n(𝔸)` does not change the last row `e_n g`. -/
theorem lastRow_unipotent_mul {r : ℕ} (u : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    lastRow F r ((u : Points F (r + 1)) * g) = lastRow F r g := by
  have hu := Unfolding.isUnitriangular_of_mem_unipotentAdelic F u
  ext i j
  simp only [lastRow, Matrix.of_apply, map_mul, Units.val_mul]
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · rw [hu.2, one_mul]
  · intro k _ hk
    rw [show ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u : Points F (r + 1)) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) (Fin.last r) k = 0 from
        hu.1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable [CompactSpace (AdeleQuotient F)]

/-- The equal-rank Whittaker integrand of `W = W_x^ψ` and `W' = W_(x')^(ψ⁻¹)` at the class of
any `g` is `W(g) W'(g) Φ(e_n g) |det g|^s`: the two generic characters cancel. -/
theorem equalWhittakerIntegrand_mk {r : ℕ} (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (x : T.Space)
    (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) (g : Points F (r + 1)) :
    equalWhittakerIntegrand F (cuspWhittaker F T ψ x) (cuspWhittaker F T' ψ⁻¹ x') Φ s
        (LeftCosetSpace.mk (unipotentAdelic F (r + 1)) g) =
      cuspWhittaker F T ψ x g * cuspWhittaker F T' ψ⁻¹ x' g * Φ (lastRow F r g) *
        detPower F (r + 1) g s := by
  obtain ⟨u, hu⟩ := Unfolding.exists_out_mk_eq (unipotentAdelic F (r + 1)) g
  have hχ := Unfolding.genericCharacter_ne_zero F r ψ hψ (fun _ => 1) u
  simp only [equalWhittakerIntegrand]
  rw [hu, Unfolding.cuspWhittaker_mul_left F T ψ hψ, Unfolding.cuspWhittaker_mul_left F T' ψ⁻¹
    (Unfolding.isStandardAdditiveCharacter_inv F ψ hψ), lastRow_unipotent_mul,
    Unfolding.detPower_unipotent_mul, Unfolding.genericCharacter_inv_eq_inv,
    mul_mul_mul_comm, mul_inv_cancel₀ hχ, one_mul]

/-- Clause 1 of the equal-rank unfolding statement, specialized to the Whittaker side: the
equal-rank Whittaker integrand of `W = W_x^ψ` and `W' = W_(x')^(ψ⁻¹)` is integrable on a right
half-plane depending only on `T` and `T'`. -/
theorem exists_integrable_equalWhittakerIntegrand (hU : EqualUnfoldingStatement.{u})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r) :
    ∃ C : ℝ, ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
        Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
          Integrable
            (equalWhittakerIntegrand F (cuspWhittaker F T ψ x) (cuspWhittaker F T' ψ⁻¹ x') Φ s)
            (whittakerQuotientMeasure F (r + 1)) := by
  obtain ⟨ω, hω, -⟩ :=
    Automorphic.OperatorRealization.irreducibleCentralCharacter F (r + 1) T.realization
      T.irreducible
  obtain ⟨ω', hω', -⟩ :=
    Automorphic.OperatorRealization.irreducibleCentralCharacter F (r + 1) T'.realization
      T'.irreducible
  obtain ⟨C, -, hC⟩ := hU F r T T' ω ω' hω hω'
  exact ⟨C, fun ψ hψ x x' Φ hΦ s hs => ((hC ψ hψ x x' Φ hΦ).1 s hs).2.1⟩

/-- The integrability half-plane of `exists_integrable_equalWhittakerIntegrand` for a nontrivial
unitary character `ψ` of `𝔸` trivial on `F`, in the form used by
`EqualEulerFactorizationStatement`. -/
theorem exists_integrable_equalWhittakerIntegrand_unitary (hU : EqualUnfoldingStatement.{u})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r) :
    ∃ C : ℝ, ∀ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
        Integrable
          (equalWhittakerIntegrand F (cuspWhittaker F T ψ.complex x)
            (cuspWhittaker F T' ψ.complex⁻¹ x') Φ s)
          (whittakerQuotientMeasure F (r + 1)) := by
  obtain ⟨C, hC⟩ := exists_integrable_equalWhittakerIntegrand hU F r T T'
  exact ⟨C, hC ψ.complex (isStandardAdditiveCharacter_of_unitary ψ hψ)⟩

end Langlands.Global.RankinSelbergGlobal.EqualEulerIntegrand
