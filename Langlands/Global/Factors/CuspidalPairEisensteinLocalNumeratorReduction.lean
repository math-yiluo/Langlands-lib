import Langlands.Global.Factors.CuspidalPairEisensteinLocalNumeratorStatement
import Langlands.Global.Factors.CuspidalPairEisensteinUnramifiedFactorizationStatement
import Langlands.Global.Factors.CuspidalPairEisensteinSemilocalNumeratorStatement
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellConvergenceStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof

/-! # The local numerator from the unramified factorization and the semilocal numerator

`CuspidalPairEisensteinLocalNumeratorStatement` follows from the absolute convergence of the
open-cell integral (`CuspidalPairEisensteinOpenCellConvergenceStatement`), its unramified
factorization (`CuspidalPairEisensteinUnramifiedFactorizationStatement`) and the semilocal
numerator (`CuspidalPairEisensteinSemilocalNumeratorStatement`): the partial open-cell
integral over the matrices integral outside `S₀` is the numerator. See the paired
Markdown. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairEisenstein

namespace CuspidalPairEisensteinLocalNumerator

variable {F : Type u} [Field F] [NumberField F]

/-- A standard additive character of `𝔸` as a unitary additive character. -/
def unitaryCharacter (ψ : AddChar (Adeles F) ℂ)
    (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ) :
    HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψ.2.2.2 x)⟩
  map_zero_eq_one' := by
    apply Subtype.ext
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' x y := by
    apply Subtype.ext
    exact AddChar.map_add_eq_mul ψ x y
  continuous_toFun := hψ.1.subtype_mk _
  nontrivial h := hψ.2.1 (by
    ext x
    exact congrArg (fun χ : AddChar (Adeles F) Circle => (χ x : ℂ)) h)

@[simp]
theorem unitaryCharacter_complex (ψ : AddChar (Adeles F) ℂ)
    (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ) :
    (unitaryCharacter ψ hψ).complex = ψ :=
  AddChar.ext _ _ fun _ => rfl

theorem unitaryCharacter_diagonal (ψ : AddChar (Adeles F) ℂ)
    (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ) (x : F) :
    unitaryCharacter ψ hψ (algebraMap F (Adeles F) x) = 1 :=
  Subtype.ext (hψ.2.2.1 x)

end CuspidalPairEisensteinLocalNumerator

open CuspidalPairEisensteinLocalNumerator

/-- The absolute convergence of the open-cell integral, its unramified factorization and the
semilocal numerator imply the local numerator of the open-cell integral. -/
def CuspidalPairEisensteinLocalNumeratorReductionStatement : Prop :=
  CuspidalPairEisensteinOpenCellConvergenceStatement.{u} →
    CuspidalPairEisensteinUnramifiedFactorizationStatement.{u, uQ} →
      CuspidalPairEisensteinSemilocalNumeratorStatement.{u} →
        CuspidalPairEisensteinLocalNumeratorStatement.{u, uQ}

theorem cuspidalPairEisensteinLocalNumeratorReduction :
    CuspidalPairEisensteinLocalNumeratorReductionStatement.{u, uQ} := by
  classical
  intro hConv hUnr hSemi F _ _ _ r t T T' hT hT' P P' S hP hP' ψ hψ
  let ψu := unitaryCharacter ψ hψ
  have hdiag : ∀ x : F, ψu (algebraMap F (Adeles F) x) = 1 := unitaryCharacter_diagonal ψ hψ
  obtain ⟨Sψ, hSψ⟩ := CuspidalPairFunctionalEquation.exists_finiteAdditiveSupport ψu hdiag
  obtain ⟨Pd⟩ := Automorphic.cuspidalDualPresentationExistence.{u, uQ, uQ} F t T'
    (dualRealization T') (Automorphic.cuspidalContragredientExistence F t T').choose_spec P'
  obtain ⟨S₀, hS₀, hnum⟩ := hSemi F r t T T' hT hT' ψ hψ (S ∪ Sψ ∪ Pd.exceptional)
  have hS : S ⊆ S₀ :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans hS₀)
  refine ⟨S₀, hS, fun s₀ hs₀ => ?_⟩
  obtain ⟨φ, hφ, hsph, c, hc, hcs₀, hc₀, σN, hcN⟩ := hnum s₀ hs₀
  have hsupp : FunctionalEquationComparison.FiniteAdditiveSupport ψu S₀ :=
    CuspidalPairFunctionalEquation.finiteAdditiveSupport_mono hSψ
      (Finset.subset_union_right.trans (Finset.subset_union_left.trans hS₀))
  have hPd : Pd.exceptional ⊆ S₀ := Finset.subset_union_right.trans hS₀
  obtain ⟨σU, hU⟩ := hUnr F r t T T' hT hT' P P' Pd S₀ (hP.trans hS) (hP'.trans hS) hPd ψu hdiag
    hsupp φ hφ hsph
  obtain ⟨σC, hC⟩ := hConv F r t T T' hT hT' ψ hψ φ hφ
  refine ⟨φ, hφ, c, hc, hcs₀, hc₀, max σN (max σU σC), fun s hs => ?_⟩
  have hσN : σN < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hσU : σU < s.re :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hσC : σC < s.re :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  have hint := hC s hσC
  rw [← unitaryCharacter_complex ψ hψ] at hint
  have h := hU s hσU hint
  rw [unitaryCharacter_complex] at h
  rw [hcN s hσN, h]

end Langlands.Global
