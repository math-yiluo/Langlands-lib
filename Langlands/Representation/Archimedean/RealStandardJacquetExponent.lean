import Langlands.Representation.Archimedean.ComplexGelfandSeparation
import Langlands.Representation.Archimedean.GLBurnside
import Langlands.Representation.Archimedean.Kostant.RealTransfer
import Langlands.Representation.Archimedean.LowerVermaCentral
import Langlands.Representation.Archimedean.LowerVermaDuflo
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealStandardCentralGrowth
import Langlands.Representation.Archimedean.RealSubquotientEval

/-! # The exponents of real standard module Jacquet functionals

The central Gelfand operators determine the unordered normalized exponents of a
nonzero Borel Jacquet functional. The paired Markdown describes the computation.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean MvPolynomial
open RealBlockPosition ComplexJacquetFinite GelfandSeparation

namespace RealStandardJacquetExponent

private abbrev CLie (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
private abbrev RLie (n : ℕ) := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ

private def realLieEquiv (n : ℕ) : CLie n ≃ₗ⁅ℂ⁆ RLie n :=
  (VermaPBW.toUnitProd n).trans (Kostant.toGL n).symm

private theorem realLieEquiv_single (n : ℕ) (i j : Fin n) :
    realLieEquiv n (Matrix.single i j 1) = 1 ⊗ₜ Matrix.single i j 1 := by
  apply (Kostant.toGL n).injective
  change Kostant.toGL n ((Kostant.toGL n).symm (VermaPBW.toUnitProd n _)) = _
  rw [LieEquiv.apply_symm_apply]
  funext u
  change Matrix.single i j (1 : ℂ) =
    Kostant.toGL n ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single i j 1) u
  rw [Kostant.toGL_tmul]
  ext p q
  change Matrix.single i j (1 : ℂ) p q =
    ((1 : ℂ) • (Matrix.single i j (1 : ℝ)).map (algebraMap ℝ ℂ)) p q
  simp [Matrix.single_apply, apply_ite]

section Gelfand

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

private abbrev diag (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) (i : Fin n) :=
  GLReynolds.famOf σ i i

private theorem diag_commute (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) (i j : Fin n) :
    Commute (diag σ i) (diag σ j) := by
  change diag σ i * diag σ j = diag σ j * diag σ i
  apply sub_eq_zero.mp
  rw [GLReynolds.isGlFamily_famOf σ i i j j]
  by_cases h : i = j <;> simp [h, eq_comm]

private abbrev diagAlgebra (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) :=
  Algebra.adjoin ℂ (Set.range (diag σ))

private instance diagAlgebraCommRing (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) :
    CommRing (diagAlgebra σ) where
  mul_comm x y := by
    apply Subtype.ext
    have hgen : ∀ a ∈ Set.range (diag σ), ∀ b ∈ Set.range (diag σ), Commute a b := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact diag_commute σ i j
    have hy : ∀ a ∈ Set.range (diag σ), Commute a y.val :=
      fun a ha => Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.2 (hgen a ha)
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.2
      (fun a ha => (hy a ha).symm)).eq.symm

private def diagAction (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (diagAlgebra σ).val.comp (MvPolynomial.aeval fun i =>
    ⟨diag σ i, Algebra.subset_adjoin (Set.mem_range_self i)⟩)

private theorem diagAction_X (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) (i : Fin n) :
    diagAction σ (X i) = diag σ i := by
  simp [diagAction]

private theorem eval_diagAction {σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} (hdiag : ∀ i v, ℓ (diag σ i v) = a i * ℓ v)
    (f : MvPolynomial (Fin n) ℂ) : ∀ v, ℓ (diagAction σ f v) = eval a f * ℓ v := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    intro v
    rw [MvPolynomial.algHom_C, Module.algebraMap_end_apply, map_smul, eval_C, smul_eq_mul]
  | add p q hp hq =>
    intro v
    rw [map_add, LinearMap.add_apply, map_add, hp, hq, map_add, add_mul]
  | mul_X p i hp =>
    intro v
    rw [map_mul, Module.End.mul_apply, hp, diagAction_X, hdiag, eval_mul, eval_X, mul_assoc]

private theorem gel_action (σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V) (k : ℕ) :
    envelopingAction σ (VermaCentral.gel n k) =
      ∑ i, (Matrix.of (GLReynolds.famOf σ) ^ k) i i := by
  let A := envelopingAction σ
  have h : A.mapMatrix (VermaCentral.Gm n) = Matrix.of (GLReynolds.famOf σ) := by
    ext i j : 1
    change A (VermaGL.unitU n i j) = σ (Matrix.single i j 1)
    simp [A, VermaGL.unitU, envelopingAction]
  rw [VermaCentral.gel, map_sum, ← h, ← map_pow]
  rfl

private theorem eval_gel {σ : CLie n →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ}
    (hup : ∀ i j, i < j → ∀ v, ℓ (GLReynolds.famOf σ i j v) = 0)
    (hdiag : ∀ i v, ℓ (diag σ i v) = a i * ℓ v) (k : ℕ) (v : V) :
    ℓ (envelopingAction σ (VermaCentral.gel n k) v) = (∑ i, gv a k i) * ℓ v := by
  have hdiag' : ∀ i v, v ∈ LinearMap.ker ℓ → diag σ i v ∈ LinearMap.ker ℓ := by
    intro i v hv
    rw [LinearMap.mem_ker, hdiag, LinearMap.mem_ker.mp hv, mul_zero]
  rw [gel_action, LinearMap.sum_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have h := diag_pow (LinearMap.ker ℓ) (GLReynolds.isGlFamily_famOf σ)
    (fun i j hij v => LinearMap.mem_ker.mpr (hup i j hij v))
    hdiag' (diagAction σ) (diagAction_X σ) k i v
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, eval_diagAction hdiag] at h
  exact h

private theorem gel_sums_eq {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : RLie n →ₗ⁅ℂ⁆ Module.End ℂ V} (hinf : HasInfinitesimalCharacter π)
    {ℓ ℓ' : V →ₗ[ℂ] ℂ} {a a' : Fin n → ℂ} {e e' : Fin n → Fin 2}
    (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0)
    (hj : IsRealJacquetFunctional n ρ π ℓ a e)
    (hj' : IsRealJacquetFunctional n ρ π ℓ' a' e') (k : ℕ) :
    ∑ i, gv a k i = ∑ i, gv a' k i := by
  let σ := π.comp (realLieEquiv n).toLieHom
  obtain ⟨c, hc⟩ := Kostant.hasInfinitesimalCharacter_comp (realLieEquiv n).symm hinf
    (VermaCentral.gel n k) (VermaCentral.gel_mem_center n k)
  have hmat (i j : Fin n) (v : V) :
      GLReynolds.famOf σ i j v = π (1 ⊗ₜ Matrix.single i j 1) v := by
    change π (realLieEquiv n (Matrix.single i j 1)) v = _
    rw [realLieEquiv_single]
  have hsum (ℓ₀ : V →ₗ[ℂ] ℂ) (a₀ : Fin n → ℂ) (e₀ : Fin n → Fin 2)
      (hℓ₀ : ℓ₀ ≠ 0) (h₀ : IsRealJacquetFunctional n ρ π ℓ₀ a₀ e₀) :
      ∑ i, gv a₀ k i = c := by
    obtain ⟨v, hv⟩ := Kostant.BorelCentralIdeal.exists_ne_zero_of_ne_zero hℓ₀
    have h := eval_gel (σ := σ) (ℓ := ℓ₀) (a := a₀)
      (fun i j hij w => by
        rw [hmat]
        apply h₀.1 _ _ w
        intro p q hpq
        apply Matrix.single_apply_of_ne
        rintro ⟨rfl, rfl⟩
        exact (not_le_of_gt hij) hpq)
      (fun i w => by
        change ℓ₀ (GLReynolds.famOf σ i i w) = _
        rw [hmat]
        exact (h₀.2 i w).1) k v
    change envelopingAction σ (VermaCentral.gel n k) = _ at hc
    rw [hc, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at h
    exact (mul_right_cancel₀ hv h).symm
  rw [hsum ℓ a e hℓ hj, hsum ℓ' a' e' hℓ' hj']

end Gelfand

open GramFormula

private theorem eval_isJacquet (n : ℕ) (ds : List RealBlock) :
    IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (kFiniteEval (realStandardModule n ds) 1) (shiftedExponent n ds) (positionSign n ds) := by
  have hder {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsUpperTriangular)
      (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
      kFiniteEval (realStandardModule n ds) 1 (realStandardLie n ds (1 ⊗ₜ X) v) =
        (∑ j, shiftedExponent n ds j * (X j j : ℂ)) *
          kFiniteEval (realStandardModule n ds) 1 v := by
    have hPS := realStandardModule_le_principalSeries n ds v.2.1
    rw [← principalSeries_posChar_shiftedExponent] at hPS
    change ((realStandardLie n ds (1 ⊗ₜ X) v : kFiniteFunctions _ _) :
      Langlands.GeneralLinear n ℝ → ℂ) 1 = _
    rw [realStandardLie_one_tmul_apply_coe]
    exact RealSubquotient.rightDerivative_upper_apply_one hPS hX
  constructor
  · intro X hX v
    rw [hder (fun i j hij => hX i j hij.le) v]
    simp [hX]
  · intro j v
    constructor
    · rw [hder (Matrix.blockTriangular_single (b := id) (le_refl j) (1 : ℝ)) v]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij.symm]
      · simp
    · change ((realStandardRep n ds (signReflection n j) v : kFiniteFunctions _ _) :
        Langlands.GeneralLinear n ℝ → ℂ) 1 = _
      rw [realStandardRep_apply_coe]
      change (v : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits (signReflection n j)) = _
      rw [one_mul, ← mul_one (Unitary.toUnits (signReflection n j)),
        RealBlockFourierFinite.apply_signReflection_mul
          (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds)
          (realStandardModule_le_principalSeries n ds v.2.1),
        realPositionCharacter_neg_one]
      rfl

end RealStandardJacquetExponent

open RealStandardJacquetExponent GramFormula

/-- The exponents of a nonzero real standard module Jacquet functional, after removing the
principal-series shift, are a permutation of the exponents of the position characters. -/
def RealStandardJacquetExponentStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (a : Fin n → ℂ) (e : Fin n → Fin 2)
    (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ),
    ℓ ≠ 0 → IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e →
      ∃ w : Equiv.Perm (Fin n), ∀ j, RealJacquetFrobenius.expo a j =
        realPositionExponent ds (w j)

theorem realStandardJacquetExponent : RealStandardJacquetExponentStatement := by
  intro n ds a e ℓ hℓ hj
  obtain ⟨v, hv⟩ := Kostant.BorelCentralIdeal.exists_ne_zero_of_ne_zero hℓ
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hev := RealStandardCentralGrowth.kFiniteEval_one_ne_zero hv0
  have h := gel_sums_eq (realStandardLie_hasInfinitesimalCharacter n ds)
    hℓ hev hj (eval_isJacquet n ds)
  obtain ⟨w, hw⟩ := exists_perm_of_gel_eq a (shiftedExponent n ds) h
  refine ⟨w, fun j => ?_⟩
  unfold RealJacquetFrobenius.expo
  unfold RealBlockPosition.shiftedExponent at hw
  linear_combination hw j

/-- A surjective intertwiner onto a nonzero standard module identifies the position
exponents up to permutation. -/
theorem realStandardPositionExponent_perm_of_surjective {n : ℕ} {ds es : List RealBlock}
    {T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T)
    (hsurj : Function.Surjective T)
    (hne : Nontrivial (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))) :
    ∃ w : Equiv.Perm (Fin n), ∀ j : Fin n,
      realPositionExponent es j = realPositionExponent ds (w j) := by
  let ev := kFiniteEval (realStandardModule n es) 1
  have hev : ev ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))
    exact RealStandardCentralGrowth.kFiniteEval_one_ne_zero hv
  let ℓ := ev ∘ₗ T
  have hℓ : ℓ ≠ 0 := by
    intro hz
    apply hev
    ext v
    obtain ⟨u, rfl⟩ := hsurj v
    exact LinearMap.congr_fun hz u
  have hJ := eval_isJacquet n es
  have hpull : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      ℓ (RealBlockPosition.shiftedExponent n es) (positionSign n es) := by
    refine ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
    · simpa only [ℓ, LinearMap.comp_apply, hT.map_realStandardLie] using hJ.1 X hX (T v)
    · simpa only [ℓ, LinearMap.comp_apply, hT.map_realStandardLie] using (hJ.2 j (T v)).1
    · simpa only [ℓ, LinearMap.comp_apply, hT.map_realStandardRep] using (hJ.2 j (T v)).2
  obtain ⟨w, hw⟩ := realStandardJacquetExponent n ds _ _ ℓ hℓ hpull
  exact ⟨w, fun j => by simpa only [expo_shiftedExponent] using hw j⟩

end Langlands.Archimedean
