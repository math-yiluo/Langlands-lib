import Langlands.GroupScheme.CliffordSpin.GeometricPoints
import Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicSplitTorus
import Langlands.GroupScheme.Quaternionic.SpinCoverProperties
import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyOfCyclicNorm
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Langlands.Global.FiniteCompletionLocalField
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed

/-! # Isotropy of scalar spin covers over totally complex number fields -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped BigOperators TensorProduct

namespace Langlands.GroupScheme

open Quaternionic
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

private theorem quadratic_isotropic_of_algClosed {K V : Type u}
    [Field K] [CharZero K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hrank : 1 < Module.finrank K V) :
    ¬ Q.Anisotropic := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero : (2 : K) ≠ 0)
  have hsep : (QuadraticMap.associated Q).SeparatingLeft := by
    intro x hx
    apply hQ.1 x
    intro y
    change Q.polarBilin x y = 0
    rw [← QuadraticMap.two_nsmul_associated K Q]
    simp only [two_nsmul, LinearMap.add_apply, hx y, add_zero]
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed hsep
  let i : Fin (Module.finrank K V) := ⟨0, by omega⟩
  let j : Fin (Module.finrank K V) := ⟨1, hrank⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) zero_lt_two
  let x : Fin (Module.finrank K V) → K := Pi.single i 1 + Pi.single j z
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h i
    simp [x, hij] at h0
  have hs (k : Fin (Module.finrank K V)) :
      x k * x k = (if k = i then 1 else 0) + (if k = j then z ^ 2 else 0) := by
    by_cases hi : k = i
    · subst k
      simp [x, hij]
    · by_cases hj : k = j
      · subst k
        simp [x, hi, pow_two]
      · simp [x, hi, hj]
  have hsum : QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K V) → K) x = 0 := by
    simp [QuadraticMap.weightedSumSquares_apply, hs, Finset.sum_add_distrib, hz]
  intro ha
  have he := ha (e.symm x) ((e.symm.map_app x).trans hsum)
  exact hx (e.symm.toLinearEquiv.injective (he.trans e.symm.toLinearEquiv.map_zero.symm))

private theorem scalar_quadraticValue_eq_zero_of_polarQuadratic
    {F : Type u} [Field F] [CharZero F] {n : ℕ}
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)) (x : Fin n → F)
    (h : ((FirstKindInvolution.scalar F).polar q).toQuadraticForm' x = 0) :
    (FirstKindInvolution.scalar F).quadraticValue x q = 0 := by
  let σ := FirstKindInvolution.scalar F
  have heq (M : Matrix (Fin n) (Fin n) F) : M.toQuadraticForm' x = σ.sesqForm M x x := by
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, FirstKindInvolution.scalar_sesqForm, σ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at h
  obtain ⟨M, rfl⟩ := Submodule.Quotient.mk_surjective (σ.quadraticKernel (Fin n)) q
  rw [σ.sesqForm_polar_mk, FirstKindInvolution.scalar_apply, ← two_mul] at h
  exact (FirstKindInvolution.scalar_quadraticValue_mk_eq_zero_iff x M).mpr
    ((mul_eq_zero.mp h).resolve_left two_ne_zero)

/-- Every scalar spin cover of a nondegenerate quadratic form of dimension
greater than four over a totally complex number field has positive split rank. -/
def NumberFieldTotallyComplexScalarSpinIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
    (n : ℕ) (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    4 < n → (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F)))
      (p : G ⟶ (FirstKindInvolution.scalar F).isometryGroup q),
      (FirstKindInvolution.scalar F).IsSpinCover q p → ¬ IsAnisotropic G

theorem numberFieldTotallyComplexScalarSpinIsotropy :
    NumberFieldTotallyComplexScalarSpinIsotropyStatement.{u} := by
  classical
  intro F _ _ _ n q hn hq G p hp
  let : Smooth ((FirstKindInvolution.scalar F).isometryGroup q).X.hom := hp.smooth
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let σ := FirstKindInvolution.scalar F
  let Q := (σ.polar q).toQuadraticForm'
  have hQ : Q.polarBilin.Nondegenerate :=
    polar_nondegenerate_of_symmetric_unit (OrthogonalMatrix.scalar_polar_transpose q) hq
  have hdim (K : Type u) [Field K] [Algebra F K] :
      Module.finrank K (K ⊗[F] (Fin n → F)) = n := by
    rw [Module.finrank_baseChange]
    simp
  have hlocal (v : Global.Place F) : ¬ (Q.baseChange (Global.placeCompletion F v)).Anisotropic := by
    rcases v with v | v
    · let K := v.Completion
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)
      let : IsAlgClosed K := ⟨fun f => Polynomial.Splits.of_splits_map
        e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
      let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
      change ¬ (Q.baseChange K).Anisotropic
      exact quadratic_isotropic_of_algClosed (Q.baseChange K)
        (CliffordSpin.nondegenerate_polar_baseChange q hq K) (by rw [hdim]; omega)
    · let K := Global.FiniteCompletion F v
      let : ValuativeRel K := Global.FiniteCompletion.valuativeRel v
      let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField v
      intro ha
      have hb := Langlands.localQuadraticAnisotropicDimensionBound K _ (Q.baseChange K) ha
      rw [hdim] at hb
      omega
  have hIso : ¬ Q.Anisotropic :=
    Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm
      Langlands.ClassFieldTheory.Global.cyclicHasseNorm F _ Q hQ hlocal
  obtain ⟨x, hx, hQx⟩ := (QuadraticMap.not_anisotropic_iff_exists Q).mp hIso
  have hxq := scalar_quadraticValue_eq_zero_of_polarQuadratic q x hQx
  let W : Submodule F (Fin n → F) := F ∙ x
  have hW : σ.IsTotallySingular q W := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact σ.quadraticValue_smul_eq_zero a x q hxq
  have hw : 1 ≤ σ.quadraticWittIndex q := by
    have h := hW.finrank_le_quadraticWittIndex
    change Module.finrank F (F ∙ x) ≤ _ at h
    rw [finrank_span_singleton hx] at h
    exact h
  have hrank := σ.quadraticWittIndex_le_splitRank_connectedIsometryGroup q hq
  intro ha
  rw [← hp.splitRank_eq, show splitRank G = 0 from ha] at hrank
  have h0 : σ.quadraticWittIndex q = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hrank
  omega

end Langlands.GroupScheme
