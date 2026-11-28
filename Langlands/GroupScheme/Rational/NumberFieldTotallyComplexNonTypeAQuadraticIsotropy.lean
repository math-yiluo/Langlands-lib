import Langlands.ClassFieldTheory.Global.CyclicHasseNormProof
import Langlands.Global.FiniteCompletionLocalField
import Langlands.GroupScheme.Composition.CayleyOrthogonalFrame
import Langlands.GroupScheme.Composition.IsotropicCayleyAutomorphismRankProof
import Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic
import Langlands.GroupScheme.OrthogonalMatrix.ScalarPoints
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankProof
import Langlands.GroupScheme.Quaternionic.LocalWittIndexOneDimension
import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Langlands.GroupScheme.Rational.NumberFieldTypeCModels
import Langlands.GroupScheme.SimplyConnected.TypeBOddQuadraticPresentationProof
import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyPresentationProof
import Langlands.GroupScheme.SymplecticMatrix.Torus
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Langlands.LinearAlgebra.NumberFieldGramIsometry
import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyOfCyclicNorm

/-! # Totally complex isotropy for types B, C and G2 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix Module
open scoped BigOperators TensorProduct

namespace Langlands.GroupScheme

open Quaternionic
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Over a totally complex number field, a nondegenerate quadratic form of
 dimension greater than four has a nonzero isotropic vector. -/
theorem numberField_totallyComplex_quadratic_exists_isotropic
    {F V : Type u} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : IsTotallyComplex F) (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hr : 4 < finrank F V) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  have hdim (K : Type u) [Field K] [Algebra F K] : finrank K (K ⊗[F] V) = finrank F V :=
    Module.finrank_baseChange
  have hl (v : Global.Place F) : ¬ (Q.baseChange (Global.placeCompletion F v)).Anisotropic := by
    rcases v with v | v
    · let K := v.Completion
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)
      let : IsAlgClosed K := ⟨fun f => Polynomial.Splits.of_splits_map
        e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
      obtain ⟨x, hx, hz⟩ := OrthogonalMatrix.exists_isotropic
        (by rw [hdim K]; omega) (Q.baseChange K)
      exact fun h => hx (h x hz)
    · let K := Global.FiniteCompletion F v
      let : ValuativeRel K := Global.FiniteCompletion.valuativeRel v
      let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField v
      intro h
      have hb := Langlands.localQuadraticAnisotropicDimensionBound K _ (Q.baseChange K) h
      rw [hdim K] at hb
      omega
  exact Q.not_anisotropic_iff_exists.mp (Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm
    Langlands.ClassFieldTheory.Global.cyclicHasseNorm F V Q hQ hl)

/-- A scalar nondegenerate form of dimension greater than four over a
totally complex number field has positive Witt index. -/
theorem FirstKindInvolution.scalarQuadraticWittIndex_pos_of_totallyComplex
    {F : Type u} [Field F] [NumberField F] (hF : IsTotallyComplex F) {n : ℕ}
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))
    (hq : (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q) (hn : 4 < n) :
    0 < (FirstKindInvolution.scalar F).quadraticWittIndex q := by
  classical
  let σ := FirstKindInvolution.scalar F
  let Q := (σ.polar q).toQuadraticForm'
  have hQ : Q.polarBilin.Nondegenerate :=
    polar_nondegenerate_of_symmetric_unit (OrthogonalMatrix.scalar_polar_transpose q) hq
  obtain ⟨x, hx, hzero⟩ := numberField_totallyComplex_quadratic_exists_isotropic hF Q hQ (by simpa using hn)
  have hval (M : Matrix (Fin n) (Fin n) F) : M.toQuadraticForm' x = σ.sesqForm M x x := by
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, FirstKindInvolution.scalar_sesqForm, σ]
    apply Finset.sum_congr rfl fun i _ => ?_
    apply Finset.sum_congr rfl fun j _ => ?_
    ring
  change (σ.polar q).toQuadraticForm' x = 0 at hzero
  rw [hval] at hzero
  have hxq : σ.quadraticValue x q = 0 := by
    obtain ⟨M, rfl⟩ := Submodule.Quotient.mk_surjective (σ.quadraticKernel (Fin n)) q
    rw [σ.sesqForm_polar_mk, FirstKindInvolution.scalar_apply, ← two_mul] at hzero
    exact (FirstKindInvolution.scalar_quadraticValue_mk_eq_zero_iff x M).mpr
      ((mul_eq_zero.mp hzero).resolve_left two_ne_zero)
  let W : Submodule F (Fin n → F) := F ∙ x
  have hW : σ.IsTotallySingular q W := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact σ.quadraticValue_smul_eq_zero a x q hxq
  exact (finrank_span_singleton hx).ge.trans hW.finrank_le_quadraticWittIndex

section Groups

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Type C of rank at least two is isotropic over a totally complex number field. -/
theorem TitsIndexData.not_isAnisotropic_of_typeC_totallyComplex
    (d : TitsIndexData G) (hF : IsTotallyComplex F) (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G) {n : ℕ} (hn : 2 ≤ n) (e : d.Vertex ≃ Fin n)
    (hC : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) : ¬ IsAnisotropic G := by
  intro hG
  rcases numberFieldTypeCModels F G d n e hn hsc habs hC with hsplit | ⟨_, D, _, _, _, _, hD, σ, hσ, H, hH, hu, ⟨t⟩⟩
  · obtain ⟨t⟩ := hsplit
    have h := card_le_splitRank (ULift.{u} (Fin n)) _
      (SymplecticMatrix.isClosedSubgroup_diagonalTorus (Fin n) F)
    rw [← splitRank_eq_of_iso t, show splitRank G = 0 from hG] at h
    have h0 := nonpos_iff_eq_zero.mp h
    simp at h0
    omega
  · let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    have hline := σ.finrank_alternatingSubspace_of_dimensions hD hσ
    let ℓ := σ.alternatingCoordinate hline
    have hℓ : ∃ a, ℓ (a - σ a) ≠ 0 := by
      have hne : σ.alternatingSubspace ≠ ⊥ := by
        intro hh
        rw [hh, finrank_bot] at hline
        exact Nat.zero_ne_one hline
      obtain ⟨a, ha, han⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨b, hb⟩ := σ.mem_alternatingSubspace.mp ha
      exact ⟨b, fun h => han ((σ.alternatingCoordinate_eq_zero_iff hline ha).mp (hb ▸ h))⟩
    have hdim : 4 < finrank F (Fin n → D) := by
      rw [Module.finrank_pi_fintype]
      simp only [hD, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change 4 < n * 4
      omega
    obtain ⟨x, hx, hz⟩ := numberField_totallyComplex_quadratic_exists_isotropic hF
      (σ.scalarQuadratic ℓ H) (σ.scalarQuadratic_nondegenerate ℓ hH hu hℓ) hdim
    have hxx := (σ.alternatingCoordinate_eq_zero_iff hline
      (σ.sesqForm_self_mem_alternatingSubspace hH x)).mp hz
    have hlineIso := (σ.isTotallyIsotropic_span_singleton_iff H x).mpr hxx
    have hr := AntihermitianSplitRank.wittIndex_le_splitRank σ H hH hu
    rw [← splitRank_eq_of_iso t, show splitRank G = 0 from hG] at hr
    have hr0 : σ.wittIndex H = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hr
    have hpos := σ.finrank_le_wittIndex hlineIso
    rw [finrank_span_singleton hx, hr0] at hpos
    omega

/-- Type B of rank at least two is isotropic over a totally complex number field. -/
theorem TitsIndexData.not_isAnisotropic_of_typeB_totallyComplex
    (d : TitsIndexData G) (hF : IsTotallyComplex F) (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G) {n : ℕ} (hn : 2 ≤ n) (e : d.Vertex ≃ Fin n)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) : ¬ IsAnisotropic G := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    have hBC (i j : Fin 2) : CartanMatrix.B 2 i j = CartanMatrix.C 2 (Fin.revPerm i) (Fin.revPerm j) := by
      fin_cases i <;> fin_cases j <;> decide
    exact d.not_isAnisotropic_of_typeC_totallyComplex hF hsc habs (by decide) (e.trans Fin.revPerm)
      (fun a b => (hB a b).trans (hBC (e a) (e b)))
  obtain ⟨q, _, hk, hr, _⟩ := typeBOddQuadraticPresentation F G d n e (by omega) hsc habs hB
  rw [ite_eq_right two_ne_zero] at hk
  have hq : (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q :=
    Matrix.vecMul_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk))
  have hp := FirstKindInvolution.scalarQuadraticWittIndex_pos_of_totallyComplex hF q hq (by omega)
  intro hG
  rw [show splitRank G = 0 from hG] at hr
  exact hp.ne' (by exact_mod_cast hr)

/-- Type G2 is split over a totally complex number field. -/
theorem TitsIndexData.splitRank_eq_two_of_typeG2_totallyComplex
    (d : TitsIndexData G) (hF : IsTotallyComplex F) (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G) (e : d.Vertex ≃ Fin 2)
    (hG2 : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) : splitRank G = 2 := by
  obtain ⟨c, i, hi⟩ := typeG2CayleyPresentation F G d e hsc habs hG2
  exact isotropicCayleyAutomorphismRank F c G i hi
    (numberField_totallyComplex_quadratic_exists_isotropic hF c.norm c.norm_nondegenerate (by
      simp [CayleyVector]))

end Groups

/-- The simply connected forms of types B and C in rank at least two have
positive split rank over a totally complex number field, and type G2 has
split rank two. -/
def NumberFieldTotallyComplexNonTypeAQuadraticIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ n : ℕ, 2 ≤ n → ∀ e : d.Vertex ≃ Fin n,
        (∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) → ¬ IsAnisotropic G) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ e : d.Vertex ≃ Fin n,
        (∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b)) → ¬ IsAnisotropic G) ∧
      (∀ e : d.Vertex ≃ Fin 2,
        (∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) → splitRank G = 2)

theorem numberFieldTotallyComplexNonTypeAQuadraticIsotropy :
    NumberFieldTotallyComplexNonTypeAQuadraticIsotropyStatement.{u} := by
  intro F _ _ hF G _ _ d hsc habs
  exact ⟨fun _ => d.not_isAnisotropic_of_typeB_totallyComplex hF hsc habs,
    fun _ => d.not_isAnisotropic_of_typeC_totallyComplex hF hsc habs,
    d.splitRank_eq_two_of_typeG2_totallyComplex hF hsc habs⟩

end Langlands.GroupScheme
