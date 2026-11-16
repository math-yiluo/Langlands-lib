import Langlands.GroupScheme.Quaternionic.WittIndexOneInputs
import Langlands.GroupScheme.Quaternionic.LocalWittIndexOneDimension
import Langlands.GroupScheme.Quaternionic.HyperbolicPair

/-! # Scalar quadratic forms of Witt index one over local fields -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- A nondegenerate quadratic form of Witt index one over a division algebra
of ground-field dimension one has at most six variables. -/
theorem card_le_six_of_finrank_one_and_quadraticWittIndex_one
    (hdim : Module.finrank K D = 1) {q : σ.QuadraticForms n}
    (hq : σ.IsNondegenerateQuadratic q) (hw : σ.quadraticWittIndex q = 1) :
    Fintype.card n ≤ 6 := by
  obtain ⟨e, f, hP⟩ := σ.exists_hyperbolicPair_of_quadraticWittIndex_pos q hq (by omega)
  have hP' : Eichler.IsHyperbolic σ q e f := ⟨hP.1, hP.2.1, hP.2.2⟩
  let φ := Eichler.pairFunctional σ q e f
  let W := (LinearMap.ker φ).restrictScalars K
  obtain ⟨s⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective (σ.quadraticKernel n) q
  let QK : QuadraticForm K (n → D) :=
    s.symm.toLinearMap.compQuadraticMap
      (LinearMap.BilinMap.toQuadraticMap (σ.sesqFormBilinear Q))
  let QW : QuadraticForm K W := QK.comp W.subtype
  have hQW : QW.Anisotropic := by
    intro x hx
    apply Subtype.ext
    have hx0 : σ.sesqForm Q x.val x.val = 0 := by
      apply s.symm.injective
      exact hx.trans s.symm.map_zero.symm
    have hxq : σ.quadraticValue x.val (Submodule.Quotient.mk Q) = 0 := by
      rw [quadraticValue_mk, hx0, Submodule.Quotient.mk_zero]
    have hxφ : φ x.val = 0 := x.property
    exact Eichler.eq_zero_of_ortho_of_quadraticWittIndex_le_one hP' hw.le
      (congrArg Prod.fst hxφ) (congrArg Prod.snd hxφ) hxq
  have hK : Module.finrank K W ≤ 4 :=
    Langlands.localQuadraticAnisotropicDimensionBound K W QW hQW
  have htower := Module.finrank_mul_finrank K D W
  rw [hdim, one_mul] at htower
  have hdimW : Module.finrank D W = Module.finrank D (LinearMap.ker φ) :=
    (Submodule.restrictScalarsEquiv K D (n → D) (LinearMap.ker φ)).finrank_eq
  rw [hdimW] at htower
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank D (LinearMap.range φ) ≤ 2 := by
    simpa using Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  omega

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
