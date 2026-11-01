import Langlands.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Compact support of diagonal test restrictions on determinant slices -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration

universe uF uV

section Algebra

variable {K : Type uF} [Field K] [TopologicalSpace K]

/-- Restrict an actual Whittaker function through the actual diagonal inclusion. -/
def diagonalWhittaker (ψ : UnitaryAdditiveCharacter K) {n : ℕ} (d : ℕ)
    (W : WhittakerFunctions ψ (n + d)) : WhittakerFunctions ψ n :=
  ⟨fun g => W.val (appendIdentity n d g), by
    intro u g
    simpa only [appendUnipotent_val, map_mul, appendUnipotent_character] using
      W.property (appendUnipotent u d) (appendIdentity n d g)⟩

/-- Pointwise reciprocal changes the character to its inverse, also at zeros.
No regularity or convergence of this auxiliary function is asserted. -/
def reciprocalWhittaker (ψ : UnitaryAdditiveCharacter K) {n : ℕ}
    (W : WhittakerFunctions ψ n) : InverseWhittakerFunctions ψ n :=
  ⟨fun g => (W.val g)⁻¹, by
    intro u g
    change (W.val (u.val * g))⁻¹ =
      (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * (W.val g)⁻¹
    rw [W.property, mul_inv_rev, Units.val_inv_eq_inv_val, mul_comm]⟩

/-- Restriction of the supplied functional to one smaller diagonal group. -/
def diagonalFunctional (ψ : UnitaryAdditiveCharacter K) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1 + 1) K) V)
    (lambda : glFunctionals ψ (n + 1) π) :
    glFunctionals ψ n (π.comp (rankInclusion 1)) :=
  ⟨lambda.val, by
    intro u v
    change lambda.val (π (rankInclusion 1 u.val) v) = _
    have heq := lambda.property (corankOneUnipotent u) v
    rw [corankOne_standardCharacter] at heq
    exact heq⟩

/-- Continuity of the actual inclusion checks the value and inverse matrices. -/
private theorem continuous_diagonalInclusion (n d : ℕ) :
    Continuous (appendIdentity (F := K) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance diagonalSupportTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance diagonalSupportValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance diagonalSupportLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance diagonalSupportT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance diagonalSupportGLTopological (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a

/-- The norm of the diagonal restriction of every smooth coefficient has compact
support on every fixed determinant slice. No functional nonvanishing, finite
length, irreducibility or analytic estimate is required. -/
theorem diagonalWhittaker_slice_hasCompactSupport (n d : ℕ)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + (d + 1) + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ (n + (d + 1)) π)
    (W : (coefficientModel π lambda).toSubmodule) (a : ℤ) :
    HasCompactSupport ((determinantSlice F.canonicalTopologicalData n a).indicator
      (whittakerNorm ψ (diagonalWhittaker ψ (d + 1) W.val))) := by
  induction d with
  | zero =>
      obtain ⟨K, hK⟩ := model_isSmooth π hπ lambda W
      have hfix : ∀ (z : ℂ) g (k : K.toSubgroup), W.val.val (g * k) = W.val.val g := by
        intro z g k
        exact congrArg (fun f : (coefficientModel π lambda).toSubmodule => f.val.val g)
          (hK k)
      obtain ⟨C, hC, hsupport⟩ := CommonLevel.corank_common_compact_support
        F.canonicalTopologicalData n ψ (fun _ : ℂ => W.val) K.toSubgroup K.isOpen hfix a
      let : T2Space (LeftUnipotentQuotient n F.Carrier) :=
        leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F.Carrier))
      apply hC.of_isClosed_subset isClosed_closure
      apply closure_minimal _ hC.isClosed
      intro q hq
      apply hsupport 0 (reciprocalWhittaker ψ (diagonalWhittaker ψ 1 W.val)) 0
      induction q using Quotient.inductionOn with
      | h g =>
          rw [Function.mem_support, Set.indicator_apply_ne_zero] at hq ⊢
          refine ⟨hq.1, ?_⟩
          have hn : W.val.val (rankInclusion 1 g) ≠ 0 := by
            have hz := hq.2
            change whittakerNorm ψ (diagonalWhittaker ψ 1 W.val) ⟦g⟧ ≠ 0 at hz
            rw [whittakerNorm_mk] at hz
            simpa only [diagonalWhittaker, appendIdentity, MonoidHom.comp_apply,
              MonoidHom.id_apply, norm_ne_zero_iff] using hz
          change W.val.val (rankInclusion 1 g) *
            (W.val.val (appendIdentity n 1 g))⁻¹ *
              determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
                (0 - (1 : ℂ) / 2) ≠ 0
          simpa only [appendIdentity, MonoidHom.comp_apply, MonoidHom.id_apply,
            mul_inv_cancel₀ hn, one_mul] using
              determinantWeight_ne_zero (normalizedAbsoluteValue F.canonicalTopologicalData) g
                (0 - (1 : ℂ) / 2)
  | succ d ih =>
      obtain ⟨v, rfl⟩ := modelMap_surjective π lambda W
      let πsmall := π.comp (rankInclusion 1)
      let lsmall := diagonalFunctional ψ π lambda
      have hsmall : IsSmooth πsmall := by
        apply isSmooth_comp _ _ hπ
        simpa only [appendIdentity, MonoidHom.comp_id] using
          continuous_diagonalInclusion (K := F.Carrier) (n + (d + 1)) 1
      exact ih πsmall hsmall lsmall (modelMap πsmall lsmall v)

end Padic

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
