import Langlands.Representation.Archimedean.SmoothCasselmanWallachPrincipalSeries

/-! # Extending a real smooth intertwiner from its empty-word estimate -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open DerivativeSmoothVectors SmoothCasselmanWallachBound

universe uV uE₁ uE₂

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n

/-- For any compact-finite source realization, a finite-word bound on the underlying target
vector gives a unique equivariant continuous extension to the genuine smooth carriers. -/
def RealSmoothIntertwinerWordExtensionStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K n) V) (π : (ℂ ⊗[ℝ] (M n)) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (R₁ : G n →* (E₁ →L[ℂ] E₁))
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (R₂ : G n →* (E₂ →L[ℂ] E₂))
    (e : V ≃ₗ[ℂ] smoothKFinite ℝ n R₁) (f : V →ₗ[ℂ] DerivativeSmoothVectors (I n) R₂),
    IsContinuousRepresentation R₁ → IsContinuousRepresentation R₂ →
    IsSmoothGKIntertwiner ℝ n R₁ ρ π ((smoothKFinite ℝ n R₁).subtype.comp e.toLinearMap) →
    IsSmoothGKIntertwiner ℝ n R₂ ρ π f →
    (∃ (S : Finset (List (M n))) (C : ℝ),
      ∀ v, ‖derivativeCLM (I n) R₂ [] (f v)‖ ≤
        C * ∑ w ∈ S, ‖derivativeCLM (I n) R₁ w (e v : DerivativeSmoothVectors (I n) R₁)‖) →
    ∃! T : DerivativeSmoothVectors (I n) R₁ →L[ℂ] DerivativeSmoothVectors (I n) R₂,
      (∀ g x, T (representation (I n) R₁ g x) = representation (I n) R₂ g (T x)) ∧
      ∀ v, T (e v : DerivativeSmoothVectors (I n) R₁) = f v

theorem realSmoothIntertwinerWordExtension :
    RealSmoothIntertwinerWordExtensionStatement.{uV, uE₁, uE₂} := by
  intro n V _ _ ρ π E₁ _ _ _ R₁ E₂ _ _ _ R₂ e f hR₁ hR₂ he hf hb
  obtain ⟨S, C, hb⟩ := hb
  let F := smoothKFinite ℝ n R₁
  let j : V →ₗ[ℂ] DerivativeSmoothVectors (I n) R₁ := F.subtype.comp e.toLinearMap
  let t : F →ₗ[ℂ] DerivativeSmoothVectors (I n) R₂ := f.comp e.symm.toLinearMap
  have ht (v : V) : t (e v) = f v := congrArg f (e.symm_apply_apply v)
  have htc : Continuous t := by
    apply (isEmbedding_derivativeCoordinates (I n) R₂).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro Xs
    let l := (derivativeCLM (I n) R₂ Xs).toLinearMap.comp t
    change Continuous l
    apply continuous_of_tendsto_nhds_zero l
    let q (x : F) := C * ∑ w ∈ S, ‖derivativeCLM (I n) R₁ w (operatorWord R₁ Xs x.val)‖
    have hq : Continuous q := continuous_const.mul (continuous_finsetSum S fun w _ =>
      ((derivativeCLM (I n) R₁ w).continuous.comp
        ((continuous_operatorWord R₁ Xs).comp continuous_subtype_val)).norm)
    have hq₀ : q 0 = 0 := by
      simp only [q, ZeroMemClass.coe_zero, operatorWord_zero, map_zero, norm_zero,
        Finset.sum_const_zero, mul_zero]
    refine squeeze_zero_norm (fun x => ?_) (hq₀ ▸ hq.continuousAt.tendsto)
    obtain ⟨v, rfl⟩ := e.surjective x
    change ‖derivativeCLM (I n) R₂ Xs (t (e v))‖ ≤ q (e v)
    rw [ht, ← derivativeCLM_nil_operatorWord, ← map_gkWord π R₂ f hf.2]
    exact (hb (gkWord π Xs v)).trans_eq (by
      simp only [q, show (↑(e v) : DerivativeSmoothVectors (I n) R₁) = j v from rfl,
        show (↑(e (gkWord π Xs v)) : DerivativeSmoothVectors (I n) R₁) =
          j (gkWord π Xs v) from rfl, map_gkWord π R₁ j he.2])
  let t₀ : F →L[ℂ] DerivativeSmoothVectors (I n) R₂ := ⟨t, htc⟩
  let ι : F →L[ℂ] DerivativeSmoothVectors (I n) R₁ := ⟨F.subtype, continuous_subtype_val⟩
  let : CompleteSpace (DerivativeSmoothVectors (I n) R₂) :=
    completeSpace_of_isContinuousRepresentation_units R₂ hR₂
  let : IsUniformAddGroup F := F.toAddSubgroup.isUniformAddGroup
  have hι : DenseRange ι := by
    change Dense (Set.range (Subtype.val : F → DerivativeSmoothVectors (I n) R₁))
    rw [Subtype.range_coe]
    exact realSmoothCompactFiniteDensity n E₁ R₁ hR₁
  let T := t₀.extend ι
  have hT (v : V) : T (j v) = f v :=
    (t₀.extend_eq hι isUniformEmbedding_subtype_val.isUniformInducing (e v)).trans (ht v)
  have commute (A : DerivativeSmoothVectors (I n) R₁ →L[ℂ] DerivativeSmoothVectors (I n) R₁)
      (B : DerivativeSmoothVectors (I n) R₂ →L[ℂ] DerivativeSmoothVectors (I n) R₂)
      (a : V → V) (ha : ∀ v, j (a v) = A (j v)) (hb' : ∀ v, f (a v) = B (f v))
      (x : DerivativeSmoothVectors (I n) R₁) : T (A x) = B (T x) := by
    have heq := hι.equalizer (T.continuous.comp A.continuous)
      (B.continuous.comp T.continuous) (funext fun y => by
        obtain ⟨v, rfl⟩ := e.surjective y
        change T (A (j v)) = B (T (j v))
        rw [← ha, hT, hT, hb'])
    exact congrFun heq x
  have hLie (X : M n) (x : DerivativeSmoothVectors (I n) R₁) :
      T (operator (I n) R₁ X x) = operator (I n) R₂ X (T x) :=
    commute (operatorCLM (I n) R₁ X) (operatorCLM (I n) R₂ X)
      (π (1 ⊗ₜ[ℝ] X)) (he.2 X) (hf.2 X) x
  have hK (k : K n) (x : DerivativeSmoothVectors (I n) R₁) :
      T (representation (I n) R₁ (Unitary.toUnits k) x) =
        representation (I n) R₂ (Unitary.toUnits k) (T x) :=
    commute (SmoothAction.derivativeAction (I n) R₁ (Unitary.toUnits k))
      (SmoothAction.derivativeAction (I n) R₂ (Unitary.toUnits k)) (ρ k) (he.1 k) (hf.1 k) x
  refine ⟨T, ⟨smoothRealGroupIntertwining n E₁ E₂ R₁ R₂ hR₁ hR₂ T hLie hK, hT⟩, ?_⟩
  intro U hU
  apply ContinuousLinearMap.ext
  intro x
  have heq := hι.equalizer U.continuous T.continuous (funext fun y => by
    obtain ⟨v, rfl⟩ := e.surjective y
    change U (j v) = T (j v)
    exact (hU.2 v).trans (hT v).symm)
  exact congrFun heq x

open Langlands.Global.RankinSelbergGlobal in
/-- A finite-word estimate on the scalar minimal principal series gives a smooth
full-group extension for every compact and Lie intertwiner from it. -/
theorem realPrincipalSeriesSmoothExtension_of_wordBound (hP : RealPrincipalSeriesWordBoundStatement.{uE₂})
    (r : ℕ) (cs : List RealCharacterData) (hcs : cs.length = r + 1)
    {E : Type uE₂} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G (r + 1) →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
    (f : kFiniteFunctions (realStandardModule (r + 1) (cs.map RealBlock.character))
        (unitaryCompact ℝ (r + 1)) →ₗ[ℂ] DerivativeSmoothVectors (I (r + 1)) R)
    (hf : IsSmoothGKIntertwiner ℝ (r + 1) R
      (realStandardRep (r + 1) (cs.map RealBlock.character))
      (realStandardLie (r + 1) (cs.map RealBlock.character)) f) :
    let ds := cs.map RealBlock.character
    let R₀ := RealStandardCompactBanach.representation (n := r + 1) ds
    ∃! T : DerivativeSmoothVectors (I (r + 1)) R₀ →L[ℂ] DerivativeSmoothVectors (I (r + 1)) R,
      (∀ g x, T (representation (I (r + 1)) R₀ g x) = representation (I (r + 1)) R g (T x)) ∧
      ∀ w, T ((RealStandardCompactBanach.compactFiniteEquiv (n := r + 1) ds) w).val = f w := by
  intro ds R₀
  obtain ⟨S, C, _, hS⟩ := hP r cs hcs E R f hR hf
  exact realSmoothIntertwinerWordExtension (r + 1) _ (realStandardRep (r + 1) ds)
    (realStandardLie (r + 1) ds) _ R₀ E R (RealStandardCompactBanach.compactFiniteEquiv ds) f
    (RealStandardCompactBanach.isContinuousRepresentation ds) hR
    (RealStandardCompactBanach.isSmoothGKIntertwiner_compactFiniteEquiv ds) hf ⟨S, C, hS⟩

end Langlands.Archimedean
