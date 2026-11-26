import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.Archimedean.RealSmoothCompactFiniteDensity
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Langlands.Representation.Archimedean.SmoothRealGroupIntertwining
import Langlands.Representation.Archimedean.SmoothAction
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

/-! # Casselman–Wallach extension from a finite word-seminorm bound -/

noncomputable section

universe uV uE₁ uE₂ uE
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Casselman–Wallach bound (real general linear groups).** Let `V` be an irreducible
admissible `(𝔤, K)`-module for `GL_(r+1)(ℝ)` and `O(r+1)`, identified by `e`, with its
compact action and derivatives, with all compact-finite genuine smooth vectors of a jointly
continuous representation `R₁` on a complex Banach space. Let `f` be a linear map from `V`
into the genuine smooth vectors of any jointly continuous representation `R₂` on a complex
Banach space that intertwines the compact action and derivatives. Then the norm of the
underlying vector of `f v` is bounded by a constant times a finite sum of genuine word
seminorms of `e v`. -/
def RealSmoothCasselmanWallachBoundStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (R₁ : Langlands.GeneralLinear (r + 1) ℝ →* (E₁ →L[ℂ] E₁))
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (R₂ : Langlands.GeneralLinear (r + 1) ℝ →* (E₂ →L[ℂ] E₂))
    (e : V ≃ₗ[ℂ] smoothKFinite ℝ (r + 1) R₁)
    (f : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₂),
    IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
    IsContinuousRepresentation R₁ → IsContinuousRepresentation R₂ →
    IsSmoothGKIntertwiner ℝ (r + 1) R₁ ρ π
      ((smoothKFinite ℝ (r + 1) R₁).subtype.comp e.toLinearMap) →
    IsSmoothGKIntertwiner ℝ (r + 1) R₂ ρ π f →
      ∃ (S : Finset (List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ))) (C : ℝ),
        ∀ v : V,
          ‖DerivativeSmoothVectors.derivativeCLM (matrixModel ℝ (r + 1)) R₂ [] (f v)‖ ≤
            C * ∑ Xs ∈ S,
              ‖DerivativeSmoothVectors.derivativeCLM (matrixModel ℝ (r + 1)) R₁ Xs
                (e v : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₁)‖

namespace SmoothCasselmanWallachBound

open DerivativeSmoothVectors

section Words

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))

/-- The composite `dR(X₁) ∘ ⋯ ∘ dR(Xₖ)` of genuine derived operators along a word. -/
def operatorWord (Xs : List (Matrix (Fin n) (Fin n) ℝ))
    (y : DerivativeSmoothVectors (matrixModel ℝ n) R) :
    DerivativeSmoothVectors (matrixModel ℝ n) R :=
  Xs.foldr (fun X w => operator (matrixModel ℝ n) R X w) y

theorem continuous_operatorWord (Xs : List (Matrix (Fin n) (Fin n) ℝ)) :
    Continuous (operatorWord R Xs) := by
  induction Xs with
  | nil => exact continuous_id
  | cons X Xs ih => exact (continuous_operator (matrixModel ℝ n) R X).comp ih

theorem operatorWord_zero (Xs : List (Matrix (Fin n) (Fin n) ℝ)) :
    operatorWord R Xs 0 = 0 := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change operator (matrixModel ℝ n) R X (operatorWord R Xs 0) = 0
    rw [ih, map_zero]

theorem derivativeCLM_nil_operator (X : Matrix (Fin n) (Fin n) ℝ)
    (w : DerivativeSmoothVectors (matrixModel ℝ n) R) :
    derivativeCLM (matrixModel ℝ n) R [] (operator (matrixModel ℝ n) R X w) =
      lieDerivative (matrixModel ℝ n) R X (derivativeCLM (matrixModel ℝ n) R [] w) := by
  rw [derivativeCLM_apply, derivativeCLM_apply, iteratedLieDerivative_nil,
    iteratedLieDerivative_nil, toSmooth_operator, smoothLieDerivative_apply]

/-- The underlying vector of the composite of derived operators along a word is the
genuine word derivative. -/
theorem derivativeCLM_nil_operatorWord (Xs : List (Matrix (Fin n) (Fin n) ℝ))
    (y : DerivativeSmoothVectors (matrixModel ℝ n) R) :
    derivativeCLM (matrixModel ℝ n) R [] (operatorWord R Xs y) =
      derivativeCLM (matrixModel ℝ n) R Xs y := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change derivativeCLM (matrixModel ℝ n) R []
        (operator (matrixModel ℝ n) R X (operatorWord R Xs y)) = _
    rw [derivativeCLM_nil_operator, ih, derivativeCLM_apply, derivativeCLM_apply,
      iteratedLieDerivative_cons]

end Words

section Algebraic

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The composite `π(1 ⊗ X₁) ∘ ⋯ ∘ π(1 ⊗ Xₖ)` along a word of real matrices. -/
def gkWord (Xs : List (Matrix (Fin n) (Fin n) ℝ)) (v : V) : V :=
  Xs.foldr (fun X w => π (1 ⊗ₜ[ℝ] X) w) v

theorem map_gkWord {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    (f : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ n) R)
    (hf : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
      f (π (1 ⊗ₜ[ℝ] X) v) = operator (matrixModel ℝ n) R X (f v))
    (Xs : List (Matrix (Fin n) (Fin n) ℝ)) (v : V) :
    f (gkWord π Xs v) = operatorWord R Xs (f v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change f (π (1 ⊗ₜ[ℝ] X) (gkWord π Xs v)) =
      operator (matrixModel ℝ n) R X (operatorWord R Xs (f v))
    rw [hf, ih]

end Algebraic

end SmoothCasselmanWallachBound

open SmoothCasselmanWallachBound DerivativeSmoothVectors in
/-- The finite word-seminorm bound implies the Casselman–Wallach extension: extend the
given map from the dense compact-finite subspace to the complete target carrier, and
upgrade compact and Lie equivariance to equivariance for the whole group. -/
theorem realSmoothCasselmanWallachExtension_of_bound
    (h : RealSmoothCasselmanWallachBoundStatement.{uV, uE₁, uE₂}) :
    RealSmoothCasselmanWallachExtensionStatement.{uV, uE₁, uE₂} := by
  intro r V _ _ ρ π E₁ _ _ _ R₁ E₂ _ _ _ R₂ e f hirr hadm hR₁ hR₂ he hf
  obtain ⟨S, C, hb⟩ := h r V ρ π E₁ R₁ E₂ R₂ e f hirr hadm hR₁ hR₂ he hf
  let I := matrixModel ℝ (r + 1)
  let F := smoothKFinite ℝ (r + 1) R₁
  have hew : ∀ (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) (v : V),
      ((e (gkWord π Xs v) : F) : DerivativeSmoothVectors I R₁) =
        operatorWord R₁ Xs (e v : DerivativeSmoothVectors I R₁) :=
    map_gkWord π R₁ (F.subtype.comp e.toLinearMap) he.2
  have hfw := map_gkWord π R₂ f hf.2
  let t : F →ₗ[ℂ] DerivativeSmoothVectors I R₂ := f.comp e.symm.toLinearMap
  have ht : ∀ v : V, t (e v) = f v := fun v => congrArg f (e.symm_apply_apply v)
  have htc : Continuous t := by
    apply (isEmbedding_derivativeCoordinates I R₂).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro Xs
    let T := (derivativeCLM I R₂ Xs).toLinearMap.comp t
    change Continuous T
    apply continuous_of_tendsto_nhds_zero T
    have hQ : Continuous (fun y : F => C * ∑ Ys ∈ S,
        ‖derivativeCLM I R₁ Ys (operatorWord R₁ Xs (y : DerivativeSmoothVectors I R₁))‖) :=
      continuous_const.mul (continuous_finsetSum S fun Ys _ =>
        ((derivativeCLM I R₁ Ys).continuous.comp
          ((continuous_operatorWord R₁ Xs).comp continuous_subtype_val)).norm)
    have hlim := hQ.tendsto 0
    simp only [ZeroMemClass.coe_zero, operatorWord_zero, map_zero, norm_zero,
      Finset.sum_const_zero, mul_zero] at hlim
    refine squeeze_zero_norm (fun y => ?_) hlim
    obtain ⟨v, rfl⟩ := e.surjective y
    change ‖derivativeCLM I R₂ Xs (t (e v))‖ ≤ _
    rw [ht, ← derivativeCLM_nil_operatorWord, ← hfw, ← hew]
    exact hb (gkWord π Xs v)
  let t₀ : F →L[ℂ] DerivativeSmoothVectors I R₂ := ⟨t, htc⟩
  let ι : F →L[ℂ] DerivativeSmoothVectors I R₁ := ⟨F.subtype, continuous_subtype_val⟩
  let : CompleteSpace (DerivativeSmoothVectors I R₂) :=
    completeSpace_of_isContinuousRepresentation_units R₂ hR₂
  let : IsUniformAddGroup F := F.toAddSubgroup.isUniformAddGroup
  have hd : Dense (F : Set (DerivativeSmoothVectors I R₁)) :=
    realSmoothCompactFiniteDensity (r + 1) E₁ R₁ hR₁
  have hι : DenseRange ι := by
    change Dense (Set.range (Subtype.val : F → DerivativeSmoothVectors I R₁))
    rwa [Subtype.range_coe]
  let T := t₀.extend ι
  have hT : ∀ v : V, T (e v : DerivativeSmoothVectors I R₁) = f v := fun v =>
    (t₀.extend_eq hι isUniformEmbedding_subtype_val.isUniformInducing (e v)).trans (ht v)
  refine ⟨T, ?_, hT⟩
  have hLie : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (y : DerivativeSmoothVectors I R₁),
      T (operator I R₁ X y) = operator I R₂ X (T y) := by
    intro X y
    have hEq := hι.equalizer (T.continuous.comp (continuous_operator I R₁ X))
      ((continuous_operator I R₂ X).comp T.continuous) (funext fun z => by
        obtain ⟨v, rfl⟩ := e.surjective z
        change T (operator I R₁ X (e v : DerivativeSmoothVectors I R₁)) =
          operator I R₂ X (T (e v : DerivativeSmoothVectors I R₁))
        have hX : ((e (π (1 ⊗ₜ[ℝ] X) v) : F) : DerivativeSmoothVectors I R₁) =
            operator I R₁ X (e v : DerivativeSmoothVectors I R₁) := he.2 X v
        rw [← hX, hT, hT]
        exact hf.2 X v)
    exact congrFun hEq y
  have hK : ∀ (k : Matrix.unitaryGroup (Fin (r + 1)) ℝ) (y : DerivativeSmoothVectors I R₁),
      T (DerivativeSmoothVectors.representation I R₁ (Unitary.toUnits k) y) =
        DerivativeSmoothVectors.representation I R₂ (Unitary.toUnits k) (T y) := by
    intro k y
    let A₁ := SmoothAction.derivativeAction I R₁ (Unitary.toUnits k)
    let A₂ := SmoothAction.derivativeAction I R₂ (Unitary.toUnits k)
    have hEq := hι.equalizer (T.continuous.comp A₁.continuous)
      (A₂.continuous.comp T.continuous) (funext fun z => by
        obtain ⟨v, rfl⟩ := e.surjective z
        change T (DerivativeSmoothVectors.representation I R₁ (Unitary.toUnits k)
            (e v : DerivativeSmoothVectors I R₁)) =
          DerivativeSmoothVectors.representation I R₂ (Unitary.toUnits k)
            (T (e v : DerivativeSmoothVectors I R₁))
        have hk : ((e (ρ k v) : F) : DerivativeSmoothVectors I R₁) =
            DerivativeSmoothVectors.representation I R₁ (Unitary.toUnits k)
              (e v : DerivativeSmoothVectors I R₁) := he.1 k v
        rw [← hk, hT, hT]
        exact hf.1 k v)
    exact congrFun hEq y
  intro g y
  exact smoothRealGroupIntertwining (r + 1) E₁ E₂ R₁ R₂ hR₁ hR₂ T hLie hK g y

end Langlands.Archimedean
