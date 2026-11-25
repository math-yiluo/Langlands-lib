import Langlands.Automorphic.ComplexPlaceParameterHeckeTwist
import Langlands.Automorphic.ContragredientSymmetry
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof
import Langlands.Automorphic.CuspidalInvariantPairingCriterion
import Langlands.Automorphic.CuspidalOperatorUnitaryMultiplicityOneReduction
import Langlands.Automorphic.CuspidalSpectralUniverseLift
import Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof
import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.OperatorDeterminantUnitary
import Langlands.Automorphic.Unramified.CyclicCuspidalCommonNormalization
import Langlands.Automorphic.Unramified.CyclicCuspidalPairProduct

/-! # The cyclic cuspidal fibre from the local norm order and partial pair pole orders -/

noncomputable section

universe uF uE uS uT

set_option autoImplicit false

open scoped NumberField

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Global.CuspidalPairBoundaryNonvanishing (IsPartialPairLFunction)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type uF} [Field F] [NumberField F]

section Twists

open ContinuousRationalFunctions

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

private theorem heckeDeterminantTwist_comm {n : ℕ}
    (S : OperatorRealization F n) (μ χ : HeckeCharacter F) :
    (S.heckeDeterminantTwist μ).heckeDeterminantTwist χ =
      (S.heckeDeterminantTwist χ).heckeDeterminantTwist μ := by
  let M := (StableAutomorphicFunctions.heckeDeterminantMultiplier n μ).toLinearMap
  let C := (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).toLinearMap
  have hcomm : C ∘ₗ M = M ∘ₗ C := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply toContinuousMap_injective F n
    ext g
    change evaluate F n (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ
      (StableAutomorphicFunctions.heckeDeterminantMultiplier n μ f)).val.val g =
      evaluate F n (StableAutomorphicFunctions.heckeDeterminantMultiplier n μ
        (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ f)).val.val g
    simp only [StableAutomorphicFunctions.evaluate_heckeDeterminantMultiplier]
    rw [← mul_assoc, mul_comm (χ.adelicDeterminant n g : ℂ), mul_assoc]
  apply Subrepresentation.toSubmodule_injective
  change (S.toSubmodule.map M).map C = (S.toSubmodule.map C).map M
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

private theorem finiteOrderDeterminantTwist_of_commonTwist {n : ℕ}
    {S T : OperatorRealization F n} (μ χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (e : ((S.heckeDeterminantTwist μ).heckeDeterminantTwist χ).Equivalence
      (T.heckeDeterminantTwist μ)) : S.IsFiniteOrderDeterminantTwist χ T := by
  have he : Nonempty ((((S.heckeDeterminantTwist μ).heckeDeterminantTwist χ).heckeDeterminantTwist
      μ⁻¹).Equivalence ((T.heckeDeterminantTwist μ).heckeDeterminantTwist μ⁻¹)) :=
    ⟨e.heckeDeterminantTwist μ⁻¹⟩
  rw [heckeDeterminantTwist_comm S μ χ, OperatorRealization.heckeDeterminantTwist_heckeDeterminantTwist_inv,
    OperatorRealization.heckeDeterminantTwist_heckeDeterminantTwist_inv] at he
  have hχtw := (OperatorRealization.isDeterminantMultiple_heckeDeterminantTwist S χ).isFiniteOrderDeterminantTwist hχ
  have htrivial := OperatorRealization.isFiniteOrderDeterminantTwist_one_iff.mpr he
  simpa only [mul_one χ] using hχtw.trans htrivial

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

end Twists

private theorem unitaryCentralCharacter_heckeDeterminantTwist
    [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T) {χ : HeckeCharacter F} (hχ : χ.IsUnitary) :
    HasUnitaryCentralCharacter (T.heckeDeterminantTwist χ) := by
  obtain ⟨ω, hω, hωT⟩ := hT
  refine ⟨χ ^ (r + 1) * ω, ?_, ?_⟩
  · intro x
    simp only [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hχ x, hω x, one_pow, mul_one]
  · change (T.realization.heckeDeterminantTwist χ).toFiniteRealization.HasCentralCharacter _
    rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
    exact T.realization.toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter χ ω hωT

/-- The exact cyclic cuspidal fibre follows from local orders of a norm-trivial
character, existence of partial pair L-functions and their same-rank orders at one. -/
def CyclicCuspidalFiberReductionStatement : Prop :=
  CuspidalPairBoundaryNonvanishingStatement.{uF, max uS uT} →
  (∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    ∃ η : HeckeCharacter F, η.IsTrivialOnNorm E ∧
      ∀ᶠ v in Filter.cofinite, ∀ w : FinitePlacesAbove E v,
        orderOf (η.finiteUniformizerValue v) = w.1.asIdeal.inertiaDeg (𝓞 F)) →
  (∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T V : CuspidalOperatorRealization F r),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter V →
    ∀ (P : CuspidalSpectralPresentation.{uF, max uS uT} T)
      (R : CuspidalSpectralPresentation.{uF, max uS uT} V)
      (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hR : R.exceptional ⊆ S)
      (L : ℂ → ℂ), IsPartialPairLFunction P R hP hR L →
      (T.realization.IsContragredientOf V.realization → meromorphicOrderAt L 1 = -1) ∧
        (¬ T.realization.IsContragredientOf V.realization → meromorphicOrderAt L 1 = 0)) →
  CyclicCuspidalFiberStatement.{uF, uE, uS, uT}

/-- The norm-character and pole-order reduction of Arthur–Clozel III.3.1. -/
theorem cyclicCuspidalFiberReduction : CyclicCuspidalFiberReductionStatement.{uF, uE, uS, uT} := by
  classical
  intro hexists hnorm horder F E _ _ _ _ _ _ _ _ r c c' s t hs ht hst
  obtain ⟨T, P, rfl, rfl⟩ := hs
  obtain ⟨U, Q, rfl, rfl⟩ := ht
  obtain ⟨μ, hT, hU, hpowers⟩ := cyclicCuspidalCommonNormalization F E r T U P Q hst
  let T₀ := T.heckeDeterminantTwist μ
  let U₀ := U.heckeDeterminantTwist μ
  let P₀ := (P.heckeDeterminantTwist μ).universeLift.{uT}
  let Q₀ := (Q.heckeDeterminantTwist μ).universeLift.{uS}
  obtain ⟨V, hVdual, hV⟩ := cuspidalUnitaryContragredientExistence F r U₀ hU
  have hUdual : U₀.realization.IsContragredientOf V.realization := CuspidalOperatorRealization.isContragredientOf_symm hVdual
  obtain ⟨R, -⟩ := cuspidalContragredientPresentationExistence.{uF, max uS uT, max uS uT}
    F r U₀ V hU hVdual Q₀
  obtain ⟨η, hη, hlocal⟩ := hnorm F E
  let d := Module.finrank F E
  have hpow : η ^ d = 1 := hη.pow_finrank_eq_one E
  have hlocalProduct : ∀ᶠ v in Filter.cofinite,
      ∃ (hp : v ∉ P₀.exceptional) (hq : v ∉ Q₀.exceptional) (f : ℕ),
        0 < f ∧ f ∣ d ∧ IsPrimitiveRoot (η.finiteUniformizerValue v) f ∧
          (P₀.spectralSystem.eigenvalues v hp).power f = (Q₀.spectralSystem.eigenvalues v hq).power f := by
    filter_upwards [hpowers, hlocal] with v hv horder_v
    obtain ⟨hp, hq, hv⟩ := hv
    let w := placeAbove E v
    let f := w.1.asIdeal.inertiaDeg (𝓞 F)
    have hf : 0 < f := w.1.asIdeal.inertiaDeg_pos (𝓞 F)
    have hζ : IsPrimitiveRoot (η.finiteUniformizerValue v) f := by
      dsimp only [f]
      rw [← horder_v w]
      exact IsPrimitiveRoot.orderOf _
    have hζpow : η.finiteUniformizerValue v ^ d = 1 := by
      let x := finiteClassInclusion F v
        (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit
      have hx := congrArg (fun χ : HeckeCharacter F => χ x) hpow
      change (η x) ^ d = 1
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using hx
    exact ⟨hp, hq, f, hf, (hζ.pow_eq_one_iff_dvd d).mp hζpow, hζ, (hv w).2⟩
  obtain ⟨S, hR, hP₀, hQ₀, hcomparison⟩ :=
    cyclicCuspidalPairProduct.{uF, max uS uT} F r r T₀ U₀ V P₀ Q₀ R η d hlocalProduct
  let χ (i : Fin d) := η ^ (i : ℕ)
  have hn (i : Fin d) : (χ i).IsTrivialOnNorm E := by
    intro x
    dsimp only [χ]
    rw [ContinuousMonoidHom.pow_apply, hη x, one_pow]
  have hTP (i : Fin d) : HasUnitaryCentralCharacter (T₀.heckeDeterminantTwist (χ i)) :=
    unitaryCentralCharacter_heckeDeterminantTwist hT ((hn i).hasFiniteOrder E).isUnitary
  have hUQ (i : Fin d) : HasUnitaryCentralCharacter (U₀.heckeDeterminantTwist (χ i)) :=
    unitaryCentralCharacter_heckeDeterminantTwist hU ((hn i).hasFiniteOrder E).isUnitary
  choose L hL using fun i => (hexists F r r (T₀.heckeDeterminantTwist (χ i)) V
    (hTP i) hV (P₀.heckeDeterminantTwist (χ i)) R S (hP₀ i) hR).1
  choose M hM using fun i => (hexists F r r (U₀.heckeDeterminantTwist (χ i)) V
    (hUQ i) hV (Q₀.heckeDeterminantTwist (χ i)) R S (hQ₀ i) hR).1
  have hsum := hcomparison L M hL hM
  let j : Fin d := ⟨0, Module.finrank_pos⟩
  have hj : (U₀.heckeDeterminantTwist (χ j)).realization.IsContragredientOf V.realization := by
    change (U₀.realization.heckeDeterminantTwist (χ j)).IsContragredientOf V.realization
    have hjχ : χ j = 1 := pow_zero η
    rw [hjχ, (OperatorRealization.isDeterminantMultiple_one_iff.mp
      (OperatorRealization.isDeterminantMultiple_heckeDeterminantTwist U₀.realization 1)).symm]
    exact hUdual
  have hMj : meromorphicOrderAt (M j) 1 = -1 :=
    (horder F r _ V (hUQ j) hV (Q₀.heckeDeterminantTwist (χ j)) R S (hQ₀ j) hR (M j) (hM j)).1 hj
  have hMnonpos (i : Fin d) : meromorphicOrderAt (M i) 1 ≤ 0 := by
    simpa using (hexists F r r _ V (hUQ i) hV (Q₀.heckeDeterminantTwist (χ i)) R
      S (hQ₀ i) hR).2 (M i) (hM i) 0
  have hMsum : (∑ i, meromorphicOrderAt (M i) 1) ≤ -1 := by
    calc
      (∑ i, meromorphicOrderAt (M i) 1) ≤
          ∑ i : Fin d, if i = j then (-1 : WithTop ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hij
        · exact le_of_eq (hij ▸ hMj)
        · exact hMnonpos i
      _ = -1 := by simp
  have hpole : ∃ i : Fin d,
      (T₀.heckeDeterminantTwist (χ i)).realization.IsContragredientOf V.realization := by
    by_contra! hno
    have hLzero (i : Fin d) : meromorphicOrderAt (L i) 1 = 0 :=
      (horder F r _ V (hTP i) hV (P₀.heckeDeterminantTwist (χ i)) R S
        (hP₀ i) hR (L i) (hL i)).2 (hno i)
    simp only [hLzero, Finset.sum_const_zero] at hsum
    exact (by decide : ¬ ((0 : WithTop ℤ) ≤ -1)) (hsum.trans_le hMsum)
  obtain ⟨i, hi⟩ := hpole
  obtain ⟨e⟩ := hi.nonempty_equivalence hUdual
  exact ⟨χ i, hn i, finiteOrderDeterminantTwist_of_commonTwist μ (χ i) ((hn i).hasFiniteOrder E) e⟩

end Langlands.Automorphic.Unramified
