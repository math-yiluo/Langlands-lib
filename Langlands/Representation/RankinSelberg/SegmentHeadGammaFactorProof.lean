import Langlands.Representation.RankinSelberg.SegmentFactorStatement
import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Representation.RankinSelberg.ComponentFactorComparisonProof
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePairPoleOrder
import Langlands.Representation.Classification.SegmentHeadTopDerivative
import Langlands.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof

/-! # Gamma factors of actual segment heads -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open CategoryTheory MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData Derivative

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

private def rankCastLinearEquiv {F : PadicField.{uF} p} (T : F.TopologicalData)
    {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear a F.Carrier)) :
    letI := T.topology
    X ≃ₗ[ℂ] (generalLinearRankCast T h).obj X := by
  subst b
  exact LinearEquiv.refl ℂ X

private theorem functional_of_top_nontrivial {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (π : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hnt : letI := T.topology
      Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π)) :
    letI := T.topology
    HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
      (θ := standardCharacter ψ n) π.representation := by
  let := T.topology
  let U := upperUnipotent (n + 1) F.Carrier
  let θ := entrywiseCharacter ψ.complex (n + 1)
  let f := functionalsLocalizationDualEquiv U θ π.representation
  let e := (SmoothRep.equivOfIso
    ((TopLocalization.topLocalizationIso T ψ (n + 1)).app π)).toLinearEquiv
  let r := rankCastLinearEquiv T (Nat.sub_self (n + 1))
    ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π)
  have hQ := (Equiv.nontrivial_congr e.toEquiv).mpr
    ((Equiv.nontrivial_congr r.toEquiv).mp hnt)
  have hdual := (Module.nontrivial_dual_iff ℂ).mpr hQ
  have hfun := (Equiv.nontrivial_congr f.toEquiv).mpr hdual
  let := hfun
  obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : functionals U θ π.representation)
  rw [← entrywiseCharacter_eq_standardCharacter]
  exact ⟨ℓ, fun hzero => hℓ (Subtype.ext hzero)⟩

private theorem rescale_zero (q : ℕ) (hq : 1 < q) (G : RationalFunctions) :
    rationalRescale (spectralShiftUnit q hq 0) G = G := by
  have hs : spectralShiftUnit q hq 0 = 1 := by
    apply Units.ext
    simp [spectralPoint]
  rw [hs, rationalRescale_num_div_denom]
  simp

private theorem ordered_balanced_twist {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (u : ℝ) {G : RationalFunctions} (h : IsPadicPairGammaFactor F ψ ν π σ G) :
    IsPadicPairGammaFactor F ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) u π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n + 1)) (-u) σ) G := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let χ := realPowerCharacter T.normalizedAbsUnits u
  have hneg : T.normalizedAbs (-1) = 1 := by
    change normalizedAbsoluteValue T (-1) = 1
    simp
  have hs : χ (-1) = 1 := by
    apply Units.ext
    simp [χ, T.normalizedAbsUnits_coe, hneg]
  have hi : χ⁻¹ (-1) = 1 := by simp [hs]
  have hp (x : F.Carrierˣ) :
      (χ x : ℂ) * (χ⁻¹ x : ℂ) =
        ((normalizedAbsoluteValue T) (x : F.Carrier) : ℂ) ^ (0 : ℂ) := by
    simp
  have ht := UnramifiedGammaTwist.pair_factor T.residueCardinality
    T.residueCardinality_gt_one ψ (normalizedAbsoluteValue T) ν
    χ χ⁻¹ 0 hs hi hp π σ h
  rw [rescale_zero] at ht
  change IsPairGammaFactor T.residueCardinality ψ (normalizedAbsoluteValue T) ν
    (twist ((realPowerCharacter T.normalizedAbsUnits u).comp determinant) π)
    (twist ((realPowerCharacter T.normalizedAbsUnits (-u)).comp determinant) σ) G
  rw [realPowerCharacter_neg]
  exact ht

/-- Opposite real determinant twists preserve the arbitrary-rank gamma certificate. -/
theorem isPadicRankGammaFactor_realPowerTwist {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (u : ℝ) (G : RationalFunctions) :
    IsPadicRankGammaFactor F ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) u π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) (-u) σ) G ↔
    IsPadicRankGammaFactor F ψ ν π σ G := by
  cases n with
  | zero => rfl
  | succ r =>
    cases t with
    | zero => rfl
    | succ n =>
      simp only [IsPadicRankGammaFactor]
      have forward (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) (u : ℝ)
          (h : IsPadicSymmetricGammaFactor F ψ ν π σ G) :
          IsPadicSymmetricGammaFactor F ψ ν
            (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) u π)
            (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n + 1)) (-u) σ) G := by
        by_cases hnr : n ≤ r
        · rw [isPadicSymmetricGammaFactor_of_le hnr] at h ⊢
          exact ordered_balanced_twist ψ ν π σ u h
        · rw [isPadicSymmetricGammaFactor_of_lt (Nat.lt_of_not_ge hnr)] at h ⊢
          simpa only [neg_neg] using ordered_balanced_twist ψ ν σ π (-u) h
      constructor
      · intro h
        simpa only [realPowerTwist_neg_cancel, neg_neg, realPowerTwist_cancel_neg] using
          forward _ _ (-u) h
      · exact forward π σ u

/-- Move a real determinant twist from the second member to the first. -/
theorem isPadicRankGammaFactor_realPowerTwist_move {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (x y : ℝ) (G : RationalFunctions) :
    IsPadicRankGammaFactor F ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) x π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) y σ) G ↔
    IsPadicRankGammaFactor F ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) (x + y) π) σ G := by
  rw [← isPadicRankGammaFactor_realPowerTwist ψ ν
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) (x + y) π) σ (-y) G,
    ← realPowerTwist_add, neg_neg, show -y + (x + y) = x by ring]

private theorem component_of_surjective {K : Type*} [Group K]
    {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ξ : Representation ℂ K X} {π : Representation ℂ K Y}
    (hirr : Representation.IsIrreducible π)
    (q : ξ.IntertwiningMap π) (hq : Function.Surjective q) :
    IsIrreducibleComponent ξ π := by
  let i : (⊤ : Subrepresentation ξ).toRepresentation.IntertwiningMap ξ :=
    { toLinearMap := (⊤ : Subrepresentation ξ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  refine ⟨hirr, ⊤, q.comp i, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hq y
  exact ⟨⟨x, by trivial⟩, hx⟩

set_option maxHeartbeats 1000000 in
private theorem component_of_segmentInduced {F : PadicField.{uF} p} {a m : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (a + 1) F.Carrier))
    {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear ((m + 1) * a + m + 1) F.Carrier) X)
    (hr : ∑ _i : Fin (m + 1), (a + 1) = (m + 1) * a + m + 1)
    (h : letI := F.canonicalTopologicalData.topology
      IsIrreducibleComponent
        (F.canonicalTopologicalData.segmentInduced A (m + 1) (Nat.succ_pos a)).representation π) :
    letI := F.canonicalTopologicalData.topology
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (fun i : Fin (m + 1) =>
          realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
            (i : ℕ) A.representation)) π := by
  let := F.canonicalTopologicalData.topology
  have hfac : (fun i => (F.canonicalTopologicalData.segmentFactors A (m + 1)
        (Nat.succ_pos a) i).representation) =
      fun i : Fin (m + 1) => realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1))
        (i : ℕ) A.representation :=
    funext fun i => rfl
  have h1 : IsIrreducibleComponent
      (F.canonicalTopologicalData.normalizedProductInduced
        (GeneralLinear.BlockShape.uniform (m + 1) (a + 1) (Nat.succ_pos a))
        (fun i => (F.canonicalTopologicalData.segmentFactors A (m + 1)
          (Nat.succ_pos a) i).representation)) π := h
  rw [hfac] at h1
  exact h1

set_option maxHeartbeats 1000000 in
/-- Henniart's gamma double-product formula for arbitrary supplied segment heads. -/
theorem segmentHeadGammaFactor :
    SegmentHeadGammaFactorStatement.{uF,uV,uW} := by
  intro p _ F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  have hπD := Classification.segmentHeadTopDerivativeNontrivial T ψ Δ π hπ
  have hσD := Classification.segmentHeadTopDerivativeNontrivial T ψ Δ' σ hσ
  have hπi := hπ.isIrreducible
  have hσi := hσ.isIrreducible
  have hπa := hπ.isAdmissible
  have hσa := hσ.isAdmissible
  have hπc : IsIrreducibleComponent
      (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation π.representation := by
    obtain ⟨hi, q, hq, -⟩ := (T.isSegmentHead_iff Δ π A hA).mp hπ
    exact component_of_surjective hi q hq
  have hσc : IsIrreducibleComponent
      (T.segmentInduced A'.obj Δ'.length Δ'.rank_pos).representation σ.representation := by
    obtain ⟨hi, q, hq, -⟩ := (T.isSegmentHead_iff Δ' σ A' hA').mp hσ
    exact component_of_surjective hi q hq
  clear hπ hσ hA hA'
  obtain ⟨⟨d, hd, cls⟩, n, hn⟩ := Δ
  obtain ⟨⟨d', hd', cls'⟩, n', hn'⟩ := Δ'
  obtain ⟨a, rfl⟩ : ∃ a, d = a + 1 := ⟨d - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, d' = b + 1 := ⟨d' - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
  have hr : ∑ _i : Fin (m + 1), (a + 1) = (m + 1) * a + m + 1 := by simp; ring
  have ht : ∑ _j : Fin (k + 1), (b + 1) = (k + 1) * b + k + 1 := by simp; ring
  let ρ := fun i : Fin (m + 1) =>
    realPowerTwist (T.determinantNorm (a + 1)) (i : ℕ) A.obj.representation
  let τ := fun j : Fin (k + 1) =>
    realPowerTwist (T.determinantNorm (b + 1)) (j : ℕ) A'.obj.representation
  have hρ (i : Fin (m + 1)) : IsOfWhittakerType a (standardCharacter ψ a) (ρ i) :=
    isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov
      ((isSupercuspidal_realPowerTwist_iff (a + 1) _ _).mpr A.property.2)
      ((isIrreducible_twist_iff _ _).mpr A.property.1)
  have hτ (j : Fin (k + 1)) : IsOfWhittakerType b (standardCharacter ψ b) (τ j) :=
    isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov
      ((isSupercuspidal_realPowerTwist_iff (b + 1) _ _).mpr A'.property.2)
      ((isIrreducible_twist_iff _ _).mpr A'.property.1)
  obtain ⟨H, hH, hprod⟩ := TemperedLFactorGamma.gamma_doubleProduct F ψ ν
    (fun _ : Fin (m + 1) => a) (fun _ : Fin (k + 1) => b) hr ht ρ τ hρ hτ
  have hπg : IsGeneric ψ ((m + 1) * a + m) π.representation :=
    ⟨hπi, hπa, functional_of_top_nontrivial T ψ _ π hπD⟩
  have hσg : IsGeneric ψ ((k + 1) * b + k) σ.representation :=
    ⟨hσi, hσa, functional_of_top_nontrivial T ψ _ σ hσD⟩
  have hG := genericSymmetricGammaFactor_isPadic F ψ ν.val ν.property
    π.representation σ.representation hπg hσg
  have hπc' := component_of_segmentInduced A.obj π.representation hr hπc
  have hσc' := component_of_segmentInduced A'.obj σ.representation ht hσc
  have hξ := (normalizedProductWhittakerType p F ψ ((m + 1) * a + m)
    (m + 1) (fun _ => a) hr ρ hρ).1.1
  have hη := (normalizedProductWhittakerType p F ψ ((k + 1) * b + k)
    (k + 1) (fun _ => b) ht τ hτ).1.1
  have heq := (componentFactorComparison p F ψ ν.val
    ((m + 1) * a + m) ((k + 1) * b + k) π.representation σ.representation
    (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr) ρ)
    (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => b) ht) τ)
    hξ hη hπc' hσc').1
      _ _ hG hprod
  refine ⟨∏ i, ∏ j, H i j, H, ?_, ?_, rfl⟩
  · exact heq ▸ hG
  · intro i j
    have h := (isPadicRankGammaFactor_realPowerTwist_move ψ ν.val
      A.obj.representation A'.obj.representation (i : ℕ) (j : ℕ) (H i j)).mp (hH i j)
    simpa only [Nat.cast_add] using h

end Langlands.RankinSelberg
