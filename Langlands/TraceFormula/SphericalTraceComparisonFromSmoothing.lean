import Langlands.BaseChange.RegularElementarySphericalTraceReplacement
import Langlands.TraceFormula.FiniteSmoothingTraceExpansion

/-! # Spherical replacement of factored smoothing traces -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals Langlands.BaseChange
open Langlands.Correspondence Langlands.HarmonicAnalysis Langlands.Unramified
open scoped BigOperators

universe u v uV uW uI uJ uH uK

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

private theorem operatorTrace_smul_mul_positivePower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T A : H →L[ℂ] H) (hT : IsTraceClass T) (d : ℂ) (k : ℕ) :
    operatorTrace ((d • A) * T ^ (k + 1)) = d * operatorTrace (A * T ^ (k + 1)) := by
  rw [smul_mul_assoc]
  apply operatorTrace_smul
  rw [pow_succ, ← mul_assoc]
  exact isTraceClass_postcomp T (A * T ^ k) hT

private theorem compression_trace_smul_mul_positivePower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) [CompleteSpace W] (T A : H →L[ℂ] H) (hT : IsTraceClass T)
    (d : ℂ) (k : ℕ) :
    operatorTrace (summandCompression W ((d • A) * T ^ (k + 1))) =
      d * operatorTrace (summandCompression W (A * T ^ (k + 1))) := by
  have hClass : IsTraceClass (A * T ^ (k + 1)) := by
    rw [pow_succ, ← mul_assoc]
    exact isTraceClass_postcomp T (A * T ^ k) hT
  rw [smul_mul_assoc]
  have h : summandCompression W (d • (A * T ^ (k + 1))) =
      d • summandCompression W (A * T ^ (k + 1)) := by
    ext1 x
    simp [summandCompression]
  rw [h]
  exact operatorTrace_smul _ _ (isTraceClass_compression W _ hClass)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- Local trace factors on the cuspidal summands and agreement of elementary
smoothing moments imply agreement of the final spherical smoothing traces. -/
def SphericalTraceComparisonFromSmoothingStatement : Prop :=
  RegularElementaryJacquetTraceStatement.{u, uW} →
  RegularElementaryJacquetTraceStatement.{v, uV} →
  UnramifiedWeylJacquetSupportStatement.{u, uW} →
  UnramifiedWeylJacquetSupportStatement.{v, uV} →
  UnramifiedGenericSigmaNormalizationStatement.{u, v, uV} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
    IsUnramifiedBaseChangeHom F E l r b →
    ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (K : Type uK) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (I : Type uI) (J : Type uJ) (W : I → Submodule ℂ H) (W' : J → Submodule ℂ K)
      [∀ i, CompleteSpace (W i)] [∀ j, CompleteSpace (W' j)],
    IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ) →
    IsHilbertSum ℂ (fun j => W' j) (fun j => (W' j).subtypeₗᵢ) →
    ∀ (T : H →L[ℂ] H) (T' : K →L[ℂ] K),
    IsTraceClass T → IsTraceClass T' → T.IsSymmetric → T'.IsSymmetric →
    (∀ i x, x ∈ W i → T x ∈ W i) → (∀ j x, x ∈ W' j → T' x ∈ W' j) →
    ∀ (τ : I → I)
      (upper : {i : I // τ i = i} → AutomorphicObject.{v,uV} E r.succPNat)
      (lower : J → AutomorphicObject.{u,uW} F r.succPNat)
      (B : ∀ i, SigmaIntertwiner σ (r + 1) (upper i).obj.representation),
    (∀ i, ∃ ψ : NontrivialAdditiveCharacter E, Whittaker.IsGeneric ψ r (upper i).obj.representation) →
    (∀ j, ∃ ψ : NontrivialAdditiveCharacter F, Whittaker.IsGeneric ψ r (lower j).obj.representation) →
    let X := StrictWeight (r + 1) ⊕ SphericalHeckeAlgebra E r
    let tests (w : StrictWeight (r + 1)) :=
      regularElementaryBaseChangeTests F E σ l hcyc he w.val w.property
    let testE : X → SchwartzBruhat (GeneralLinear (r + 1) E.Carrier) :=
      Sum.elim (fun w => (tests w).1) (fun φ => φ.val)
    let testF : X → SchwartzBruhat (GeneralLinear (r + 1) F.Carrier) :=
      Sum.elim (fun w => (tests w).2) (fun φ => (b φ).val)
    let distE i := twistedDistribution (sphericalHaar E r) (upper i).obj.representation
      (upper i).property.2 (B i).toLinearMap
    let distF j := Character.distribution (sphericalHaar F r) (lower j).obj.representation
      (lower j).property.2
    ∀ (A : X → H →L[ℂ] H) (A' : X → K →L[ℂ] K) (d : ℂ),
    (∀ i,
      (∀ hi : τ i = i, ∃ C : ℕ → ℂ, ∀ x k,
        operatorTrace (summandCompression (W i) (A x * T ^ (k + 1))) =
          distE ⟨i, hi⟩ (testE x) * C k) ∧
      (τ i ≠ i → ∀ x k, summandCompression (W i) (A x * T ^ (k + 1)) = 0)) →
    (∀ j, ∃ C : ℕ → ℂ, ∀ x k,
      operatorTrace (summandCompression (W' j) (A' x * T' ^ (k + 1))) =
        distF j (testF x) * C k) →
    (∀ w k, operatorTrace (A (Sum.inl w) * T ^ (k + 1)) =
      d * operatorTrace (A' (Sum.inl w) * T' ^ (k + 1))) →
    ∀ φ, operatorTrace (A (Sum.inr φ) * T) = d * operatorTrace (A' (Sum.inr φ) * T')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
theorem sphericalTraceComparisonFromSmoothing :
    SphericalTraceComparisonFromSmoothingStatement.{u, v, uV, uW, uI, uJ, uH, uK} := by
  classical
  intro hTraceF hTraceE hWeylF hWeylE hSigma p _ F E _ _ σ l r hcyc he b hb
    H _ _ _ K _ _ _ I J W W' _ _ hW hW' T T' hT hT' hSymm hSymm' hInv hInv'
    τ upper lower B hGenE hGenF X tests testE testF distE distF A A' d hMomE hMomF hMom φ
  let L (i : I) (x : X) : ℂ :=
    if h : τ i = i then distE ⟨i, h⟩ (testE x) else 0
  have hL (i : I) : ∃ C : ℕ → ℂ, ∀ x k,
      operatorTrace (summandCompression (W i) (A x * T ^ (k + 1))) = L i x * C k := by
    by_cases hi : τ i = i
    · obtain ⟨C, hC⟩ := (hMomE i).1 hi
      exact ⟨C, fun x k => by simpa only [L, dite_eq_left hi] using hC x k⟩
    · exact ⟨fun _ => 0, fun x k => by simp only [(hMomE i).2 hi x k, operatorTrace_zero, mul_zero]⟩
  let A'' (x : X) := d • A' x
  have hL' (j : J) : ∃ C : ℕ → ℂ, ∀ x k,
      operatorTrace (summandCompression (W' j) (A'' x * T' ^ (k + 1))) =
        distF j (testF x) * C k := by
    obtain ⟨C, hC⟩ := hMomF j
    refine ⟨fun k => d * C k, fun x k => ?_⟩
    calc
      _ = d * operatorTrace (summandCompression (W' j) (A' x * T' ^ (k + 1))) :=
        compression_trace_smul_mul_positivePower (W' j) T' (A' x) hT' d k
      _ = _ := by rw [hC]; ring
  have hComparable (w : StrictWeight (r + 1)) (k : ℕ) :
      operatorTrace (A (Sum.inl w) * T ^ (k + 1)) =
        operatorTrace (A'' (Sum.inl w) * T' ^ (k + 1)) := by
    exact (hMom w k).trans (operatorTrace_smul_mul_positivePower T' _ hT' d k).symm
  have hFinal := compactOperatorTraceReplacement H K T T' (StrictWeight (r + 1))
    (A ∘ Sum.inl) (A'' ∘ Sum.inl) (A (Sum.inr φ)) (A'' (Sum.inr φ))
    hT hT' hSymm hSymm' hComparable ?_
  · change _ = operatorTrace ((d • A' (Sum.inr φ)) * T') at hFinal
    rw [smul_mul_assoc] at hFinal
    exact hFinal.trans (operatorTrace_smul d (A' (Sum.inr φ) * T')
      (isTraceClass_postcomp T' (A' (Sum.inr φ)) hT'))
  intro z hz hEqual
  obtain ⟨D, c, hD⟩ := finiteSmoothingTraceExpansion H I W hW T X A L hT hSymm hInv hL z hz
  obtain ⟨D', c', hD'⟩ := finiteSmoothingTraceExpansion K J W' hW' T' X A''
    (fun j x => distF j (testF x)) hT' hSymm' hInv' hL' z hz
  let Dfix := D.filter (fun i => τ i = i)
  let incl (i : Dfix) : {i : I // τ i = i} := ⟨i.val, (Finset.mem_filter.mp i.2).2⟩
  have hE (x : X) : eigenspaceTrace T z (A x) =
      ∑ i : Dfix, c i.val * distE (incl i) (testE x) := by
    rw [hD x]
    calc
      _ = ∑ i ∈ Dfix, c i * L i x :=
        (Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hnot => by
          have hn : τ i ≠ i := fun h => hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
          simp only [L, dite_eq_right hn, mul_zero])).symm
      _ = _ := by
        rw [← Finset.sum_coe_sort Dfix (fun i => c i * L i x)]
        exact Finset.sum_congr rfl (fun i _ => by
          have hi : τ i.val = i.val := (Finset.mem_filter.mp i.2).2
          simp only [L, dite_eq_left hi, incl])
  have hF (x : X) : eigenspaceTrace T' z (A'' x) =
      ∑ j : D', c' j.val * distF j.val (testF x) := by
    rw [hD' x]
    exact (Finset.sum_coe_sort D' (fun j => c' j * distF j (testF x))).symm
  rw [hE, hF]
  refine regularElementarySphericalTraceReplacement hTraceF hTraceE hWeylF hWeylE hSigma p F E σ l r hcyc he b hb
    Dfix D' (upper ∘ incl) (fun j => lower j.val) (fun i => B (incl i))
    (fun i => hGenE (incl i)) (fun j => hGenF j.val) (fun i => c i.val) (fun j => c' j.val)
    (fun w => ?_) φ
  simpa only [Function.comp_apply, hE (Sum.inl w), hF (Sum.inl w), distE, distF, testE, testF,
    tests, Sum.elim_inl] using hEqual w

end Langlands.TraceFormula
