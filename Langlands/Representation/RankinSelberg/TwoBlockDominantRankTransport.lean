import Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.Representation.Induction.OppositeProductReversalProof

/-!
# Transport for the dominant-rank parent proof

Internal assembly tools. The lower analytic gamma and L conclusions remain open.
This file only transports supplied certificates along the published actual
normalized induction equivalence, reversing the complete dependent block family.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open GeneralLinear HarmonicAnalysis MeasureTheory Polynomial Whittaker

universe uF uV uW

theorem reverseSum {t : ℕ} (m : Fin 2 → ℕ)
    (h : ∑ i, (m i + 1) = t + 1) :
    ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
  (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- The lower representation with the complete dependent block family reversed. -/
abbrev lowerReversed :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  letI : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
  letI : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev
  TwoBlockJacquet.inducedRep F (reverseSum m h) (fun i => σ i.rev)

/-- Reverse sizes, carriers and representations in the lower induction, then
use the actual normalized equivalence to recover the original upper product. -/
theorem lowerReversedToUpperEquiv
    (hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSmooth (σ i)) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    letI : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev
    Nonempty (Representation.Equiv
      (lowerReversed F m h σ)
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  let : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev
  obtain ⟨E, _, _⟩ := glOppositeProductReversal p F F.canonicalTopologicalData
    (t + 1) (succBlockShape (fun i => m i.rev) (reverseSum m h))
    (fun i => W i.rev) (fun i => σ i.rev) (fun i => hs i.rev)
  let Q (e : Equiv.Perm (Fin 2)) : Prop :=
    let B : BlockShape (t + 1) :=
      { length := 2
        size := fun i => m (e i) + 1
        positive := fun i => Nat.succ_pos (m (e i))
        sum_eq := (Equiv.sum_comp e (fun i => m i + 1)).trans h }
    letI : ∀ i : Fin 2, AddCommGroup (W (e i)) := fun i => hadd (e i)
    letI : ∀ i : Fin 2, Module ℂ (W (e i)) := fun i => hmod (e i)
    Nonempty (Representation.Equiv
      (TwoBlockJacquet.inducedRep F (reverseSum m h) (fun i => σ i.rev))
      (F.canonicalNormalizedProductInduced B (fun i => σ (e i))))
  have hQ : Q (Fin.revPerm.trans Fin.revPerm) := ⟨E⟩
  have he : (Fin.revPerm.trans Fin.revPerm : Equiv.Perm (Fin 2)) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [he] at hQ
  exact hQ

variable
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier;
    AdditiveHaarMeasure F.Carrier}
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)

/-- Reindex supplied lower gamma certificates and transport the induced-pair
certificate along the actual normalized representation equivalence. -/
theorem gammaConclusion
    (hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSmooth (σ i))
    (hLower : ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν π (σ i.rev) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν π (lowerReversed F m h σ) (∏ i, G i)) :
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, G i) := by
  obtain ⟨G, hG, hInd⟩ := hLower
  obtain ⟨E⟩ := lowerReversedToUpperEquiv F m h σ hs
  refine ⟨fun i => G i.rev, ?_, ?_⟩
  · intro i
    exact (congrArg
      (fun j => IsPadicSymmetricGammaFactor F ψ ν π (σ j) (G i.rev))
      (Fin.rev_rev i)).mp (hG i.rev)
  · have hp : (∏ i : Fin 2, G i.rev) = ∏ i : Fin 2, G i :=
      Equiv.prod_comp Fin.revPerm G
    rw [hp]
    exact (IsPadicSymmetricGammaFactor.congr_equiv
      (Representation.Equiv.refl π) E).1 hInd

/-- Transport supplied lower L-polynomial certificates without altering the
direction of the polynomial divisibility or its witnesses. -/
theorem lConclusion
    (hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSmooth (σ i))
    (hLower : ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν π (lowerReversed F m h σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν π (σ i.rev) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P) :
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P := by
  obtain ⟨P, Pi, hInd, hPi, Q, e, hdiv⟩ := hLower
  obtain ⟨E⟩ := lowerReversedToUpperEquiv F m h σ hs
  refine ⟨P, fun i => Pi i.rev, ?_, ?_, Q, e, ?_⟩
  · exact (IsPadicSymmetricLPolynomial.congr_equiv
      (Representation.Equiv.refl π) E).1 hInd
  · intro i
    exact (congrArg
      (fun j => IsPadicSymmetricLPolynomial F ψ ν π (σ j) (Pi i.rev))
      (Fin.rev_rev i)).mp (hPi i.rev)
  · have hp : (∏ i : Fin 2, Pi i.rev) = ∏ i : Fin 2, Pi i :=
      Equiv.prod_comp Fin.revPerm Pi
    rwa [hp]

end Langlands.RankinSelberg.DominantRankTransport

namespace Langlands.RankinSelberg.DominantRankTransport

open GeneralLinear HarmonicAnalysis MeasureTheory Polynomial Whittaker

universe uF uV uW

/-- Every block is strictly smaller than the test rank, even when the induced
rank equals the test rank. This is only a consequence of the two positive blocks. -/
theorem block_lt_of_dominant {r t : ℕ} (m : Fin 2 → ℕ)
    (h : ∑ i, (m i + 1) = t + 1) (htr : t ≤ r) (i : Fin 2) :
    m i < r := by
  have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  fin_cases i
  · change m 0 < r
    omega
  · change m 1 < r
    omega

/-- The missing Section 4 gamma conclusion for the actual lower induction.
This proposition is an unproved conditional interface. -/
def LowerGammaDominantInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
    t ≤ r →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        (TwoBlockJacquet.inducedRep F h σ) (∏ i, G i)

/-- The missing Section 4 L conclusion for the actual lower induction.
The polynomial equation is in the same direction as the published target. -/
def LowerLDominantInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
    t ≤ r →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (TwoBlockJacquet.inducedRep F h σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P

/-- The actual lower gamma conclusion would imply the exact published dominant
target, with no common-universe restriction or extra representation premise. -/
theorem gammaDominant_of_lower
    (hLower : LowerGammaDominantInput.{uF, uV, uW}) :
    TwoBlockGammaDominantRankStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t m h V _ _ W hadd hmod π σ htr hπ hσ
  have hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSmooth (σ i) :=
    fun i => (hσ i).1.1
  let : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev
  exact gammaConclusion F m h σ π hs
    (hLower p F ψ ν r t (fun i => m i.rev) (reverseSum m h)
      π (fun i => σ i.rev) htr hπ (fun i => hσ i.rev))

/-- The actual lower L conclusion would imply the exact published dominant
target, preserving its polynomial witnesses and independent universes. -/
theorem lDominant_of_lower
    (hLower : LowerLDominantInput.{uF, uV, uW}) :
    TwoBlockLDominantRankStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t m h V _ _ W hadd hmod π σ htr hπ hσ
  have hs : ∀ i, letI := F.canonicalTopologicalData.topology; IsSmooth (σ i) :=
    fun i => (hσ i).1.1
  let : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev
  exact lConclusion F m h σ π hs
    (hLower p F ψ ν r t (fun i => m i.rev) (reverseSum m h)
      π (fun i => σ i.rev) htr hπ (fun i => hσ i.rev))

end Langlands.RankinSelberg.DominantRankTransport
