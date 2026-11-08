import Langlands.Representation.RankinSelberg.CenteredSegmentReflectedGamma
import Langlands.Representation.RankinSelberg.CenteredSegmentSupercuspidalProduct
import Langlands.Representation.RankinSelberg.TemperedLFactorDual
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.Whittaker.FiniteProductCriterion
import Langlands.Representation.Whittaker.Transport

/-! # Gamma assembly on actual positive block shapes -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Polynomial Classification LocalFactor

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance blockGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance blockGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance blockGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance blockGammaGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- Certified whole and block polynomials, a reflected ratio, and the actual
whole gamma expression, on the supplied positive block shapes. -/
def HasBlockShapeReflectedGammaData {r t : ℕ}
    (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j)) : Prop :=
  ∃ (P Pd : ℂ[X]) (Q Qd : Fin B.length → Fin C.length → ℂ[X]),
    IsPadicSymmetricLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced B π)
      (F.canonicalNormalizedProductInduced C σ) P ∧
    IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      ((F.canonicalNormalizedProductInduced B π).comp
        (inverseTranspose (r + 1) F.Carrier).toMonoidHom)
      ((F.canonicalNormalizedProductInduced C σ).comp
        (inverseTranspose (t + 1) F.Carrier).toMonoidHom) Pd ∧
    (∀ i j, IsPadicRankLPolynomial F ψ ν.val (π i) (σ j) (Q i j)) ∧
    (∀ i j, IsPadicRankLPolynomial F (ψ.scale (-1)) ν.val
      ((π i).comp (inverseTranspose (B.size i) F.Carrier).toMonoidHom)
      ((σ j).comp (inverseTranspose (C.size j) F.Carrier).toMonoidHom) (Qd i j)) ∧
    Nonempty (TemperedLFactorGamma.ReflectedRatioData (residueReflection F)
      P Pd (∏ i, ∏ j, Q i j) (∏ i, ∏ j, Qd i j)) ∧
    ∀ G : RatFunc ℂ, IsPadicSymmetricGammaFactor F ψ ν.val
      (F.canonicalNormalizedProductInduced B π)
      (F.canonicalNormalizedProductInduced C σ) G →
      HasRationalGammaExpression (residueReflection F) P Pd G

/-- Reduce each positive size function to successors once, then reuse the
published two-family original, dual, and gamma constructions. -/
theorem hasBlockShapeReflectedGammaData {r t : ℕ}
    (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j))
    (hiπ : ∀ i, (π i).IsIrreducible) (haπ : ∀ i, IsAdmissible (π i))
    (hfπ : ∀ i, HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
      (θ := entrywiseCharacter ψ.complex (B.size i)) (π i))
    (hiσ : ∀ j, (σ j).IsIrreducible) (haσ : ∀ j, IsAdmissible (σ j))
    (hfσ : ∀ j, HasFunctional (N := upperUnipotent (C.size j) F.Carrier)
      (θ := entrywiseCharacter ψ.complex (C.size j)) (σ j)) :
    HasBlockShapeReflectedGammaData F ψ ν B C π σ := by
  classical
  obtain ⟨k, size, pos, total⟩ := B
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => by
      have := pos i
      show size i = size i - 1 + 1
      omega⟩
  obtain ⟨l, size', pos', total'⟩ := C
  obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
    ⟨fun j => size' j - 1, funext fun j => by
      have := pos' j
      show size' j = size' j - 1 + 1
      omega⟩
  have hπ (i) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i) := by
    have h : HasFunctional (N := upperUnipotent (m i + 1) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (m i + 1)) (π i) := hfπ i
    rw [entrywiseCharacter_eq_standardCharacter] at h
    exact isOfWhittakerType_of_isGeneric F ⟨hiπ i, haπ i, h⟩
  have hσ (j) : IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j) := by
    have h : HasFunctional (N := upperUnipotent (n j + 1) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (n j + 1)) (σ j) := hfσ j
    rw [entrywiseCharacter_eq_standardCharacter] at h
    exact isOfWhittakerType_of_isGeneric F ⟨hiσ j, haσ j, h⟩
  let d := TemperedLFactorDivisibility.twoFamilyLPolynomialData
    F ψ ν m n total total' π σ hπ hσ
  obtain ⟨dd⟩ := TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData
    F ψ ν m n total total' π σ hπ hσ
  have hr := TemperedLFactorGamma.nonempty_reflectedRatioData
    F ψ ν m n total total' π σ hπ hσ
    d.inducedPolynomial dd.inducedPolynomial d.blockPolynomial dd.blockPolynomial
    d.induced_spec d.block_spec dd.induced_spec dd.block_spec
  refine ⟨d.inducedPolynomial, dd.inducedPolynomial, d.blockPolynomial,
    dd.blockPolynomial, d.induced_spec, dd.induced_spec, d.block_spec, dd.block_spec,
    hr, ?_⟩
  intro G hG
  have hπind := normalizedProductWhittakerType p F ψ r k m total π hπ
  have hσind := normalizedProductWhittakerType p F ψ t l n total' σ hσ
  obtain ⟨e, he⟩ := TemperedLFactorGamma.epsilon_exists_of_whittakerType
    F ψ ν _ _ hπind hσind
  refine ⟨e.1, e.2, ?_⟩
  exact (symmetricGammaExpression p F ψ ν r t _ _
    (whittakerTypeGammaConstructionInput p F ψ ν r t _ _ _ _ hπind hσind)
    e d.inducedPolynomial dd.inducedPolynomial he d.induced_spec dd.induced_spec G).mp hG

/-- A positive-rank irreducible admissible block with an entrywise functional
has such a functional on its actual smooth dual, for the same character. -/
theorem hasEntrywiseFunctional_smoothContragredient {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hirr : π.IsIrreducible) (hadm : IsAdmissible π)
    (hf : HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n) π) :
    HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n) (smoothContragredient π) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [entrywiseCharacter_eq_standardCharacter] at hf ⊢
    have h := isOfWhittakerType_of_isGeneric F ⟨hirr, hadm, hf⟩
    exact (isOfWhittakerType_smoothContragredient_inverse F π ψ
      ((isOfWhittakerType_standard_iff_inverse ψ π).mp h) hirr).exists_ne_zero

/-- Whole-product genericity supplies the mixed block certificates needed for
the centered gamma germ. The second whole representation is the normalized
product of the actual smooth duals of the twisted blocks. -/
theorem centeredSegmentFamilyGammaGerm_of_blockShape
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {r : ℕ} (B : BlockShape (r + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hirr : ∀ i, (δ i).IsIrreducible)
    (hadm : ∀ i, (δ i).IsAdmissible)
    (hf : HasFunctional (N := upperUnipotent (r + 1) F.Carrier)
      (θ := standardCharacter ψ r)
      (F.canonicalTopologicalData.twistedProductInduced B δ s).representation)
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val
      (F.canonicalTopologicalData.twistedProductInduced B δ s).representation
      (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).contragredient.representation))
      G) :
    ∃ (c : ℂˣ) (m : ℤ), IsCenteredSegmentFamilyGammaGerm F d s G
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal)
      (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) := by
  let A := F.canonicalTopologicalData.twistedBlocks B δ s
  have hiA (i) : (A i).IsIrreducible :=
    (Langlands.isIrreducible_twist_iff _ _).mpr (hirr i)
  have haA (i) : (A i).IsAdmissible :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter
        (B.size i) (s i))).mpr (hadm i)
  have hfA := (hasStandardFunctional_finiteProduct_iff
    F.canonicalTopologicalData ψ r B A).mp hf
  have hiAd (i) : (A i).contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff
      (compactOpen_cofinal F F.canonicalTopologicalData (B.size i)) (A i) (haA i)).mpr
      (hiA i)
  have haAd (i) : (A i).contragredient.IsAdmissible :=
    (SmoothRep.isAdmissible_contragredient_iff
      (compactOpen_cofinal F F.canonicalTopologicalData (B.size i)) (A i)).mpr (haA i)
  have hfAd (i) := hasEntrywiseFunctional_smoothContragredient F ψ (B.positive i)
    (A i).representation (hiA i) (haA i) (hfA i)
  obtain ⟨P, Pd, Q, Qd, _, _, hQ, hQd, ⟨ratio⟩, hExpr⟩ :=
    hasBlockShapeReflectedGammaData F ψ ν B B
      (fun i => (A i).representation) (fun i => (A i).contragredient.representation)
      hiA haA hfA hiAd haAd hfAd
  exact centeredSegmentFamilyGammaGerm_of_reflectedRatio
    F ψ ν (ψ.scale (-1)) (DominantRankTransport.negatedSelfDualHaar F ψ ν)
    d hH hEq hadm hirr s Q Qd hQ hQd (hExpr G hG) ratio

/-- The actual mixed-product gamma germ and its real-axis order restriction
force an equivalence of the supplied action to a unitary supercuspidal product. -/
theorem unitarySupercuspidalProduct_of_blockShapeGamma
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {r : ℕ} (B : BlockShape (r + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hU : IsUnitaryGenericDatum F F.canonicalTopologicalData B δ s)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (e : ρ.Equiv (F.canonicalTopologicalData.twistedProductInduced B δ s).representation)
    (hf : HasFunctional (N := upperUnipotent (r + 1) F.Carrier)
      (θ := standardCharacter ψ r) ρ)
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val
      (F.canonicalTopologicalData.twistedProductInduced B δ s).representation
      (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).contragredient.representation))
      G)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    IsUnitarySupercuspidalProduct.{uF, uW, uX} F F.canonicalTopologicalData B ρ := by
  have hpos : 0 < B.length := by
    by_contra h
    have hz : B.length = 0 := by omega
    have hs := B.sum_eq
    simp [hz] at hs
  let : Nonempty (Fin B.length) := ⟨⟨0, hpos⟩⟩
  obtain ⟨c, m, hgerm⟩ := centeredSegmentFamilyGammaGerm_of_blockShape
    F ψ ν hH hEq B δ s d (fun i => (hU.1 i).1)
      (fun i => (hU.1 i).2.2.isAdmissible)
      ((hasFunctional_iff_of_equiv e).mp hf) hG
  obtain ⟨partner, hs, _, hb⟩ :=
    exists_symmetric_centeredSegmentBaseEulerFamily hEq ψ ν hU d
  have hr := IsCenteredSegmentFamilyGammaGerm.segmentRigidity F d hgerm partner hs hb
    (fun t => epsilonMonomial_holomorphicUnitAt F c m (t : ℂ)) hzero
  exact unitarySupercuspidalProduct_of_length_one_zero_exponents
    F F.canonicalTopologicalData B δ s d (fun i => (hU.1 i).2.1)
    (fun i => (hr i).1) (fun i => (hr i).2) ρ e

end Langlands.RankinSelberg
