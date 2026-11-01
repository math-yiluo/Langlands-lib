import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockIntegrands
import Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Joined row measures and the actual upper first-block coefficient -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent

universe uF uV uW uA uS

section RowMeasure

variable (K : Type uF) [MeasurableSpace K]

/-- Concatenate the Jacquet rows before the external rows, without a
permutation within either rectangle. -/
def firstBlockRowJoinEquiv (a b j : ℕ) :
    (Matrix (Fin b) (Fin a) K × Matrix (Fin j) (Fin a) K) ≃ᵐ
      Matrix (Fin (b + j)) (Fin a) K :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin b ⊕ Fin j => Fin a → K)).symm.trans
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (b + j) => Fin a → K) finSumFinEquiv)

theorem firstBlockRowJoinEquiv_apply (a b j : ℕ)
    (Z : Matrix (Fin b) (Fin a) K) (T : Matrix (Fin j) (Fin a) K) :
    firstBlockRowJoinEquiv K a b j (Z, T) =
      (Matrix.fromRows Z T).submatrix finSumFinEquiv.symm id := by
  ext i l
  change (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (b + j) => Fin a → K) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi _).symm (Z, T)) i l = _
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases i <;> simp [Matrix.submatrix, Matrix.fromRows,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] <;> rfl

variable {K} [AddGroup K] [TopologicalSpace K]
variable (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]

/-- The two supplied product measures concatenate to the supplied measure
of all smaller JPSS rows. -/
theorem measurePreserving_firstBlockRowJoinEquiv (a b j : ℕ) :
    MeasurePreserving (firstBlockRowJoinEquiv K a b j)
      ((rectangularMeasure ν b a).prod (rectangularMeasure ν j a))
      (rectangularMeasure ν (b + j) a) :=
  (measurePreserving_piCongrLeft
    (fun _ : Fin (b + j) => rowMeasure ν a) finSumFinEquiv).comp
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin b ⊕ Fin j => rowMeasure ν a))

/-- Genuine product integrability justifies concatenating the rows and
moving the small quotient integral between the two row integrals. -/
theorem integral_firstBlockJoinedRows
    {α : Type uA} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (a b j : ℕ)
    (H : Matrix (Fin (b + j)) (Fin a) K → α → ℂ)
    (hH : Integrable (fun p : α × Matrix (Fin (b + j)) (Fin a) K => H p.2 p.1)
      (μ.prod (rectangularMeasure ν (b + j) a))) :
    Integrable (fun Z => ∫ q, ∫ T,
      H (firstBlockRowJoinEquiv K a b j (Z, T)) q
        ∂rectangularMeasure ν j a ∂μ) (rectangularMeasure ν b a) ∧
    (∫ Z, ∫ q, ∫ T, H (firstBlockRowJoinEquiv K a b j (Z, T)) q
      ∂rectangularMeasure ν j a ∂μ ∂rectangularMeasure ν b a) =
      ∫ q, ∫ X, H X q ∂rectangularMeasure ν (b + j) a ∂μ := by
  let e := firstBlockRowJoinEquiv K a b j
  have he := measurePreserving_firstBlockRowJoinEquiv ν a b j
  have hs := (he.prod (MeasurePreserving.id μ)).integrable_comp_of_integrable hH.swap
  have ht := (measurePreserving_prodAssoc (rectangularMeasure ν b a)
    (rectangularMeasure ν j a) μ).symm.integrable_comp_of_integrable hs
  have hx : ∀ᵐ Z ∂rectangularMeasure ν b a,
      Integrable (fun p : Matrix (Fin j) (Fin a) K × α => H (e (Z, p.1)) p.2)
        ((rectangularMeasure ν j a).prod μ) := ht.prod_right_ae
  have hswap :
      (fun Z => ∫ T, ∫ q, H (e (Z, T)) q ∂μ ∂rectangularMeasure ν j a) =ᵐ[
        rectangularMeasure ν b a]
      (fun Z => ∫ q, ∫ T, H (e (Z, T)) q ∂rectangularMeasure ν j a ∂μ) := by
    filter_upwards [hx] with Z hZ
    exact integral_integral_swap hZ
  have hj := he.integrable_comp_of_integrable hH.swap.integral_prod_left
  refine ⟨hj.integral_prod_left.congr hswap, ?_⟩
  calc
    _ = ∫ Z, ∫ T, ∫ q, H (e (Z, T)) q ∂μ
        ∂rectangularMeasure ν j a ∂rectangularMeasure ν b a :=
      integral_congr_ae hswap.symm
    _ = ∫ p, ∫ q, H (e p) q ∂μ
        ∂(rectangularMeasure ν b a).prod (rectangularMeasure ν j a) :=
      (integral_prod _ hj).symm
    _ = ∫ X, ∫ q, H X q ∂μ ∂rectangularMeasure ν (b + j) a :=
      he.integral_comp' (fun X => ∫ q, H X q ∂μ)
    _ = _ := integral_integral_swap hH.swap

end RowMeasure

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance disintegrationTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance disintegrationValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance disintegrationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance disintegrationSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance disintegrationMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance disintegrationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance disintegrationGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance disintegrationGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance disintegrationUpperMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance disintegrationUpperBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance disintegrationQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance disintegrationQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

/-- Product convergence at a transported large rank, with no nonvanishing
assumption on either supplied functional. -/
theorem upperSliceConvergesAt {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {S : Type uS} [AddCommGroup S] [Module ℂ S]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) S)
    (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n ρ)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (Wsmall : (coefficientModel ρ ell).toSubmodule)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hρ : IsOfWhittakerType n (inverseStandardCharacter ψ n) ρ)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (hμ : QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (ν : AdditiveHaarMeasure F.Carrier) (d : ℤ) :
    Integrable (fun z : LeftUnipotentQuotient n F.Carrier ×
        Matrix (Fin j) (Fin (n + 1)) F.Carrier =>
      unequalRankIntegrandAt F j k hr ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        Wtest.val Wsmall.val 0 z.2 z.1)
      ((μ.restrict (determinantSlice F.canonicalTopologicalData n d)).prod
        (rectangularMeasure ν j (n + 1))) := by
  subst r
  exact upperSliceConverges F j k ψ π ρ lambda ell Wtest Wsmall hπ hρ μ hμ ν d

/-- Rank transport commutes with the actual iterated slice coefficient. -/
theorem unequalRankSliceCoefficientAt_eq_integral {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n) (d : ℤ) :
    unequalRankSliceCoefficientAt F j k hr ψ μ ν W W' d =
      ∫ q in determinantSlice F.canonicalTopologicalData n d,
        ∫ X, unequalRankIntegrandAt F j k hr ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) W W' 0 X q ∂ν ∂μ := by
  subst r
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

/-- The actual upper row integral evaluated at a representative of the
small quotient. Its representative independence follows below. -/
def firstBlockUpperRowAverage (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ U, firstBlockUpperValue F h j k ell f Wtest s
    (firstBlockEmbedding h F.Carrier q.out * (lowerRadical h F.Carrier Z * g))
    (firstBlockColumns h j U Y) ∂rectangularMeasure ν j (m 0 + 1)

/-- The chosen representative disappears after the exact affine row
substitution. The right side uses the actual small quotient integrand. -/
theorem firstBlockUpperRowAverage_eq (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ∫ T, unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (translateWhittaker ψ (t + (j + k + 1)) Wtest
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val s (firstBlockRows j Z T) q
        ∂rectangularMeasure ν j (m 0 + 1) := by
  unfold firstBlockUpperRowAverage
  rw [integral_firstBlockUpperValue]
  simp only [firstBlockFiberIntegrand, Quotient.out_eq]

/-- The local upper first-block coefficient, retaining both actual
rectangles and the supplied quotient slice. -/
def firstBlockUpperCoefficient
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ Z, ∫ q in determinantSlice F.canonicalTopologicalData (m 0) d,
    firstBlockUpperRowAverage F h j k ell f Wtest ν 0 q Z Y g ∂μ
      ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)

/-- Product convergence of the actual smaller integrand justifies the row
disintegration; no convergence is deduced from total integral equalities. -/
theorem firstBlockUpperCoefficient_eq_small
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite μ] (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (hsmall : Integrable
      (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
          Matrix (Fin (m 1 + 1 + j)) (Fin (m 0 + 1)) F.Carrier =>
        unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (translateWhittaker ψ (t + (j + k + 1)) Wtest
            (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
              appendIdentity t (j + k + 1) g))
          (firstBlockCoefficient ell f g).val 0 z.2 z.1)
      ((μ.restrict (determinantSlice F.canonicalTopologicalData (m 0) d)).prod
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)))) :
    Integrable (fun Z => ∫ q in determinantSlice F.canonicalTopologicalData (m 0) d,
      firstBlockUpperRowAverage F h j k ell f Wtest ν 0 q Z Y g ∂μ)
        (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ∧
    firstBlockUpperCoefficient F h j k ell f Wtest ν μ d Y g =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      unequalRankSliceCoefficientAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        (translateWhittaker ψ (t + (j + k + 1)) Wtest
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val d := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hint, heq⟩ := integral_firstBlockJoinedRows ν
    (μ.restrict (determinantSlice F.canonicalTopologicalData (m 0) d))
    (m 0 + 1) (m 1 + 1) j _ hsmall
  simp only [firstBlockRowJoinEquiv_apply] at hint heq
  change Integrable (fun Z => ∫ q, ∫ T,
    unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (translateWhittaker ψ (t + (j + k + 1)) Wtest
        (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
          appendIdentity t (j + k + 1) g))
      (firstBlockCoefficient ell f g).val 0 (firstBlockRows j Z T) q
        ∂rectangularMeasure ν j (m 0 + 1)
        ∂μ.restrict (determinantSlice F.canonicalTopologicalData (m 0) d))
    (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) at hint
  constructor
  · simpa only [firstBlockUpperRowAverage_eq, integral_const_mul] using
      hint.const_mul (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)))
  · unfold firstBlockUpperCoefficient
    simp_rw [firstBlockUpperRowAverage_eq, integral_const_mul]
    congr 1
    rw [unequalRankSliceCoefficientAt_eq_integral]
    exact heq

/-- The actual local upper coefficient equals the actual smaller JPSS
coefficient for the full Whittaker-type inputs, including zero functionals. -/
theorem firstBlockUpperCoefficient_eq_small_of_whittakerType
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0))
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite μ]
    (hμ : QuotientIntegration.IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μ)
    (d : ℤ) (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Integrable (fun Z => ∫ q in determinantSlice F.canonicalTopologicalData (m 0) d,
      firstBlockUpperRowAverage F h j k ell f Wmodel.val ν 0 q Z Y g ∂μ)
        (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ∧
    firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      unequalRankSliceCoefficientAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        (translateWhittaker ψ (t + (j + k + 1)) Wmodel.val
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val d := by
  apply firstBlockUpperCoefficient_eq_small
  exact upperSliceConvergesAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
    π (σ 0) lambda (ell 0)
    (translateModelEquiv ψ π lambda
      (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g) Wmodel)
    (firstBlockCoefficient ell f g) hπ hσ μ hμ ν d

end Padic

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
