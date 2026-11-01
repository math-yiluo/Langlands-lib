import Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel
import Langlands.Representation.RankinSelberg.TwoBlockDualSectionJacquetProof
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarOrbit
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroCovariance

/-!
# Scalar and determinant transport for the dominant reversed dual

These representative-level identities retain the actual right Weyl translation.
The comparison of the two five-block matrices and all quotient integration remain
separate obligations.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet

universe uF uV uW

section Determinants

variable {K : Type uF} [Field K] (abv : AbsoluteValue K ℝ) {n : ℕ}

/-- Left multiplication by the long Weyl matrix adds no determinant scalar;
inverse transpose reverses the complex exponent. -/
theorem determinantWeight_longWeyl_inverseTranspose (g : GeneralLinear n K) (z : ℂ) :
    determinantWeight abv (weylLong n K * inverseTranspose n K g) z =
      determinantWeight abv g (-z) := by
  rw [determinantWeight_mul, determinantWeight_inverseTranspose]
  have hw : determinantWeight abv (weylLong n K) z = 1 := by
    simp only [determinantWeight, adjacentRank_abv_det_weylLong,
      Complex.ofReal_one, Complex.one_cpow]
  rw [hw, one_mul]

/-- The complementary rectangle sizes give exactly matching weights at
the parameters `s` and `1-s`, for every complex parameter. -/
theorem dualDeterminantWeight (j k : ℕ) (g : GeneralLinear n K) (s : ℂ) :
    determinantWeight abv (weylLong n K * inverseTranspose n K g)
        (1 - s - ((k+j+1 : ℕ) : ℂ)/2 + (k : ℂ)) =
      determinantWeight abv g (s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) := by
  rw [determinantWeight_longWeyl_inverseTranspose]
  congr 1
  push_cast
  ring

/-- Comparing both coefficient kernels at parameter zero retains one
factor of the original absolute determinant. -/
theorem dualDeterminantWeight_zero (j k : ℕ) (g : GeneralLinear n K) :
    determinantWeight abv (weylLong n K * inverseTranspose n K g)
        (0 - ((k+j+1 : ℕ) : ℂ)/2 + (k : ℂ)) =
      (abv (Matrix.det g.val) : ℂ) *
        determinantWeight abv g (0 - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) := by
  have hd := dualDeterminantWeight abv j k g 1
  simp only [sub_self] at hd
  rw [hd, show (1 : ℂ) - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ) =
      (0 - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) + 1 by ring,
    determinantWeight_exponent_add]
  simp only [determinantWeight, Complex.cpow_one]
  ring

end Determinants

section Coefficient

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {t r j k : ℕ} (hr : r=t+(j+k+1))
  (ψ : UnitaryAdditiveCharacter K)
  (π : Representation ℂ (GeneralLinear (r+1) K) V)

/-- The actual dual test of Section 4.10(3), including its prescribed
right factor `diag(I_(t+1),w_(j+k+1))`. -/
def reversedDualTest (Wtest : WhittakerFunctions ψ r) :
    WhittakerFunctions (ψ.scale (-1)) r :=
  translateWhittaker (ψ.scale (-1)) r
    (firstDualFunction ψ r Wtest) (rightWeyl hr)

@[simp] theorem reversedDualTest_apply (Wtest : WhittakerFunctions ψ r)
    (P : GeneralLinear (r+1) K) :
    (reversedDualTest hr ψ Wtest).val P =
      Wtest.val (weylLong (r+1) K *
        inverseTranspose (r+1) K (P * rightWeyl hr)) := rfl

/-- The prescribed right translation is represented by translating the
vector in the actual inverse-transpose representation. -/
theorem translatedDualTest_coefficient (L : glFunctionals ψ r π) (v : V) :
    reversedDualTest hr ψ (coefficientMap π L v) =
      coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π L)
        (inverseTransposePullback π (rightWeyl hr) v) := by
  rw [reversedDualTest, firstDualFunction_coefficient]
  apply Subtype.ext
  funext P
  change (firstDualFunctional ψ π L).val
      (inverseTransposePullback π (P * rightWeyl hr) v) =
    (firstDualFunctional ψ π L).val
      (inverseTransposePullback π P (inverseTransposePullback π (rightWeyl hr) v))
  rw [map_mul, Module.End.mul_apply]

end Coefficient

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i+1) = t+1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F.Carrier) (W i))

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

omit h σ hadd hmod in
/-- On a determinant slice of order `d`, the extra zero-parameter scalar
is precisely `q^(-d)` for the canonical residue cardinality. -/
theorem dualDeterminantWeight_zero_onSlice {n : ℕ} (j k : ℕ)
    (g : GeneralLinear n F.Carrier) (d : ℤ)
    (hd : F.canonicalTopologicalData.ord (Matrix.det g.val) = d) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (weylLong n F.Carrier * inverseTranspose n F.Carrier g)
        (0 - ((k+j+1 : ℕ) : ℂ)/2 + (k : ℂ)) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-d) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          g (0 - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) := by
  rw [dualDeterminantWeight_zero]
  congr 1
  rw [normalizedAbsoluteValue_apply,
    F.canonicalTopologicalData.normalizedAbs_of_ne_zero g.det_ne_zero, hd,
    Complex.ofReal_zpow, Complex.ofReal_natCast]

set_option maxHeartbeats 1600000 in
/-- One actual section equivalence supplies all reflected scalar values.
Its weighted comparison retains the source's explicit right Weyl translate.
No equality between the two five-block matrices is assumed or concluded. -/
theorem exists_reversedDualScalarRealization (hσ : ∀ i, IsSmooth (σ i)) :
    let mD : Fin 2 → ℕ := fun i => m i.rev
    let hD : ∑ i, (mD i+1) = t+1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i+1)).trans h
    let WD : Fin 2 → Type uW := fun i => W i.rev
    letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
    letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
    let σD : ∀ i, Representation ℂ (GeneralLinear (mD i+1) F.Carrier) (WD i) :=
      fun i => inverseTransposePullback (σ i.rev)
    ∃ E : Representation.Equiv
        (inverseTransposePullback (TwoBlockJacquet.inducedRep F h σ))
        (TwoBlockJacquet.inducedRep F hD σD),
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
        let ellD : ∀ i, glInverseFunctionals (ψ.scale (-1)) (mD i) (σD i) :=
          fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev)
        (∀ (r : ℕ) (Wtest : WhittakerFunctions ψ r)
          (f : Sections F h σ) (g : GeneralLinear (t+1) F.Carrier)
          (P : GeneralLinear (r+1) F.Carrier),
          rawScalarValue ellD (E f) (firstDualFunction ψ r Wtest)
              (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) P =
            rawScalarValue ell f Wtest g
              (weylLong (r+1) F.Carrier * inverseTranspose (r+1) F.Carrier P)) ∧
        ∀ (r j k : ℕ) (hr : r=t+(j+k+1))
          (Wtest : WhittakerFunctions ψ r) (f : Sections F h σ)
          (g : GeneralLinear (t+1) F.Carrier) (P : GeneralLinear (r+1) F.Carrier) (s : ℂ),
          rawScalarValue ellD (E f) (reversedDualTest hr ψ Wtest)
              (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) P *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g)
              (1-s-((k+j+1 : ℕ) : ℂ)/2+(k : ℂ)) =
            rawScalarValue ell f Wtest g
                (weylLong (r+1) F.Carrier *
                  inverseTranspose (r+1) F.Carrier (P * rightWeyl hr)) *
              determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
                g (s-((j+k+1 : ℕ) : ℂ)/2+(j : ℂ)) := by
  dsimp only
  obtain ⟨E, -, -, hE⟩ := twoBlockDualSectionJacquet p F t m h W σ hσ
  refine ⟨E, ?_⟩
  intro ψ ell
  obtain ⟨-, hscalar, -⟩ := hE ψ ell
  have hinv (g : GeneralLinear (t+1) F.Carrier) :
      weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) = g := by
    simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive,
      ← mul_assoc, weylLong_mul_self, one_mul]
  constructor
  · intro r Wtest f g P
    simp only [rawScalarValue, hscalar, hinv, firstDualFunction_apply]
  · intro r j k hr Wtest f g P s
    simp only [rawScalarValue, hscalar, hinv, reversedDualTest_apply,
      dualDeterminantWeight]

end Padic

end Langlands.RankinSelberg.TwoBlockDominantRectangular
