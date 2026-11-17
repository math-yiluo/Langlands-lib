import Langlands.Global.RankinSelberg.ArchimedeanSchwartzAssembly
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction
import Langlands.Global.RankinSelberg.FourierStandardOutsideProof
import Langlands.Global.Factors.HeckeMixedComponents

/-! # Exact Fourier products from the rectangular measure comparison -/

noncomputable section
universe u uK
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean Langlands.Global.CompletionPadic
open Langlands.ClassField.Global.RelativeWeilGroup
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

attribute [local instance] rectangleMeasurableSpace rectangleBorelSpace

variable (F : Type u) [Field F] [NumberField F]

/-- On finite adeles integral outside `S`, the character is the product of its
canonical components in `S`, without enlarging `S` by an auxiliary control set. -/
theorem finite_character_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (S : Finset (FinitePlace F))
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v))
    (hψv : ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v))
    (x : FiniteAdeles F) (hx : ∀ v ∉ S, x v ∈ v.adicCompletionIntegers F) :
    ψ ((0 : InfiniteAdeles F), x) = ∏ v ∈ S, ψv v (x v) := by
  let b : Adeles F := ((0 : InfiniteAdeles F), x)
  let z := b - finiteAdditivePartialSum S x
  have hz : ψ z = 1 := by
    apply character_eq_one_of_integralOutside hS z
    · funext v
      change 0 - infiniteProjection F v (finiteAdditivePartialSum S x) = 0
      rw [infiniteProjection_finiteAdditivePartialSum, sub_self]
    · intro v hv
      change finiteProjection F v (b - finiteAdditivePartialSum S x) = 0
      rw [map_sub, finiteProjection_finiteAdditivePartialSum, ite_eq_left hv]
      exact sub_self _
    · intro v hv
      change finiteProjection F v (b - finiteAdditivePartialSum S x) ∈ _
      rw [map_sub, finiteProjection_finiteAdditivePartialSum, ite_eq_right hv, sub_zero]
      exact hx v hv
  have hb : b = finiteAdditivePartialSum S x + z := by
    dsimp [z]
    abel
  change ψ b = _
  rw [hb, AddChar.map_add_eq_mul, hz, mul_one]
  rw [finiteAdditivePartialSum, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => (hψv v (x v)).symm

/-- The archimedean character is the product of the supplied real and complex
scaled characters in the mixed coordinates. -/
theorem infinite_character_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (haR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ)
    (haC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))
    (x : InfiniteAdeles F) :
    ψ (x, (0 : FiniteAdeles F)) =
      (∏ v, realScaledCharacter (aR v)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 v)) *
      ∏ w, complexScaledCharacter (aC w)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 w) := by
  rw [infinite_additive_product, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => haR v (x v.1)
  · exact Finset.prod_congr rfl fun w _ => haC w (x w.1)

/-- The character of a row pairing splits into its local pairings when both
rows are integral outside `S`. -/
theorem pairing_character_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (S : Finset (FinitePlace F))
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (haR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ)
    (haC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))
    (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v))
    (hψv : ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v))
    (n : ℕ) (x y : RowVector F n)
    (hx : x ∈ integralOutside F n S) (hy : y ∈ integralOutside F n S) :
    ψ.complex (∑ j, x 0 j * y 0 j) =
      (∏ v, (realScaledCharacter (aR v)).complex
        (∑ j, realRowCoordinates F n v x j * realRowCoordinates F n v y j)) *
      (∏ w, (complexScaledCharacter (aC w)).complex
        (∑ j, complexRowCoordinates F n w x j * complexRowCoordinates F n w y j)) *
      ∏ v : S, ((ψv v.1)
        (∑ j, localCoordinates F n v.1 x j * localCoordinates F n v.1 y j) : ℂ) := by
  let b : Adeles F := ∑ j, x 0 j * y 0 j
  have hb : b = (b.1, (0 : FiniteAdeles F)) + ((0 : InfiniteAdeles F), b.2) := by
    apply Prod.ext <;> simp
  have hfin : ∀ v ∉ S, b.2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    change finiteProjection F v (∑ j, x 0 j * y 0 j) ∈ _
    rw [map_sum]
    apply (v.adicCompletionIntegers F).sum_mem
    intro j _
    rw [map_mul]
    exact (v.adicCompletionIntegers F).mul_mem _ _ (hx v hv j) (hy v hv j)
  change (ψ b : ℂ) = _
  rw [hb, AddChar.map_add_eq_mul, infinite_character_product F ψ aR haR aC haC,
    finite_character_product F ψ S hS ψv hψv b.2 hfin,
    Circle.coe_mul, Circle.coe_mul]
  simp only [← Circle.coeHom_apply, map_prod]
  have hreal (v : {v : InfinitePlace F // v.IsReal}) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F b.1).1 v =
        ∑ j, realRowCoordinates F n v x j * realRowCoordinates F n v y j := by
    change ((((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comp
      (RingHom.fst _ _)) (∑ j, x 0 j * y 0 j) = _
    simp only [map_sum, map_mul]
    rfl
  have hcomplex (w : {v : InfinitePlace F // v.IsComplex}) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F b.1).2 w =
        ∑ j, complexRowCoordinates F n w x j * complexRowCoordinates F n w y j := by
    change ((((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) w).comp
      (RingHom.snd _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comp
      (RingHom.fst _ _)) (∑ j, x 0 j * y 0 j) = _
    simp only [map_sum, map_mul]
    rfl
  have hlocal (v : FinitePlace F) :
      b.2 v = ∑ j, localCoordinates F n v x j * localCoordinates F n v y j := by
    change finiteProjection F v (∑ j, x 0 j * y 0 j) = _
    simp [localCoordinates, map_sum, map_mul]
  simp_rw [hreal, hcomplex, hlocal]
  rw [Finset.prod_coe_sort S (fun v => Circle.coeHom ((ψv v)
    (∑ j, localCoordinates F n v x j * localCoordinates F n v y j)))]
  rfl

/-- Evaluating the unique row preserves its product measure. -/
theorem integral_row_matrix (K : Type uK) [MeasurableSpace K] (ν : Measure K)
    (n : ℕ) (f : (Fin n → K) → ℂ) :
    (∫ y : Matrix (Fin 1) (Fin n) K, f (y 0)
      ∂Measure.pi (fun _ : Fin 1 => Measure.pi (fun _ : Fin n => ν))) =
      ∫ y, f y ∂Measure.pi (fun _ : Fin n => ν) := by
  exact (measurePreserving_piUnique (fun _ : Fin 1 =>
    Measure.pi (fun _ : Fin n => ν))).integral_comp' f

/-- The rectangular integral with one row is the local Fourier integral. -/
theorem rectangular_fourier_integral (K : Type uK) [Field K] [TopologicalSpace K]
    [MeasurableSpace K] (χ : AddChar K ℂ) (ν : HarmonicAnalysis.AdditiveHaarMeasure K)
    (n : ℕ) (Φ : (Fin n → K) → ℂ) (x : Fin n → K) :
    (∫ y : Matrix (Fin 1) (Fin n) K,
      Φ (y 0) * χ (∑ j, y 0 j * x j) ∂Langlands.RankinSelberg.rectangularMeasure ν 1 n) =
      ArchimedeanLocal.fourierTransform χ ν.measure Φ x :=
  integral_row_matrix K ν.measure n (fun y => Φ y * χ (∑ j, y j * x j))

/-- The finite local row Fourier integral under the canonical p-adic topology. -/
def padicRowFourier {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (n : ℕ) (Φ : (Fin n → K.Carrier) → ℂ) (x : Fin n → K.Carrier) : ℂ :=
  let _ := K.canonicalTopologicalData.topology
  let _ := borel K.Carrier
  HarmonicAnalysis.rowFourierIntegral χ ν n Φ x

/-- The p-adic rectangular integral with one row agrees with the row convention. -/
theorem padicRect_fourier_integral {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (n : ℕ) (Φ : (Fin n → K.Carrier) → ℂ) (x : Fin n → K.Carrier) :
    padicRectIntegral K 1 n ν (fun y => Φ (y 0) * (χ (∑ j, y 0 j * x j) : ℂ)) =
      padicRowFourier K χ ν n Φ x := by
  let _ := K.canonicalTopologicalData.topology
  let _ := borel K.Carrier
  unfold padicRectIntegral padicRowFourier HarmonicAnalysis.rowFourierIntegral
    HarmonicAnalysis.rowMeasure Langlands.RankinSelberg.rectangularMeasure
  rw [integral_row_matrix K.Carrier ν.measure n
    (fun y => Φ y * (χ (∑ j, y j * x j) : ℂ))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => mul_comm _ _

/-- Integrality of a one-row rectangle is exactly row integrality. -/
theorem rectIntegralOutside_row (n : ℕ) (S : Finset (FinitePlace F)) :
    rectIntegralOutside F 1 n S = integralOutside F n S := by
  ext x
  constructor
  · intro h v hv j
    exact h v hv 0 j
  · intro h v hv i j
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact h v hv j

@[simp] theorem realRectCoordinates_row (n : ℕ)
    (v : {v : InfinitePlace F // v.IsReal}) (x : RowVector F n) :
    realRectCoordinates F v x 0 = realRowCoordinates F n v x := rfl

@[simp] theorem complexRectCoordinates_row (n : ℕ)
    (w : {v : InfinitePlace F // v.IsComplex}) (x : RowVector F n) :
    complexRectCoordinates F w x 0 = complexRowCoordinates F n w x := rfl

@[simp] theorem localRectCoordinates_row (n : ℕ)
    (v : FinitePlace F) (x : RowVector F n) :
    localRectCoordinates F v x 0 = localCoordinates F n v x := rfl

/-- The exact local Fourier formula for the assembled tensor follows from the
published rectangular self-dual measure comparison. -/
def RestrictedTensorFourierReductionStatement : Prop :=
  RectangleTateStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (S : Finset (FinitePlace F)), FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∀ (n : ℕ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ),
    fourierTransform F n ψ.complex (restrictedTensor F n S ΦR ΦC Φv) =
      (integralOutside F n S).indicator fun x =>
        (∏ v, ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)
          (realRowCoordinates F n v x)) *
        (∏ w, ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)
          (complexRowCoordinates F n w x)) *
        ∏ v : S, padicRowFourier (padicField v.1) (ψv v.1) (νv v.1) n (Φv v.1)
          (localCoordinates F n v.1 x)

/-- Exact Fourier products, conditional only on the rectangular measure premise. -/
theorem restrictedTensorFourierReduction : RestrictedTensorFourierReductionStatement.{u} := by
  intro hT F _ _ _ ψ hψ S hS aR haR aC haC ψv hψv νv hνv n ΦR ΦC Φv
  funext x
  by_cases hx : x ∈ integralOutside F n S
  · rw [Set.indicator_of_mem hx]
    let hR := fun v (y : Matrix (Fin 1) (Fin n) ℝ) =>
      ΦR v (y 0) * (realScaledCharacter (aR v)).complex
        (∑ j, y 0 j * realRowCoordinates F n v x j)
    let hC := fun w (y : Matrix (Fin 1) (Fin n) ℂ) =>
      ΦC w (y 0) * (complexScaledCharacter (aC w)).complex
        (∑ j, y 0 j * complexRowCoordinates F n w x j)
    let hL := fun (v : S) (y : Matrix (Fin 1) (Fin n) (padicField v.1).Carrier) =>
      Φv v.1 (y 0) * ((ψv v.1) (∑ j, y 0 j * localCoordinates F n v.1 x j) : ℂ)
    have hfactor := hT F ψ hψ S hS aR haR aC haC ψv hψv νv hνv 1 n hR hC hL
    rw [rectIntegralOutside_row] at hfactor
    have hint :
        fourierTransform F n ψ.complex (restrictedTensor F n S ΦR ΦC Φv) x =
          ∫ y, (integralOutside F n S).indicator (fun y =>
            (∏ v, hR v (realRectCoordinates F v y)) *
            (∏ w, hC w (complexRectCoordinates F w y)) *
            ∏ v : S, hL v (localRectCoordinates F v.1 y)) y ∂rectangleMeasure F 1 n := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [restrictedTensor_eq F n S ΦR ΦC Φv]
      by_cases hy : y ∈ integralOutside F n S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
          pairing_character_product F ψ S hS aR haR aC haC ψv hψv n y x hy hx]
        simp only [hR, hC, hL, realRectCoordinates_row, complexRectCoordinates_row,
          localRectCoordinates_row, Finset.prod_mul_distrib]
        ring
      · simp only [Set.indicator_of_notMem hy, zero_mul]
    rw [hint]
    simpa only [hR, hC, hL, rectangular_fourier_integral, padicRect_fourier_integral,
      ArchimedeanLocal.realFourierTransform, ArchimedeanLocal.complexFourierTransform]
      using hfactor
  · rw [Set.indicator_of_notMem hx]
    exact (fourierStandardOutside F ψ S hS n _
      (restrictedTensor_isStandardOutside F n S ΦR ΦC Φv)).1 x hx

end Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor
