import Langlands.Global.AdelicRegularizedConeIntegralExtensionality
import Langlands.Global.AdelicSquareIntegrableTwistUniqueness
import Langlands.Global.AdelicStandardPositiveLog
import Langlands.Global.AdelicWeakConstantTermDirectness

/-! # Identification of the regularized weak constant term pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {K : Subgroup (AdelicGroupPoints F G)} {Q : StandardIndex F G fam.i fam.ν}

local notation "Forms" => (AdelicGroupPoints F G → ℂ)
local notation "Param" => ComplexCharacterParameter F (fam.P Q)

/-- A normalized Levi pairing distributes over a finite sum in the first argument when the
summand pairings are integrable. -/
theorem normalizedPairing_finsetSum (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (x : AdelicGroupPoints F (fam.P Q)) {Label : Type*} (s : Finset Label)
    (u : Label → Forms) (g : Forms)
    (hint : ∀ i ∈ s, Integrable (fam.squareIntegrablePairingIntegrand K Q x (u i) g)
      (fam.squareIntegrablePairingMeasure K hKc Q)) :
    fam.normalizedPairing K hKc Q x (∑ i ∈ s, u i) g =
      ∑ i ∈ s, fam.normalizedPairing K hKc Q x (u i) g := by
  have he :
      fam.squareIntegrablePairingIntegrand K Q x (∑ i ∈ s, u i) g =
        fun z => ∑ i ∈ s, fam.squareIntegrablePairingIntegrand K Q x (u i) g z := by
    funext z
    simp only [squareIntegrablePairingIntegrand, Finset.sum_apply, Finset.sum_mul]
  unfold normalizedPairing
  rw [he, integral_finsetSum s hint, Finset.mul_sum]

private theorem centralTranslate_finsetSum {Label : Type*} (s : Finset Label) (u : Label → Forms)
    (z : fam.positiveSplitComponent fam.top) :
    fam.centralTranslate z (∑ i ∈ s, u i) = ∑ i ∈ s, fam.centralTranslate z (u i) := by
  funext g
  simp only [centralTranslate, Finset.sum_apply]

attribute [local instance] isClosedImmersion_p

variable {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hK : IsIwasawaCompact (fam.p fam.bot) K) (z : fam.positiveSplitComponent fam.top)

local notation "A2" =>
  IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p Q) (fam.iU Q) (fam.l Q)
local notation "Orth" => fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc Q

/-- A regular coroot-coordinate expansion of the same extended weak constant term pairing,
obtained from another finite twisted presentation of the first argument, gives the same
regularized cone integral. Finite exponential and inducing labels can both repeat their
parameters. The comparison includes central translates. -/
def WeakConstantTermRegularizedConeIdentificationStatement
    (E Φ EQ ΦQ : Forms) (e : ∀ J : StandardIndex F G fam.i fam.ν, fam.UnitaryPairingExpansion J)
    {Label Term : Type*} (s : Finset Label) (lam : Label → Param) (v : Label → Forms)
    (t : Finset Term) (ν : Term → Param) (poly : Term → MvPolynomial (fam.relativeSimpleRoots Q) ℂ) : Prop :=
  let hKQ := fam.isIwasawaCompact_index hK Q
  let u := fun i => fam.centralTranslate z (hKQ.parameterTwist (v i) (lam i))
  let g := fam.centralTranslate z ΦQ
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK z E Φ e →
  fam.IsWeakConstantTerm hsmooth Kinf rho Q E EQ →
  fam.IsWeakConstantTerm hsmooth Kinf rho Q Φ ΦQ →
  (∀ i ∈ s, A2 (v i)) →
  Orth (EQ - ∑ i ∈ s, hKQ.parameterTwist (v i) (lam i)) →
  (e Q).IsRegular →
  (∀ j ∈ t, parameterRealPart F (fam.P Q) (ν j) = 0) →
  (∀ j ∈ t, ∀ α, fam.corootValue Q (ν j) α ≠ 0) →
  (∀ x ∈ fam.positiveSplitComponent Q, ∀ c : fam.relativeSimpleRoots Q → ℝ,
    characterLog F (fam.P Q) x = ∑ α, c α • fam.relativeCoroot Q α →
      (∀ i ∈ s, Integrable (fam.squareIntegrablePairingIntegrand K Q x (u i) g)
        (fam.squareIntegrablePairingMeasure K hK.isCompact Q)) ∧
      ∑ i ∈ s, fam.normalizedPairing K hK.isCompact Q x (u i) g =
        ∑ j ∈ t, Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (ν j) α) *
          MvPolynomial.eval (fun α => (c α : ℂ)) (poly j)) →
  ∀ T : V fam.T, (e Q).regularizedConeIntegral T =
    ∑ j ∈ t, regularizedOrthantTerm (fam.weightCoordinate Q T) (poly j) (fam.corootValue Q (ν j))

/-- Weak constant term uniqueness and uniqueness of the inducing part identify the slice
integrals. Surjectivity of the logarithm and presentation independence identify the cone
integrals. -/
theorem weakConstantTerm_regularizedConeIntegral_eq
    (E Φ EQ ΦQ : Forms) (e : ∀ J : StandardIndex F G fam.i fam.ν, fam.UnitaryPairingExpansion J)
    {Label Term : Type*} (s : Finset Label) (lam : Label → Param) (v : Label → Forms)
    (t : Finset Term) (ν : Term → Param) (poly : Term → MvPolynomial (fam.relativeSimpleRoots Q) ℂ) :
    fam.WeakConstantTermRegularizedConeIdentificationStatement
      rho hsmooth hcalc hK z E Φ EQ ΦQ e s lam v t ν poly := by
  dsimp only [WeakConstantTermRegularizedConeIdentificationStatement]
  intro he hE hΦ hv hr hreg hunit hν hp T
  obtain ⟨E', Φ', s', v', hE', hΦ', hpart, hpair⟩ := he Q
  have hEE' : E' = EQ := hE'.unique hE
  have hΦΦ' : Φ' = ΦQ := hΦ'.unique hΦ
  subst E'
  subst Φ'
  have hparts := IsSquareIntegrableTwistDecomposition.twistSum_eq fam rho hsmooth hcalc
    (fam.isIwasawaCompact_index hK Q) hpart s lam v hv hr
  let u := fun i => fam.centralTranslate z ((fam.isIwasawaCompact_index hK Q).parameterTwist (v i) (lam i))
  let g := fam.centralTranslate z ΦQ
  have hEval (c : fam.relativeSimpleRoots Q → ℝ) :
      (e Q).eval c = ∑ j ∈ t, Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (ν j) α) *
        MvPolynomial.eval (fun α => (c α : ℂ)) (poly j) := by
    obtain ⟨_, log, hlog⟩ := fam.standardPositiveLog Q
    obtain ⟨x, hx⟩ := log.surjective (Multiplicative.ofAdd (∑ α, c α • fam.relativeCoroot Q α))
    have hxLog : characterLog F (fam.P Q) x.val = ∑ α, c α • fam.relativeCoroot Q α :=
      (hlog x).symm.trans (congrArg Multiplicative.toAdd hx)
    obtain ⟨hInt₁, hEq₁⟩ := hpair x.val x.property c hxLog
    obtain ⟨hInt₂, hEq₂⟩ := hp x.val x.property c hxLog
    rw [← hEq₁, ← fam.normalizedPairing_finsetSum hK.isCompact x.val s' _ _ hInt₁,
      ← fam.centralTranslate_finsetSum, hparts, fam.centralTranslate_finsetSum]
    change fam.normalizedPairing K hK.isCompact Q x.val (∑ i ∈ s, u i) g = _
    rw [fam.normalizedPairing_finsetSum hK.isCompact x.val s u g hInt₂, hEq₂]
  have hzero {p : Param} (hreal : parameterRealPart F (fam.P Q) p = 0) (α : fam.relativeSimpleRoots Q) :
      (fam.corootValue Q p α).re = 0 := by
    simp [corootValue, complexParameterPairing_re, hreal]
  exact sum_regularizedOrthantTerm_eq_of_eval_eq (e Q).exponents t
    (fam.corootValue Q) (fun j => fam.corootValue Q (ν j)) (e Q).coefficient poly
    (fun p h => hzero ((e Q).unitary p h)) (fun j h => hzero (hunit j h))
    hreg hν hEval (fam.weightCoordinate Q T)

end Langlands.Global.StandardParabolicFamily
