import Langlands.LocalFactor.CommonClosureOrdinaryTransport
import Langlands.LocalFactor.Abelian.Transport

/-! # Supplied common-closure systems on standalone harmonic and Weil inputs -/

noncomputable section

universe uF uE uV

namespace Langlands.LocalFactor.CommonClosureSystemTransport

open CommonClosure Weil.Local LocalClassField HarmonicAnalysis VirtualRepresentation
open CommonClosureSpectral.Transport CommonClosureWeilDeligne.Transport

variable {p : ℕ} [Fact p.Prime]
  (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
local instance : MeasurableSpace E.Carrier := borel E.Carrier
local instance : Algebra (Padic p) (extensionFiniteIntermediate F E f).field :=
  ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
local instance : TopologicalSpace (extensionFiniteIntermediate F E f).field :=
  (fieldData F (extensionFiniteIntermediate F E f)).topology
local instance : MeasurableSpace (extensionFiniteIntermediate F E f).field :=
  borel (extensionFiniteIntermediate F E f).field

/-- Inverse pullback of the standalone character along the actual image-field equivalence. -/
def imageAdditiveCharacter (ψ : UnitaryAdditiveCharacter E.Carrier) :
    AdditiveCharacter F (extensionFiniteIntermediate F E f) :=
  PadicField.ConductorTransport.additiveCharacter E
    ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f) ψ

@[simp]
theorem imageAdditiveCharacter_apply (ψ : UnitaryAdditiveCharacter E.Carrier)
    (y : (extensionFiniteIntermediate F E f).field) :
    imageAdditiveCharacter F E f ψ y =
      ψ ((extensionIntermediatePadicEquiv F E f).symm y) := rfl

/-- Pushforward of the actual regular additive Haar measure to the image field. -/
def imageHaarMeasure (μ : AdditiveHaarMeasure E.Carrier) :
    HaarMeasure F (extensionFiniteIntermediate F E f) :=
  PadicField.AbelianTransport.haarMeasure E
    ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f) μ

@[simp]
theorem imageHaarMeasure_measure (μ : AdditiveHaarMeasure E.Carrier) :
    (imageHaarMeasure F E f μ).measure =
      MeasureTheory.Measure.map (extensionIntermediatePadicEquiv F E f) μ.measure := rfl

/-- The inverse exact-virtual comparison also commutes with the intrinsic spectral twist. -/
theorem virtualEquiv_symm_twist (s : ℂ)
    (x : StandaloneVirtual.{uE, max uF uV} E) :
    (virtualEquiv F E f).symm
      (SpectralTwist.virtual (localDegree E)
        (E.canonicalTopologicalData.residueCardinality : ℝ)
        (standalone_residueCardinality_pos E) s x) =
    CommonClosureSpectral.virtualTwist F (extensionFiniteIntermediate F E f) s
      ((virtualEquiv F E f).symm x) := by
  apply (virtualEquiv F E f).injective
  rw [LinearEquiv.apply_symm_apply, virtualEquiv_twist, LinearEquiv.apply_symm_apply]

/-- Deligne's spectral value on standalone inputs, conditional on the explicitly
supplied common-closure system. This is one transported component, not a new family. -/
def conditionalDeligneValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (_hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (x : StandaloneVirtual.{uE, max uF uV} E) (s : ℂ) : ℂˣ :=
  ε (extensionFiniteIntermediate F E f)
    (imageAdditiveCharacter F E f ψ) (imageHaarMeasure F E f μ)
    ((virtualEquiv F E f).symm
      (SpectralTwist.virtual (localDegree E)
        (E.canonicalTopologicalData.residueCardinality : ℝ)
        (standalone_residueCardinality_pos E) s x))

/-- The intrinsic standalone twist evaluates the same supplied image-field component. -/
theorem conditionalDeligneValue_eq (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (x : StandaloneVirtual.{uE, max uF uV} E) (s : ℂ) :
    conditionalDeligneValue F E f e ε hε ψ μ x s =
      CommonClosureSpectral.conditionalDeligneValue F e ε hε
        (extensionFiniteIntermediate F E f) (imageAdditiveCharacter F E f ψ)
        (imageHaarMeasure F E f μ) ((virtualEquiv F E f).symm x) s := by
  unfold conditionalDeligneValue CommonClosureSpectral.conditionalDeligneValue
  rw [virtualEquiv_symm_twist]

/-- The comparison on every common-closure virtual class. -/
theorem conditionalDeligneValue_virtualEquiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (x : Virtual.{uF, uV} F (extensionFiniteIntermediate F E f)) (s : ℂ) :
    conditionalDeligneValue F E f e ε hε ψ μ (virtualEquiv F E f x) s =
      CommonClosureSpectral.conditionalDeligneValue F e ε hε
        (extensionFiniteIntermediate F E f) (imageAdditiveCharacter F E f ψ)
        (imageHaarMeasure F E f μ) x s := by
  rw [conditionalDeligneValue_eq, LinearEquiv.symm_apply_apply]

/-- Multiplicativity in exact virtual sums is inherited from the supplied system. -/
theorem conditionalDeligneValue_add (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (x y : StandaloneVirtual.{uE, max uF uV} E) (s : ℂ) :
    conditionalDeligneValue F E f e ε hε ψ μ (x + y) s =
      conditionalDeligneValue F E f e ε hε ψ μ x s *
        conditionalDeligneValue F E f e ε hε ψ μ y s := by
  simp only [conditionalDeligneValue, map_add]
  exact hε.2.1 _ _ _ _ _

/-- The zero exact virtual class has value one for every spectral coordinate. -/
@[simp]
theorem conditionalDeligneValue_zero (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier) (s : ℂ) :
    conditionalDeligneValue F E f e ε hε ψ μ 0 s = 1 := by
  simp only [conditionalDeligneValue, map_zero, NonabelianSystem.value_zero hε.2.1]

/-- The exact class of an actual continuous standalone underlying representation. -/
def standaloneUnderlyingClass (A : LocalWeilDeligneRepresentation.{uE, uV} E)
    (hA : A.toFiniteRepresentation.IsContinuous) : StandaloneVirtual.{uE, uV} E :=
  ExactGrothendieckGroup.ofRepresentation _ ⟨A.toFiniteRepresentation, hA⟩

/-- Equivalent standalone pairs have the same ordinary exact class. -/
theorem standaloneUnderlyingClass_eq_of_equiv
    {A B : LocalWeilDeligneRepresentation.{uE, uV} E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (i : WeilDeligneRepresentation.Equiv A B) :
    standaloneUnderlyingClass E A hA = standaloneUnderlyingClass E B hB :=
  ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ i.representationEquiv

/-- Taking the ordinary class commutes with the actual standalone pair construction. -/
theorem underlyingClass_standalonePair
    (A : CommonClosureWeilDeligne.Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (hA : A.toFiniteRepresentation.IsContinuous) :
    virtualEquiv F E f
      (CommonClosureWeilDeligne.underlyingClass F (extensionFiniteIntermediate F E f) A hA) =
    standaloneUnderlyingClass E (standalonePair F E f A)
      (standalonePair_isContinuous F E f A hA) :=
  virtualEquiv_ofRepresentation F E f ⟨A.toFiniteRepresentation, hA⟩

/-- The complete conditional standalone WD value retains the actual determinant on
`V^I / (ker N)^I` at geometric Frobenius and the intrinsic coordinate `q_E^(-s)`. -/
def conditionalEpsilonValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (A : LocalWeilDeligneRepresentation.{uE, max uF uV} E)
    (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : ℂ) : ℂˣ :=
  conditionalDeligneValue F E f e ε hε ψ μ (standaloneUnderlyingClass E A hA) s *
    WeilDeligne.quotientCorrectionValue A (localInertia E) Φ.val
      (spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
        (standalone_residueCardinality_pos E) s)

/-- Pair equivalence preserves both the exact ordinary class and the actual
quotient correction of the standalone conditional value. -/
theorem conditionalEpsilonValue_eq_of_equiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    {A B : LocalWeilDeligneRepresentation.{uE, max uF uV} E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (i : WeilDeligneRepresentation.Equiv A B)
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : ℂ) :
    conditionalEpsilonValue F E f e ε hε ψ μ A hA Φ s =
      conditionalEpsilonValue F E f e ε hε ψ μ B hB Φ s := by
  unfold conditionalEpsilonValue
  rw [standaloneUnderlyingClass_eq_of_equiv E hA hB i]
  congr 1
  apply Units.ext
  simp only [WeilDeligne.quotientCorrectionValue_eq_eval,
    WeilDeligne.quotientCorrectionPolynomial_eq_of_equiv (localInertia E) i]

/-- The full epsilon expression agrees for corresponding harmonic inputs, actual
pairs, and geometric Frobenius lifts, at the unchanged spectral coordinate. -/
theorem conditionalEpsilonValue_standalonePair (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : UnitaryAdditiveCharacter E.Carrier) (μ : AdditiveHaarMeasure E.Carrier)
    (A : CommonClosureWeilDeligne.Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : ℂ) :
    conditionalEpsilonValue F E f e ε hε ψ μ (standalonePair F E f A)
      (standalonePair_isContinuous F E f A hA) Φ s =
    CommonClosureWeilDeligne.conditionalEpsilonValue F e ε hε
      (extensionFiniteIntermediate F E f) (imageAdditiveCharacter F E f ψ)
      (imageHaarMeasure F E f μ) A hA (geometricFrobeniusEquiv F E f Φ) s := by
  unfold conditionalEpsilonValue CommonClosureWeilDeligne.conditionalEpsilonValue
  rw [← underlyingClass_standalonePair F E f A hA,
    conditionalDeligneValue_virtualEquiv, quotientValue_standalonePair]

end Langlands.LocalFactor.CommonClosureSystemTransport
