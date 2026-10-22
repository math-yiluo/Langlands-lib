import Langlands.Geometry.Analytic.RationalLocalization.Definitions

/-! # Domain representations tested on presented strict affinoids -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The image condition for the actual contravariant map on spectra. -/
def HasImageIn {P Q : PresentedStrictAffinoidAlgebra K}
    (φ : BoundedAlgHom K P Q) (U : Set (BanachSpectrum P)) : Prop :=
  ∀ x : BanachSpectrum Q, BanachSpectrum.comap φ.toBoundedRingHom x ∈ U

/-- A specified actual affinoid map represents a closed subset with respect to
all presented strict affinoid tests. This is weaker than the full affinoid-domain
property, whose tests include non-strict affinoids. -/
def Represents {P Q : PresentedStrictAffinoidAlgebra K}
    (i : BoundedAlgHom K P Q) (U : Set (BanachSpectrum P)) : Prop :=
  IsClosed U ∧
  Set.range (BanachSpectrum.comap i.toBoundedRingHom) = U ∧
  ∀ (R : PresentedStrictAffinoidAlgebra K) (φ : BoundedAlgHom K P R),
    HasImageIn K φ U →
    ∃! ψ : BoundedAlgHom K Q R, ψ.comp i = φ

/-- Rational input data in the actual base algebra, with no common spectrum
zero. No representing algebra or universal property is an input field. -/
structure RationalData (P : PresentedStrictAffinoidAlgebra K) where
  arity : ℕ
  denominator : P
  numerator : Fin arity → P
  no_common_zero : ∀ x : BanachSpectrum P,
    x denominator ≠ 0 ∨ ∃ j, x (numerator j) ≠ 0

namespace RationalData

variable {K} {P : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)

/-- The subset cut out by the unit-radius rational inequalities. -/
def locus : Set (BanachSpectrum P) :=
  RationalLocalization.locus K P d.arity d.denominator d.numerator

/-- Construct the actual closed-ideal Tate quotient from the rational inputs. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  RationalLocalization.algebra K P d.arity d.denominator d.numerator

/-- The bounded structural map of the constructed rational quotient. -/
def baseMap : BoundedAlgHom K P d.algebra :=
  RationalLocalization.baseMap K P d.arity d.denominator d.numerator

/-- The continuous spectrum map of the constructed rational quotient. -/
def spectrumMap : C(BanachSpectrum d.algebra, BanachSpectrum P) :=
  BanachSpectrum.comapContinuous d.baseMap.toBoundedRingHom

end RationalData

end Langlands.Analytic.StrictTestDomain
