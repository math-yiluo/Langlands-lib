import Langlands.Geometry.Analytic.RationalLocalization.Definitions

/-! # Rational localization with actual affinoid-algebra inputs -/

noncomputable section

universe u v

namespace Langlands.Analytic.RationalLocalization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

/-- Equations, spectrum identification, bounded extension and transport for the
constructed rational quotient of an arbitrary presented strict affinoid algebra.
Power bounds for extension remain explicit. -/
def LocalizationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : P) (f : Fin m → P),
    (∀ j, baseMap K P m g f g * fractionCoordinate K P m g f j =
      baseMap K P m g f (f j)) ∧
    (∀ x : BanachSpectrum (algebra K P m g f),
      BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom x ∈
        locus K P m g f) ∧
    (GeneratesUnitIdeal K P m g f →
      IsUnit (baseMap K P m g f g) ∧
      Set.range (BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom) =
        locus K P m g f ∧
      Topology.IsClosedEmbedding
        (BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom) ∧
      ∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
        (φ ψ : BoundedAlgHom K (algebra K P m g f) B),
        φ.comp (baseMap K P m g f) = ψ.comp (baseMap K P m g f) → φ = ψ) ∧
    (∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
      [IsUltrametricDist B] [CompleteSpace B]
      (φ : BoundedAlgHom K P B) (b : Fin m → B),
      HasBoundedMonomials (Fin m) B b →
      (∀ j, φ g * b j = φ (f j)) →
      ∃ ψ : BoundedAlgHom K (algebra K P m g f) B,
        ψ.comp (baseMap K P m g f) = φ ∧
        ∀ j, ψ (fractionCoordinate K P m g f j) = b j) ∧
    (∀ (Q : PresentedStrictAffinoidAlgebra K) (g' : Q) (f' : Fin m → Q)
      (e : BoundedAlgEquiv K P Q),
      e g = g' → (∀ j, e (f j) = f' j) →
      ∃ E : BoundedAlgEquiv K (algebra K P m g f) (algebra K Q m g' f'),
        E.toBoundedAlgHom.comp (baseMap K P m g f) =
          (baseMap K Q m g' f').comp e.toBoundedAlgHom ∧
        (∀ j, E (fractionCoordinate K P m g f j) =
          fractionCoordinate K Q m g' f' j) ∧
        ∀ x : BanachSpectrum (algebra K Q m g' f'),
          BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom
              (E.spectrumHomeomorph x) =
            e.spectrumHomeomorph
              (BanachSpectrum.comap (baseMap K Q m g' f').toBoundedRingHom x))

end Langlands.Analytic.RationalLocalization
