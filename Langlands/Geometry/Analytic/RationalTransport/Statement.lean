import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Langlands.Geometry.Analytic.RationalPresentation.Definitions

/-! # Bounded transport of actual rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

/-- Base maps preserving the displayed elements extend uniquely when new
coordinates are prescribed; base equivalences induce bounded equivalences
compatible with the actual spectrum maps. No unit-ideal hypothesis is imposed. -/
def TransportStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
    (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K)
    (n' : ℕ) (S' : Set (StrictTateAlgebra (Fin n') K))
    (g' : StrictTateAlgebra (Fin n') K) (f' : Fin m → StrictTateAlgebra (Fin n') K),
    (∀ (φ : BoundedAlgHom K (ofRelations K n S) (ofRelations K n' S')),
      φ (presentationMap K (ofRelations K n S) g) =
        presentationMap K (ofRelations K n' S') g' →
      (∀ j, φ (presentationMap K (ofRelations K n S) (f j)) =
        presentationMap K (ofRelations K n' S') (f' j)) →
      ∃! χ : BoundedAlgHom K (algebra K n m S g f) (algebra K n' m S' g' f'),
        χ.comp (baseMap K n m S g f) = (baseMap K n' m S' g' f').comp φ ∧
        ∀ j, χ (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) =
          coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j)) ∧
    (∀ (e : BoundedAlgEquiv K (ofRelations K n S) (ofRelations K n' S')),
      e (presentationMap K (ofRelations K n S) g) =
        presentationMap K (ofRelations K n' S') g' →
      (∀ j, e (presentationMap K (ofRelations K n S) (f j)) =
        presentationMap K (ofRelations K n' S') (f' j)) →
      ∃ E : BoundedAlgEquiv K (algebra K n m S g f) (algebra K n' m S' g' f'),
        E.toBoundedAlgHom.comp (baseMap K n m S g f) =
          (baseMap K n' m S' g' f').comp e.toBoundedAlgHom ∧
        (∀ j, E (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) =
          coordinate K (algebra K n' m S' g' f') (Fin.natAdd n' j)) ∧
        ∀ x : BanachSpectrum (algebra K n' m S' g' f'),
          BanachSpectrum.comap (baseMap K n m S g f).toBoundedRingHom
              (E.spectrumHomeomorph x) =
            e.spectrumHomeomorph
              (BanachSpectrum.comap (baseMap K n' m S' g' f').toBoundedRingHom x))

end Langlands.Analytic.RationalPresentation
