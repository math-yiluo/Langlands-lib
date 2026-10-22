import Langlands.Geometry.Analytic.RationalIdentity.Definitions

/-! # Target for rational identity charts -/

universe u

namespace Langlands.Analytic.RationalIdentity

/-- Bounded actual fractions give an identity chart, with unit-ball and
empty-tuple specializations. -/
def IdentityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K),
    (∀ (m : ℕ) (g : Pˣ) (f : Fin m → P),
      StrictTateAlgebra.HasBoundedMonomials (Fin m) P (fractions K P m g f) →
      ∃ e : BoundedAlgEquiv K P (RationalLocalization.algebra K P m (g : P) f),
        (∀ a : P, e a = RationalLocalization.baseMap K P m (g : P) f a) ∧
        (∀ x : BanachSpectrum (RationalLocalization.algebra K P m (g : P) f),
          e.spectrumHomeomorph x =
            BanachSpectrum.comap
              (RationalLocalization.baseMap K P m (g : P) f).toBoundedRingHom x) ∧
        RationalLocalization.locus K P m (g : P) f = Set.univ) ∧
    (∀ (m : ℕ) (f : Fin m → P), (∀ i, ‖f i‖ ≤ 1) →
      ∃ e : BoundedAlgEquiv K P (RationalLocalization.algebra K P m 1 f),
        ∀ a : P, e a = RationalLocalization.baseMap K P m 1 f a) ∧
    (∃ e : BoundedAlgEquiv K P
        (RationalLocalization.algebra K P 0 1 (fun i => Fin.elim0 i)),
      ∀ a : P,
        e a = RationalLocalization.baseMap K P 0 1 (fun i => Fin.elim0 i) a)

end Langlands.Analytic.RationalIdentity
