import Langlands.Geometry.FormalGroup.RationalHeight
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Existence and denominator independence of rational height -/

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open TopologicalSpace

/-- The affine finite-coordinate O-height target: every local quasi-isogeny
between finite-height formal O-modules has exactly one local rank height function. -/
def RationalHeightExistenceUniquenessStatement
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (F : Type v) [Field F] [Algebra O F] [IsFractionRing O F]
    (R : Type v) [CommRing R] [Algebra O R] : Prop :=
  ∀ π : O, Irreducible π →
    ∀ (σ τ : Type) [Finite σ] [Finite τ]
      (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) (d e : ℕ),
      M.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) d →
      N.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) e →
      ∀ (U : Opens (PrimeSpectrum R)) (z : LocalQuasiIsogeny F π M N U),
        ∃! h : U → ℤ,
          RationalSection.HasHeightFunction π (Nat.card (IsLocalRing.ResidueField O)) z.val h

end Langlands.FormalGroup.ModuleLaw
