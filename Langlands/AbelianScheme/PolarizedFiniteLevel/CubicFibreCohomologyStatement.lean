import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Cohomology of the cubic diagonal bundle over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Over an algebraically closed field, the actual cubic diagonal bundle of an
ordinary polarized datum has no higher cohomology, and its global sections have
dimension `6^g*d`. This is a theorem target. -/
def CubicFibreCohomologyStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] [IsAlgClosed K] (g d n : ℕ), 0 < d →
    ∀ a : Datum P (Spec (CommRingCat.of K)) g d n,
      (∀ i : ℕ, 0 < i →
        IsZero ((relativeCohomology a.abelian.X.hom i).obj a.cubicBundle.obj)) ∧
      Module.finrank K ((relativeCohomology a.abelian.X.hom 0).obj a.cubicBundle.obj) =
        6 ^ g * d

end Langlands.AbelianScheme.PolarizedFiniteLevel
