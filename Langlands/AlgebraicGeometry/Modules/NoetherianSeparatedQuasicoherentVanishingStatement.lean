import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Vanishing of quasi-coherent cohomology above the dimension of a noetherian scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Let `X` be a noetherian separated scheme whose underlying space has Krull dimension at
most `d`, with a morphism `f : X ⟶ Spec R`. For every quasi-coherent `𝒪_X`-module `M` and
every `n > d`, the Library cohomology `Hⁿ(X, M)`, computed as right-derived `R`-module
global sections, is zero. -/
def NoetherianSeparatedQuasicoherentVanishingStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R) [IsNoetherian X]
    [X.IsSeparated] (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
      ∀ (M : X.Modules), M.IsQuasicoherent →
        ∀ n : ℕ, d < n → IsZero ((DerivedSections.relativeCohomology f n).obj M)

end Langlands.AlgebraicGeometry.Modules
