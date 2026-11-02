import Langlands.AlgebraicGeometry.Modules.CechResolution.Complex
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Direct images of sheafified Čech terms over an affine base

This proposition isolates the quasi-coherence and positive higher-direct-image
vanishing used termwise in the proof of Stacks Project, tag 01XL, with tag 01XC.
It uses the published sheafified alternating Čech terms and actual pushforward
and right-derived pushforward functors. This file only states the proposition.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

/-- Over an affine base, the direct images of the Čech terms of a quasi-coherent
module on a separated scheme are quasi-coherent, and each term is acyclic for
pushforward in every positive derived degree. -/
def CechTermDirectImageStatement : Prop :=
  ∀ (X : Scheme.{u}) (R : CommRingCat.{u}) (π : X ⟶ Spec R), IsSeparated π →
    ∀ (𝒰 : X.OrderedAffineCover) (M : X.Modules), M.IsQuasicoherent → ∀ q : ℕ,
      ((Scheme.Modules.pushforward π).obj (cechTerm 𝒰 M q)).IsQuasicoherent ∧
        ∀ n : ℕ,
          IsZero ((DerivedSections.higherDirectImage π (n + 1)).obj (cechTerm 𝒰 M q))

end Langlands.AlgebraicGeometry.Modules.CechResolution
