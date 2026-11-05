import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotients
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Stable images of actual proper adic cohomology -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For a coherent module on a proper scheme over a noetherian ring, the image
from a sufficiently high adic quotient is the image from the original module,
with one bound on the difference of indices. -/
def ProperAdicCohomologyStableImageStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f →
      ∀ (M : X.Modules), M.IsQuasicoherent →
        (∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) →
          ∀ p : ℕ, ∃ c : ℕ, ∀ n k : ℕ, ∀ h : n + c ≤ k,
            LinearMap.range
                ((DerivedSections.relativeCohomology f p).map
                  (IdealAdic.adicTransition f I M
                    (Nat.le_trans (Nat.le_add_right n c) h))).hom =
              LinearMap.range
                ((DerivedSections.relativeCohomology f p).map
                  (IdealAdic.adicProjection f I M n)).hom

end Langlands.AlgebraicGeometry.Modules
