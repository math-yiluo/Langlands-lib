import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Geometric reductivity of reductive groups (Haboush's theorem) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

/-- Haboush's theorem: a pseudo-reductive group `G` over an algebraically closed field `k`
(that is, a connected reductive group) is geometrically reductive. For every finite-dimensional
coordinate representation `ρ` of `G` and every nonzero fixed vector `v`, there is a homogeneous
polynomial `F` of positive degree on the representation space that is invariant under `ρ` on
points over every test scheme and does not vanish at `v`. -/
def ReductiveGeometricReductivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (v : n → k),
      v ≠ 0 → ρ.IsFixedVector v →
      ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
        (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
          MvPolynomial.eval₂ (scalarMap T)
              ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
            MvPolynomial.eval₂ (scalarMap T) x F) ∧
        MvPolynomial.eval v F ≠ 0

end Langlands.GroupScheme
