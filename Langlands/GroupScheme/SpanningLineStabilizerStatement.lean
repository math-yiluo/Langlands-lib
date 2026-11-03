import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # A spanning representation with the same coordinate-line stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

/-- A coordinate line in a finite representation of a smooth affine group over
an algebraically closed field admits a finite representation with the same
unit-scalar stabilizer on every relative scheme test, in which the rational
orbit of the distinguished basis vector spans the whole coordinate space. -/
def SpanningLineStabilizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
    ∃ (n' : ℕ) (j' : Fin (n' + 1)) (ρ' : MatrixRepresentation G (Fin (n' + 1))),
      (∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
        (∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ'.pointMatrix Z x :
              Matrix (Fin (n' + 1)) (Fin (n' + 1)) Γ(Z.left, ⊤)) *ᵥ
                Pi.single j' 1 =
            (c : Γ(Z.left, ⊤)) •
              (Pi.single j' 1 : Fin (n' + 1) → Γ(Z.left, ⊤))) ↔
        (∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *ᵥ
                Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) •
              (Pi.single j 1 : Fin (n + 1) → Γ(Z.left, ⊤)))) ∧
      Submodule.span k
        (Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
          (ρ'.rationalMatrix g :
              Matrix (Fin (n' + 1)) (Fin (n' + 1)) k) *ᵥ
            (Pi.single j' 1 : Fin (n' + 1) → k)) = ⊤

end Langlands.GroupScheme
