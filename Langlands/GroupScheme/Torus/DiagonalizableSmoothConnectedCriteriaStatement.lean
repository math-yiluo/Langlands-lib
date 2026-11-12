import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Smoothness and connectedness of diagonalizable groups: statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Smoothness and connectedness criteria for `D(M)`** (Milne, *Algebraic Groups* (2017),
Remark 12.5, with `M` finitely generated as fixed at the start of §12.b). Let `k` be a field
of characteristic exponent `p` and let `Λ` be a finitely generated abelian group. For the
diagonalizable group `D(Λ) = Spec k[Λ]` over `k`:

1. `D(Λ)` is connected if and only if every torsion element of `Λ` is killed by a power
   of `p`;
2. `D(Λ)` is smooth over `k` if and only if `Λ` has no nonzero element killed by `p`;
3. `D(Λ)` is smooth and connected if and only if `Λ` is a free `ℤ`-module. -/
def DiagonalizableSmoothConnectedCriteriaStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
    (ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left ↔
        ∀ x : Λ, IsOfFinAddOrder x → ∃ n : ℕ, p ^ n • x = 0) ∧
      (Smooth (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom ↔
        ∀ x : Λ, p • x = 0 → x = 0) ∧
      (Smooth (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom ∧
          ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left ↔
        Module.Free ℤ Λ)

end Langlands.GroupScheme
