import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.GaloisPointRational

/-! # Induced tori (KP Definition 2.5.1) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- KP Definition 2.5.1: `T` is induced if, for some finite Galois extension `E/k` splitting
`T`, the character lattice `X^*(T_E)` has a `ℤ`-basis permuted by `Gal(E/k)`. -/
def IsInducedTorus (T : CommGroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra k E), FiniteDimensional k E ∧ IsGalois k E ∧
    IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp) ∧
    ∃ (I : Type u)
      (b : Module.Basis I ℤ
        (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))),
      ∀ (σ : E ≃ₐ[k] E) (i : I), ∃ j : I,
        characterLattice.galoisRepresentation k E T σ (b i) = b j

/-- An induced torus is a torus: its finite Galois splitting field splits it. -/
theorem IsInducedTorus.isTorus {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} (h : IsInducedTorus Z) :
    IsTorus Z.toGrp := by
  obtain ⟨E, hE, aE, -, -, hs, -⟩ := h
  exact ⟨E, hE, aE, hs⟩

end Langlands.GroupScheme
