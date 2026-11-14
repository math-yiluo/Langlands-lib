import Langlands.GroupScheme.Torus.Lattice
import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Multiplication

/-! # Isogeny sections of surjections of tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isogeny sections of a surjection of tori.**
For a homomorphism `q : B → C` of commutative tori over a field whose
underlying scheme map is surjective, some homomorphism `s : C → B` satisfies
`q ∘ s = [n]` for a positive integer `n`. -/
def TorusSurjectionIsogenySectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (B C : CommGroupScheme (Spec (CommRingCat.of k))),
    IsTorus B.toGrp → IsTorus C.toGrp →
    ∀ q : B.toGrp ⟶ C.toGrp, Surjective q.hom.hom.left →
      ∃ n : ℕ, 0 < n ∧ ∃ s : C.toGrp ⟶ B.toGrp,
        s ≫ q = multiplication C.toGrp (n : ℤ)

end Langlands.GroupScheme
