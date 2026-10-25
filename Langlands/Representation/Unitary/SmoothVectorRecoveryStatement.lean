import Langlands.Representation.Unitary.HermitianDual

/-!
# Recovering an admissible representation from its smooth realization

This proposition names the smooth-vector comparison for a dense equivariant
realization preserving an actual invariant positive form. It supplies no proof
or completion construction.
-/

namespace Langlands

universe uG uV uH

/-- In a dense continuous realization preserving the invariant positive form of
an admissible representation, the vectors with open stabilizer are exactly the
image of the original algebraic carrier. -/
def AdmissibleSmoothVectorRecovery : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), IsAdmissible ρ →
      ∀ (b : InvariantPositiveForm ρ)
        (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Representation ℂ G H),
        (∀ g : G, Continuous (σ g)) →
        ∀ j : ρ.IntertwiningMap σ,
          DenseRange j →
          (∀ v w : V, inner ℂ (j v) (j w) = b.inner v w) →
          ∀ w : H, w ∈ smoothVectors σ ↔ ∃ v : V, j v = w

end Langlands
