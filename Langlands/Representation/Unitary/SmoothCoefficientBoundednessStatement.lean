import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Bounded smooth coefficients of admissible unitarizable representations

The statement uses the smooth dual and imposes no norm on the carrier.
-/

namespace Langlands

universe uG uV

/-- Every smooth-dual coefficient of an admissible unitarizable representation
is bounded when compact open subgroups are cofinal. The carrier has no chosen
norm or topology, and the bound may depend on the functional and vector. -/
def AdmissibleUnitarizableSmoothCoefficientsBounded
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] : Prop :=
  ∀ (ρ : Representation ℂ G V),
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    IsAdmissible ρ → IsUnitarizable ρ →
    ∀ (ℓ : SmoothDual ρ) (v : V),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ g : G, ‖smoothDualPairing ρ ℓ (ρ g v)‖ ≤ C

end Langlands
