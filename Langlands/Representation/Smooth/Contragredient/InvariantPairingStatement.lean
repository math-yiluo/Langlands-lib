import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Basic.Complex.Basic

/-!
# Smooth-dual perfectness of an invariant bilinear pairing

This proposition target assumes compact-open cofinality, admissibility on one
side, smoothness on the other, and two-sided nondegeneracy. No pairing is
constructed and no proof of the target is supplied here.
-/

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An invariant bilinear pairing, nondegenerate on both sides, identifies a
smooth representation with the smooth dual of an admissible representation,
provided compact open subgroups are cofinal among open subgroups. -/
def SmoothInvariantPairingDualityStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
      IsAdmissible ρ → IsSmooth σ →
      ∀ b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ,
        (∀ (g : G) (w : W) (v : V), b (σ g w) (ρ g v) = b w v) →
        (∀ w : W, (∀ v : V, b w v = 0) → w = 0) →
        (∀ v : V, (∀ w : W, b w v = 0) → v = 0) →
        ∃ E : Representation.Equiv σ (smoothContragredient ρ),
          ∀ (w : W) (v : V), smoothDualPairing ρ (E w) v = b w v

end Langlands
