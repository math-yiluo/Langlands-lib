import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-!
# Continuation of unitarizability along a connected parameter set

A family `s ↦ π s` of representations of one topological group on one complex
vector space, indexed by real parameters in a preconnected set `J`, is
considered. The family has the same action on a fixed compact open subgroup,
every member is admissible and irreducible and admits a nonzero invariant
sesquilinear form, and matrix entries depend continuously on the parameter.
The proposition says that unitarizability at one parameter of `J` propagates to
every parameter of `J`. This is the soft analytic step of Zelevinsky 1980,
Proposition 1.11, printed p.175. This module supplies the proposition only.
-/

namespace Langlands

universe uG uV

/-- Unitarizability continues along a preconnected real parameter set `J` for a
family `π` of representations on one carrier `V`, when the members agree on a
compact open subgroup `K`, are admissible and irreducible, each admits a nonzero
invariant sesquilinear form, and every scalar `ℓ (π s g v)` is continuous on `J`.
This definition supplies the proposition only. -/
def UnitarizabilityContinuationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : ℝ → Representation ℂ G V) (J : Set ℝ) (K : OpenSubgroup G),
    IsCompact (K : Set G) → IsPreconnected J →
    (∀ s ∈ J, ∀ t ∈ J, ∀ k ∈ K, π s k = π t k) →
    (∀ s ∈ J, IsAdmissible (π s)) →
    (∀ s ∈ J, (π s).IsIrreducible) →
    (∀ s ∈ J, ∃ b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, b ≠ 0 ∧
      ∀ (g : G) (v w : V), b (π s g v) (π s g w) = b v w) →
    (∀ (g : G) (v : V) (ℓ : Module.Dual ℂ V),
      ContinuousOn (fun s => ℓ (π s g v)) J) →
    ∀ s₀ ∈ J, IsUnitarizable (π s₀) → ∀ s ∈ J, IsUnitarizable (π s)

end Langlands
