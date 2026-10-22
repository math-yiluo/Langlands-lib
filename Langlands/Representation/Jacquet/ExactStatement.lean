import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Coinvariants

namespace Langlands

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Compact detection of coinvariant relations and exactness of smooth complex
coinvariants when every finite subset lies in a compact open subgroup. -/
def SmoothCoinvariantExactnessStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ s : Finset G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ ∀ g ∈ s, g ∈ K) →
    (∀ rho : Representation ℂ G V, IsSmooth rho →
      ∀ v : V, v ∈ Representation.Coinvariants.ker rho ↔
        ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
          v ∈ Representation.Coinvariants.ker (rho.comp K.toSubgroup.subtype)) ∧
    (∀ (rho : Representation ℂ G U) (sigma : Representation ℂ G V)
      (tau : Representation ℂ G W)
      (i : rho.IntertwiningMap sigma) (p : sigma.IntertwiningMap tau),
      Function.Injective i → Function.Surjective p →
      LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap →
      IsSmooth sigma →
      Function.Injective (Representation.Coinvariants.map rho sigma i) ∧
      LinearMap.range (Representation.Coinvariants.map rho sigma i) =
        LinearMap.ker (Representation.Coinvariants.map sigma tau p) ∧
      Function.Surjective (Representation.Coinvariants.map sigma tau p))

end Langlands
