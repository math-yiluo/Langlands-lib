import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Intertwining

namespace Langlands

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Admissibility is closed under subobjects, quotients, and extensions in a
short exact sequence whose middle representation is smooth. -/
def AdmissibleShortExactStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H) →
    ∀ (rho : Representation ℂ G U) (sigma : Representation ℂ G V)
      (tau : Representation ℂ G W)
      (i : rho.IntertwiningMap sigma) (p : sigma.IntertwiningMap tau),
      Function.Injective i → Function.Surjective p →
      LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap →
      IsSmooth sigma →
      (IsAdmissible sigma ↔ IsAdmissible rho ∧ IsAdmissible tau)

end Langlands
