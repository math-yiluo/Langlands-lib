import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.LocallyConstant.Basic

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Scalar endomorphisms, the Schur Hom-space dichotomy, and the unique smooth
central character of an irreducible admissible complex representation. -/
def AdmissibleSchurStatement : Prop :=
  ∀ [IsTopologicalGroup G] (rho : Representation ℂ G V),
    IsAdmissible rho → rho.IsIrreducible →
    (∀ f : rho.IntertwiningMap rho,
      ∃! c : ℂ, f = c • Representation.IntertwiningMap.id rho) ∧
    (∀ sigma : Representation ℂ G W,
      IsAdmissible sigma → sigma.IsIrreducible →
      (Nonempty (rho.Equiv sigma) →
        Nonempty ((rho.IntertwiningMap sigma) ≃ₗ[ℂ] ℂ)) ∧
      (¬ Nonempty (rho.Equiv sigma) →
        ∀ f : rho.IntertwiningMap sigma, f = 0)) ∧
    (∃! chi : Subgroup.center G →* ℂˣ,
      IsLocallyConstant (chi : Subgroup.center G → ℂˣ) ∧
      ∀ (z : Subgroup.center G) (v : V), rho (z : G) v = (chi z : ℂ) • v)

end Langlands
