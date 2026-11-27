import Langlands.BushnellKutzko.RepresentationIntertwining
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Coinduced

/-! # Extracting an extension in the induced degree -/

namespace Langlands.BushnellKutzko

universe uG uV uW

/-- A split copy of a subgroup representation extends to the intermediate group
which contains its self-intertwining, when the ambient degree equals the induced
degree from that group. -/
def ExtensionFromInducedDegreeStatement : Prop :=
  ∀ (G : Type uG) [Group G] (H A : Subgroup G) [A.FiniteIndex] (hHA : H ≤ A)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (π : Representation ℂ G W)
    (i : ρ.IntertwiningMap (π.comp H.subtype))
    (p : Representation.IntertwiningMap (π.comp H.subtype) ρ),
    (∀ v, p (i v) = v) →
    (∀ x, Intertwines ρ ρ x → x ∈ A) →
    Module.finrank ℂ W = A.index * Module.finrank ℂ V →
    ∃ κ : Representation ℂ A V, κ.comp (Subgroup.inclusion hHA) = ρ ∧
      Nonempty (π.Equiv (Representation.coind A.subtype κ)) ∧
      ∀ (j : ρ.IntertwiningMap (π.comp H.subtype)) (v : V), j v = i (p (j v))

end Langlands.BushnellKutzko
