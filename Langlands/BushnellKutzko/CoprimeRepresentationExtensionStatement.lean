import Langlands.MathlibBase
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Extending an invariant representation across a subgroup of coprime index -/

namespace Langlands.BushnellKutzko

universe uG uW

/-- An invariant irreducible representation extends to the ambient group when it extends over a
finite-index subgroup whose index is coprime to the degree times a determinant exponent. -/
def CoprimeRepresentationExtensionStatement : Prop :=
  ∀ (G : Type uG) [Group G] (N P : Subgroup G) [N.Normal] [P.FiniteIndex],
    ∀ hNP : N ≤ P,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (η : Representation ℂ N W) [η.IsIrreducible],
      (∀ g : G, Nonempty (η.Equiv (η.comp (MulAut.conjNormal g).toMonoidHom))) →
      (∃ ηP : Representation ℂ P W, ηP.comp (Subgroup.inclusion hNP) = η) →
      ∀ a : ℕ, (∀ n : N, LinearMap.det (η n) ^ a = 1) →
        P.index.Coprime (Module.finrank ℂ W * a) →
        ∃ κ : Representation ℂ G W, κ.comp N.subtype = η

end Langlands.BushnellKutzko
