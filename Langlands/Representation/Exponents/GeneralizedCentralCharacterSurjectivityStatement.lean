import Langlands.Representation.Exponents.Central
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Surjectivity on actual uniform generalized central-character spaces -/

namespace Langlands

universe uG uV uW

/-- An intertwiner that is onto on the ambient carriers remains onto on each
uniform generalized central-character space, when the source's full-centre
action operators span a finite-dimensional space of endomorphisms. -/
def GeneralizedCentralCharacterSurjectivityStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ρ (z : G)))) →
    ∀ (f : ρ.IntertwiningMap σ), Function.Surjective f →
      ∀ (χ : Subgroup.center G →* ℂˣ),
        Function.Surjective (generalizedCentralCharacterMap f χ)

end Langlands
