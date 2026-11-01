import Langlands.AlgebraicGeometry.Modules.SectionResidue

/-!
# Vanishing of pulled-back sections in a local frame

This module states that, over an open `U` on which a section `τ` of a module sheaf is a
frame, a global section `s` with local expression `s|_U = a • τ` pulls back to zero along
a morphism landing in `U` exactly when the function `a` pulls back to zero. This module
supplies a statement target, not a proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

/-- Let `τ` be a section of a module sheaf `M` over an open `U` such that, on every open
`W ≤ U`, multiplication `r ↦ r • τ|_W` is a bijection from functions on `W` to sections of
`M` on `W`. If a global section `s` restricts on `U` to `a • τ`, then for every morphism
`g : T ⟶ X` whose preimage of `U` is all of `T`, the pullback of `s` along `g` is zero
exactly when the pullback `g.appLE U ⊤ hg a` of the function `a` is zero.
This proposition is a statement target, not a proof. -/
def FrameVanishingCriterionStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) (τ : Γ(M, U)) (a : Γ(X, U))
    (s : GlobalSections M),
    (∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective (fun r : Γ(X, W) ↦ r • M.presheaf.map (homOfLE hW).op τ)) →
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = a • τ →
    ∀ (T : Scheme.{u}) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U),
      pullbackSection g M s = 0 ↔ g.appLE U ⊤ hg a = 0

end Langlands.SchemeModule
