/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Global sections of the pullback along an étale morphism

For an étale morphism `f: P ⟶ V`, the pullback `f^*` of étale sheaves is the restriction along
the localization functor `P_ét ⥤ V_ét`
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`).
Hence the global sections of `f^* F` are the sections of `F` over the étale `V`-scheme `P`,
naturally in `F`.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarCompSectionsIso`: `Γ(P, f^* F) ≅ F(P)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {P V : Scheme.{u}} (f : P ⟶ V) [AlgebraicGeometry.Etale f]

/-- The image of the terminal object of `P_ét` under the localization functor along an étale
`f: P ⟶ V` is `P`, as an étale `V`-scheme. -/
noncomputable def overMapTerminalIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale f)).obj
      (⊤_ P.Etale) ≅ Scheme.Etale.mk f :=
  (MorphismProperty.Over.map ⊤ _).mapIso
      (terminalIsoIsTerminal (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale P)) ≪≫
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp; rfl)

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Global sections of the pullback along an étale morphism**: for `f: P ⟶ V` étale, the global
sections of
`f^* F` are the sections of `F` over the étale `V`-scheme `P`, naturally in `F`. -/
noncomputable def upperStarCompSectionsIso :
    (f)^*[A] ⋙ (sheafSections P.smallEtaleTopology A).obj (op (⊤_ P.Etale)) ≅
      (sheafSections V.smallEtaleTopology A).obj (op (Scheme.Etale.mk f)) :=
  Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A f inferInstance) _ ≪≫
    NatIso.ofComponents (fun F ↦ F.obj.mapIso (overMapTerminalIso f).symm.op)
      (fun φ ↦ (φ.hom.naturality _).symm)

end AlgebraicGeometry.Etale
