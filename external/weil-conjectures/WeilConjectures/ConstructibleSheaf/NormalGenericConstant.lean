/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Constant sheaves on a normal Noetherian scheme

Let `V` be a Noetherian normal integral scheme with generic point `e : Spec K ⟶ V`. For a finite
module `M` the natural map `M_V ⟶ e_* M_K` of étale sheaves is an isomorphism
(`AlgebraicGeometry.Etale.isIso_constantSheaf_toLowerStar_genericPoint`, blueprint
`proposition-proper-direct-image-finite-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The natural map `M_V ⟶ e_* M_K` from a constant sheaf on `V` to the direct image of the
constant sheaf along a morphism `e : W ⟶ V`: the unit of `e^* ⊣ e_*` followed by the
identification `e^* M_V ≅ M_W`. -/
def Etale.constantSheafToLowerStar {V W : Scheme.{u}} (e : W ⟶ V) (M : ModuleCat.{u + 1} Λ) :
    (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (e)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).unit.app _ ≫
    (e)_*[ModuleCat.{u + 1} Λ].map ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) e).hom.app M)

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: A generic constant sheaf on a
normal Noetherian scheme.

Let `V` be a Noetherian normal integral scheme (integral, with integrally closed local rings),
with generic inclusion `e : Spec K ⟶ V`. For a finite `Λ`-module `M` (for instance a finite
abelian group, `Λ = ℤ/N`), the natural map `M_V ⟶ e_* M_K` of étale sheaves is an
isomorphism. -/
theorem Etale.isIso_constantSheaf_toLowerStar_genericPoint {V : Scheme.{u}} [IsNoetherian V]
    [IsIntegral V] (hV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsIso (Etale.constantSheafToLowerStar (V.fromSpecStalk (genericPoint V)) M) := by
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed Λ hV M).1 inferInstance

end AlgebraicGeometry

end
