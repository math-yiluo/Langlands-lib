/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleStalkNeighbourhoodSpreading

/-!
# Local extension with an overlap comparison

## References

* Stacks Project, Tag 0EYJ, local claim and spreading, and Tags 0BQ5 and 0EY3
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite étale model extends near a point outside the original open, with an
isomorphism of the two covers on the overlap. The neighbourhood need not contain U. -/
theorem GaloisCover.exists_local_finiteEtale_model_overlap {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U) (hU : U ≠ ⊤)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU) :
    ∃ (W : S.Opens) (s : S), s ∉ U ∧ s ∈ W ∧
      ∃ Q : (c ⁻¹ᵁ W).toScheme.FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ U))).obj PA ≅
          (FiniteEtale.pullback
          (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W))).obj Q) := by
  obtain ⟨s, hs, Q, e⟩ :=
    GaloisCover.exists_stalk_finiteEtale_model hS c σ hσ G hG
      q j hCη sη hsq hsj Z hZ U hηU hU jU PA ψ hjU hψ
  obtain ⟨W, hsW, R, eR⟩ :=
    FiniteEtale.exists_neighbourhood_model_of_stalk c U PA s Q e
  exact ⟨W, s, hs, hsW, R, eR⟩

end AlgebraicGeometry.Scheme
