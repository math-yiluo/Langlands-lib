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
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood

/-!
# Unramifiedness along a split trait section

## References

* Stacks Project, Tags 0EYG, 0EYH, 0EYI and 0EYJ
* Stacks Project, Tag 0EYI(2), applied as in Tag 0EYJ, trait paragraph
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Splitting along the generic section kills the relative differentials near
all points above the closed section point. -/
theorem GaloisCover.stalk_normalization_trait_section_unramified {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      ∃ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)).Opens, x ∈ V ∧ FormallyUnramified (V.ι ≫ n) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn x hx
  have := hn
  have hm := GaloisCover.stalk_normalization_trait_section_maximalIdeal
    c σ hσ G hG q j hCη sη hsj Z hZ U jU PA ψ hjU hψ s hs hmin hdvr hn x hx
  have hr := GaloisCover.stalk_normalization_trait_section_residue_separable
    c σ hσ G hG q j hCη Z U jU PA ψ hjU hψ s hs hmin hdvr hn x hx
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c (S.fromSpecStalk s))
  apply FormallyUnramified.exists_neighbourhood_of_stalkMap n x
  algebraize [(n.stalkMap x).hom]
  have : IsLocalHom
      (algebraMap ((pullback c (S.fromSpecStalk s)).presheaf.stalk (n x))
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c (S.fromSpecStalk s))).presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (n.stalkMap x).hom
  have : Algebra.EssFiniteType
      ((pullback c (S.fromSpecStalk s)).presheaf.stalk (n x))
      ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))).presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap n x
  have := hr
  rw [← RingHom.algebraMap_toAlgebra (n.stalkMap x).hom,
    RingHom.formallyUnramified_algebraMap]
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hm

end AlgebraicGeometry.Scheme
