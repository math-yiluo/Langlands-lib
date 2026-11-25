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

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity

/-!
# Etaleness of the finite normalization over a stalk

## References

* Stacks Project, Tag 0EYJ, proof of the local claim
* Stacks Project, Tag 0EYJ, local claim
* Stacks Project, local claim
* Tags 0EYI, 0EYE, 0EY9 and 0EYB
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem normalization_etale_restrict {P X : Scheme.{u}} (V : X.Opens)
    (π : P ⟶ V.toScheme) [IsFinite π] [Etale π] [QuasiCompact V.ι] :
    Etale ((π ≫ V.ι).fromNormalization ∣_ V) := by
  let f := π ≫ V.ι
  have hpb : IsPullback (𝟙 P) π f V.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  have hfin : IsFinite (pullback.snd f V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  have het : Etale (pullback.snd f V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  have hn : Etale (pullback.snd f V.ι).fromNormalization := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
      (pullback.snd f V.ι).toNormalization, Hom.toNormalization_fromNormalization]
    exact het
  have hp : Etale (pullback.snd f.fromNormalization V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale (f.normalizationPullback V.ι),
      Hom.normalizationPullback_snd]
    exact hn
  rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
    (pullbackRestrictIsoRestrict f.fromNormalization V).hom,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]
  exact hp

/-- Local affine-chart form of the stalk normalization claim: if the normalization over the
stalk at a generic boundary point `s` is finite, then its ring maps on all affine charts are
étale. -/
theorem GaloisCover.stalk_normalization_etale_local_charts {S C : Scheme.{u}} [IsNoetherian S]
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
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) →
    ∀ {V : (pullback c (S.fromSpecStalk s)).Opens} (_ : IsAffineOpen V)
      {W : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))).Opens} (_ : IsAffineOpen W)
      (e : W ≤ (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))) ⁻¹ᵁ V),
      ((pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))).appLE V W e).hom.Etale := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro hfin
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c (S.fromSpecStalk s))
  have hn : Etale n := by
    obtain ⟨W, hW, het⟩ := GaloisCover.stalk_normalization_section_neighbourhood
      hS c σ hσ G hG q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ s hs hmin hfin
    let a := S.fromSpecStalk s
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    have hτ : τ ≫ pullback.fst c a ≫ c = a := by
      simp [τ, Category.assoc, hσ]
    apply stalk_normalization_etale_of_fibre_neighbourhood hS c U hηU PA s hs hmin hfin
      (normalization_etale_restrict (c ⁻¹ᵁ U) PA.obj.hom)
    refine ⟨W, τ (IsLocalRing.closedPoint (S.presheaf.stalk s)), hW, ?_, het⟩
    rw [← Hom.comp_apply, hτ]
    exact S.fromSpecStalk_closedPoint
  let : Etale n := hn
  intro V hV W hW e
  exact n.etale_appLE hV hW e

/-- Etaleness of the finite normalization at a generic boundary point. -/
theorem GaloisCover.stalk_normalization_etale {S C : Scheme.{u}} [IsNoetherian S]
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
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) →
    Etale (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro hfin
  refine ⟨?_⟩
  exact GaloisCover.stalk_normalization_etale_local_charts hS c σ hσ G hG q j hCη sη hsq hsj Z hZ
    U hηU jU PA ψ hjU hψ s hs hmin hfin

end AlgebraicGeometry.Scheme
