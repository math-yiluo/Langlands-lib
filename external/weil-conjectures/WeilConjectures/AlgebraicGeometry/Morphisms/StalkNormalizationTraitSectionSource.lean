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
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified

/-!
# Source etaleness over the local section in the trait case

## References

* Stacks Project, Tags 0EYJ, 0EYG, 0EYH and 0EYI
* Stacks Project, Tag 0EYJ, trait paragraph, and Tag 0EYI(2)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem stalk_dvr {S : Scheme.{u}} [IsNoetherian S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (U : S.Opens) (hηU : genericPoint S ∈ U) (s : S) (hs : s ∉ U)
    (hdim : ringKrullDim (S.presheaf.stalk s) < (2 : WithBot ℕ∞)) :
    IsDiscreteValuationRing (S.presheaf.stalk s) := by
  have hfield : ¬ IsField (S.presheaf.stalk s) := by
    intro h
    let : Field (S.presheaf.stalk s) := h.toField
    have hgen : genericPoint S ⤳ s :=
      (genericPoint_spec S).specializes_iff_mem.mpr (Set.mem_univ s)
    have hmem : genericPoint S ∈ Set.range (S.fromSpecStalk s) := by
      rw [S.range_fromSpecStalk]
      exact hgen
    obtain ⟨y, hy⟩ := hmem
    have hyclosed : y = IsLocalRing.closedPoint (S.presheaf.stalk s) :=
      (inferInstance : Subsingleton (PrimeSpectrum (S.presheaf.stalk s))).elim _ _
    rw [hyclosed, S.fromSpecStalk_closedPoint] at hy
    exact hs (hy.symm ▸ hηU)
  let : IsIntegrallyClosed (S.presheaf.stalk s) := hS s
  let : Ring.KrullDimLE 1 (S.presheaf.stalk s) := Ring.krullDimLE_iff.mpr
    (ENat.WithBot.lt_add_one_iff.mp (by norm_num; exact hdim))
  let : Ring.DimensionLEOne (S.presheaf.stalk s) :=
    ⟨fun hp hprime ↦ hprime.isMaximal_of_ne_bot hp⟩
  let : IsDedekindDomain (S.presheaf.stalk s) := {}
  exact ((IsDiscreteValuationRing.TFAE (S.presheaf.stalk s) hfield).out 3 1).mp
    (show IsDedekindDomain (S.presheaf.stalk s) from inferInstance)

/-- Every point of the finite local normalization above the closed section point
has a source open neighbourhood on which the normalization map is etale,
when the local base has dimension less than two. -/
theorem GaloisCover.stalk_normalization_trait_section_source {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdim : ringKrullDim (S.presheaf.stalk s) < (2 : WithBot ℕ∞)) :
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
        (pullback.fst c a)).Opens, x ∈ V ∧ Etale (V.ι ≫ n) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  have hdvr := stalk_dvr hS U hηU s hs hdim
  dsimp only
  intro hn x hx
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c (S.fromSpecStalk s))
  let : IsFinite n := hn
  let : Flat n := GaloisCover.stalk_normalization_trait_flat
    c G hG q j hCη Z U jU PA ψ hjU hψ s hs hmin hdvr hn
  obtain ⟨V, hxV, hV⟩ := GaloisCover.stalk_normalization_trait_section_unramified
    c σ hσ G hG q j hCη sη hsj Z hZ U jU PA ψ hjU hψ
    s hs hmin hdvr hn x hx
  let : FormallyUnramified (V.ι ≫ n) := hV
  refine ⟨V, hxV, ?_⟩
  exact Etale.of_formallyUnramified_of_flat (V.ι ≫ n)

end AlgebraicGeometry.Scheme
