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

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource

/-!
# Etaleness near the local section of a normalization

## References

* Stacks Project, Tag 0EYJ, local computation
* Stacks Project, formal section calculation
* Tag 0EYI (split-section trait test), Tag 0EY9 (power series full faithfulness), and Tag 0EY6 (flat
  base change for the depth-two extension)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Finiteness lets source-local etaleness around the whole fibre give a target open.
private theorem etale_shrink_of_fibre_source_opens {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y)
    (h : ∀ x : X, f x = y → ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) :
    ∃ W : Y.Opens, y ∈ W ∧ Etale (f ∣_ W) := by
  classical
  let E : X.Opens := ⨆ V : {V : X.Opens // Etale (V.ι ≫ f)}, V.val
  let W : Y.Opens := ⟨(f '' (E : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ E.isOpen.isClosed_compl).isOpen_compl⟩
  have hy : y ∈ W := by
    rintro ⟨x, hx, hxy⟩
    obtain ⟨V, hxV, hV⟩ := h x hxy
    apply hx
    exact (le_iSup (fun V : {V : X.Opens // Etale (V.ι ≫ f)} ↦ V.val)
      ⟨V, hV⟩) hxV
  have hle : f ⁻¹ᵁ W ≤ E := by
    intro x hx
    by_contra hxE
    exact hx ⟨x, hxE, rfl⟩
  let g := f ∣_ W
  have hlocal (x : (f ⁻¹ᵁ W).toScheme) :
      ∃ V : (f ⁻¹ᵁ W).toScheme.Opens, x ∈ V ∧ Etale (V.ι ≫ g) := by
    have hxE : (f ⁻¹ᵁ W).ι x ∈ E := hle x.property
    obtain ⟨V, hxV⟩ := (TopologicalSpace.Opens.mem_iSup.mp hxE)
    let T := (f ⁻¹ᵁ W).ι ⁻¹ᵁ V.val
    have hT : Etale (T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f) := by
      have hcomp : T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f =
          ((f ⁻¹ᵁ W).ι ∣_ V.val) ≫ V.val.ι ≫ f := by
        simp only [← Category.assoc, morphismRestrict_ι]
        rfl
      rw [hcomp]
      let : Etale (V.val.ι ≫ f) := V.property
      infer_instance
    have hT' : Etale ((T.ι ≫ g) ≫ W.ι) := by
      simpa only [Category.assoc, g, morphismRestrict_ι] using hT
    let := hT'
    exact ⟨T, hxV, AlgebraicGeometry.Etale.of_comp (T.ι ≫ g) W.ι⟩
  choose V hxV hV using hlocal
  have htop : (⨆ x, V x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  exact ⟨W, hy, IsZariskiLocalAtSource.of_iSup_eq_top V htop hV⟩

/-- The section meets an open over which the finite local normalization is etale. -/
theorem GaloisCover.stalk_normalization_section_neighbourhood {S C : Scheme.{u}} [IsNoetherian S]
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
    let a := S.fromSpecStalk s
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    ∃ W : (pullback c a).Opens,
      τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ W ∧
      Etale ((pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)) ∣_ W) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro hfin
  let a := S.fromSpecStalk s
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
  let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
    pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  let : IsFinite n := hfin
  apply etale_shrink_of_fibre_source_opens n (τ (IsLocalRing.closedPoint _))
  by_cases hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (S.presheaf.stalk s)
  · exact GaloisCover.stalk_normalization_depth_two_section_source
      hS c σ hσ G hG q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ s hs hmin hdim hfin
  · exact GaloisCover.stalk_normalization_trait_section_source
      hS c σ hσ G hG q j hCη sη hsj Z hZ U hηU jU PA ψ hjU hψ s hs hmin
      (lt_of_not_ge hdim) hfin

end AlgebraicGeometry.Scheme
