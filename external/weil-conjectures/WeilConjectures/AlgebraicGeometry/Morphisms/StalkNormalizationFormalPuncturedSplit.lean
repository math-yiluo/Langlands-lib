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

public import WeilConjectures.RingTheory.Depth

public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedRestrict
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalZeroSliceSplit
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSplitAssembly
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful

/-!
# Splitting of the stalk normalization over the punctured formal chart

## References

* Stacks Project, Tag 0EYJ; Tags 0EY6, 0EY9, 0337 and 031S
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Over a flat power-series chart through the section at a boundary point `s` of depth at
least `2`, the pulled-back finite normalization is isomorphic to the trivial `G`-cover over the
preimage of `U`. -/
theorem GaloisCover.exists_stalk_normalization_formal_punctured_split {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
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
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      Flat t →
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d))) ≫ t = τ →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ (r ⁻¹ᵁ V).toScheme,
        e.hom ≫ r ∣_ V = p ∣_ V := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn d t ht hb hz
  have h := stalk_normalization_formal_punctured_restriction
    c G U PA s hs hmin d t hb
  dsimp only at h
  obtain ⟨hp, hep, hr, her, hV⟩ := h
  have hslice := GaloisCover.stalk_normalization_formal_zero_slice_split
    hS c σ hσ G q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ
    s d t hb hz
  dsimp only at hslice
  obtain ⟨e₀, he₀⟩ := hslice
  let := hp
  let := hep
  let := hr
  let := her
  refine powerSeries_punctured_split_assembly _ _ _ ?_ e₀ he₀
  by_cases hd : d = 0
  · subst d
    left
    have hz : IsIso (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin 0) :
          MvPowerSeries (Fin 0) (S.presheaf.stalk s) →+* S.presheaf.stalk s))) := by
      let e := (MvPowerSeries.isEmptyEquiv (Fin 0) (S.presheaf.stalk s)).toRingEquiv
      change IsIso (Scheme.Spec.map e.toCommRingCatIso.hom.op)
      infer_instance
    infer_instance
  · right
    exact finiteEtale_powerSeries_punctured_section_fully_faithful
      (S.presheaf.stalk s) hdepth d (Nat.pos_of_ne_zero hd) _ hV

end AlgebraicGeometry.Scheme
