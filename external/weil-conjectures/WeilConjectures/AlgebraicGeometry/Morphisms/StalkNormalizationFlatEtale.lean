/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import WeilConjectures.RingTheory.Depth

import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity

/-!
# Purity turns flatness of a depth-two normalization into etaleness

## References

* Stacks Project, Tag 0EY6, assertion (3), applied to the local normalization in the proof of Tag
  0EYJ
* Stacks Project, Tag 0EY6, assertions (2) and (3)
* Tag 0EYJ, proof of the local claim, paragraph starting with depth(A) at least two
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Normalization recovers the finite map on its original open, for any
-- morphism property invariant under source isomorphisms.
private theorem morphismProperty_normalization_restrict_iff
    (p : MorphismProperty Scheme.{u}) [p.RespectsIso]
    {P X : Scheme.{u}} (V : X.Opens)
    (π : P ⟶ V.toScheme) [IsFinite π] [QuasiCompact V.ι] :
    p ((π ≫ V.ι).fromNormalization ∣_ V) ↔ p π := by
  let f := π ≫ V.ι
  have hpb : IsPullback (𝟙 P) π f V.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  have hfin : IsFinite (pullback.snd f V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  rw [← p.cancel_left_of_respectsIso (pullbackRestrictIsoRestrict f.fromNormalization V).hom,
    pullbackRestrictIsoRestrict_hom_morphismRestrict,
    ← p.cancel_left_of_respectsIso (f.normalizationPullback V.ι),
    Hom.normalizationPullback_snd,
    ← p.cancel_left_of_respectsIso (pullback.snd f V.ι).toNormalization,
    Hom.toNormalization_fromNormalization,
    ← p.cancel_left_of_respectsIso hpb.isoPullback.hom, hpb.isoPullback_hom_snd]

-- Restriction commutes with pullback for every property stable under base change.
set_option backward.isDefEq.respectTransparency false in
private theorem morphismProperty_pullback_restrict
    (p : MorphismProperty Scheme.{u}) [p.IsStableUnderBaseChange]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (U : Y.Opens) (hf : p (f ∣_ U)) :
    p (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  let n := pullback.snd f g
  have hp := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := n ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl le_rfl (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
      exact (inf_idem _).symm)
  dsimp only [n] at hp
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hp
  exact p.of_isPullback hp hf

-- The unchanged statement includes normality and generic-density hypotheses;
-- the flat source-open proof below does not need them.
/-- On the finite local normalization, every flat source open is etale.
No section, group action, or generic rational point is assumed. -/
theorem finiteEtale_stalk_normalization_etale_of_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
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
    IsFinite n → ∀ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a)).Opens, Flat (V.ι ≫ n) → Etale (V.ι ≫ n) := by
  dsimp only
  intro hn V hflat
  have : IsFinite PA.obj.hom := PA.property
  have : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let a := S.fromSpecStalk s
  let l := pullback.fst c a
  let q := pullback.snd c a
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let n := pullback.snd f.fromNormalization l
  let N := pullback f.fromNormalization l
  let T := l ⁻¹ᵁ (c ⁻¹ᵁ U)
  let W := V.ι ⁻¹ᵁ (n ⁻¹ᵁ T)
  have : IsFinite n := hn
  have : Flat (V.ι ≫ n) := hflat
  have : IsLocallyNoetherian (pullback c a) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian n
  have hetT : Etale (n ∣_ T) := morphismProperty_pullback_restrict @Etale
    f.fromNormalization l (c ⁻¹ᵁ U)
    ((morphismProperty_normalization_restrict_iff @Etale (c ⁻¹ᵁ U) PA.obj.hom).mpr
      (inferInstance : Etale PA.obj.hom))
  have hetW : Etale (W.ι ≫ (V.ι ≫ n)) := by
    let j := V.ι.resLE (n ⁻¹ᵁ T) W le_rfl
    have : Etale j := inferInstance
    have : Etale ((n ⁻¹ᵁ T).ι ≫ n) := by
      rw [← morphismRestrict_ι]
      infer_instance
    have heq : W.ι ≫ V.ι = j ≫ (n ⁻¹ᵁ T).ι := by simp [j]
    rw [← Category.assoc, heq, Category.assoc]
    infer_instance
  have hboundary : ∀ y : (pullback c a : Scheme.{u}),
      y ∉ T ↔ (l ≫ c) y = s := by
    intro y
    constructor
    · intro hy
      apply hmin
      · have hp := pullback.condition (f := c) (g := a)
        change (l ≫ c) y ⤳ s
        rw [hp]
        exact ((IsLocalRing.specializes_closedPoint (q y)).map a.continuous).trans
          (specializes_of_eq fromSpecStalk_closedPoint)
      · exact hy
    · intro hy hmem
      exact hs (hy ▸ hmem)
  apply etale_of_flat_quasiFinite_depth_two_boundary (V.ι ≫ n) W hetW
  intro x hx
  have hnot : n (V.ι x) ∉ T := hx
  have hxs : (l ≫ c) (n (V.ι x)) = s := (hboundary _).mp hnot
  let r := (V.ι ≫ n) ≫ q
  have : Flat r := inferInstance
  have hrx : r x = IsLocalRing.closedPoint (S.presheaf.stalk s) := by
    apply a.isEmbedding.injective
    change ((V.ι ≫ n) ≫ q ≫ a) x = a (IsLocalRing.closedPoint _)
    rw [← pullback.condition]
    simpa only [l, a, Hom.comp_apply, fromSpecStalk_closedPoint] using hxs
  have hbase : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (Spec (S.presheaf.stalk s)).presheaf.stalk (r x))
      ((Spec (S.presheaf.stalk s)).presheaf.stalk (r x)) := by
    rw [hrx]
    let e := (stalkClosedPointIso (S.presheaf.stalk s)).commRingCatIsoToRingEquiv.symm
    have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
    obtain ⟨_, hlocal, _, he⟩ := IsLocalRing.depth_eq_add_of_flat_local e.toRingHom
      (RingHom.Flat.of_bijective e.bijective)
    rw [he]
    exact hdepth.trans (le_add_right le_rfl)
  obtain ⟨_, hlocal, _, hformula⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (r.stalkMap x).hom (Flat.stalkMap r x)
  rw [hformula]
  exact hbase.trans (le_add_right le_rfl)

end AlgebraicGeometry.Scheme
