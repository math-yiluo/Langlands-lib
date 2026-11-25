/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import WeilConjectures.RingTheory.Depth

public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.MvPowerSeriesFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.NormalLocalDepthTwo

/-!
# Boundary depths in the formal test for the stalk normalization

## References

* Stacks Project, Tag 0EYJ; Tags 0EY6, 0EY9, 0337 and 031S
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem depth_le_of_flat_stalk {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (x : X) :
    IsLocalRing.depth (R := Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) ≤
      IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x) := by
  obtain ⟨_, hlocal, _, hd⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (f.stalkMap x).hom (Flat.stalkMap f x)
  rw [hd]
  exact le_self_add

/-- Over a flat power-series chart at a boundary point `s` of depth at least `2`, the pulled-back
finite normalization and the trivial `G`-cover have depth at least `2` at all points lying
outside the preimage of `U`. -/
theorem GaloisCover.stalk_normalization_formal_boundary_depths {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Finite G]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      Flat t →
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      (∀ x : F, r x ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk x) (F.presheaf.stalk x)) ∧
      (∀ x : E, p x ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk x) (E.presheaf.stalk x)) := by
  dsimp only
  intro hn d t ht hbase
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
  let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
  let V := (t ≫ l) ⁻¹ᵁ (c ⁻¹ᵁ U)
  let b : T ⟶ Spec (S.presheaf.stalk s) :=
    Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d)))
  have : IsFinite n := hn
  have : Flat t := ht
  have : Flat b := Flat.SpecMap_iff.mpr
    (MvPowerSeries.constants_flat (S.presheaf.stalk s) d)
  have : IsLocallyNoetherian (pullback c a) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian n
  have : IsLocallyNoetherian (pullback n t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd n t)
  have hdim := stalk_normalization_boundary_dimension_two hS c U PA s hmin hdepth hn
  have hnormal := stalk_normalization_normal_part hS c U PA s
  have hN : ∀ z : N, n z ∉ l ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := N.presheaf.stalk z) (N.presheaf.stalk z) := by
    intro z hz
    let : IsDomain (N.presheaf.stalk z) := (hnormal z).1
    let : IsIntegrallyClosed (N.presheaf.stalk z) := (hnormal z).2
    exact IsLocalRing.depth_two_of_normal (N.presheaf.stalk z) (hdim z hz)
  have hclosed : ∀ y : T, y ∉ V →
      b y = IsLocalRing.closedPoint (S.presheaf.stalk s) := by
    intro y hy
    have hs' : (l ≫ c) (t y) = s := by
      apply hmin
      · have heq : l ≫ c = q ≫ a := pullback.condition
        rw [heq, Hom.comp_apply]
        exact ((IsLocalRing.specializes_closedPoint (q (t y))).map a.continuous).trans
          (specializes_of_eq S.fromSpecStalk_closedPoint)
      · exact hy
    apply a.isEmbedding.injective
    have heq : t ≫ q = b := hbase
    rw [← heq, Hom.comp_apply, S.fromSpecStalk_closedPoint]
    change a (q (t y)) = s
    rw [← Hom.comp_apply, ← pullback.condition]
    exact hs'
  have hT : ∀ y : T, y ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := T.presheaf.stalk y) (T.presheaf.stalk y) := by
    intro y hy
    have hA : (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (S.presheaf.stalk s)).presheaf.stalk (b y))
        ((Spec (S.presheaf.stalk s)).presheaf.stalk (b y)) := by
      rw [hclosed y hy]
      let e := (stalkClosedPointIso (S.presheaf.stalk s)).commRingCatIsoToRingEquiv.symm
      let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
      obtain ⟨_, hlocal, _, hd⟩ := IsLocalRing.depth_eq_add_of_flat_local e.toRingHom
        (RingHom.Flat.of_bijective e.bijective)
      rw [hd]
      exact hdepth.trans le_self_add
    exact hA.trans (depth_le_of_flat_stalk b y)
  constructor
  · intro x hx
    let g := pullback.fst n t
    have hnot : n (g x) ∉ l ⁻¹ᵁ (c ⁻¹ᵁ U) := by
      have heq : n (g x) = t ((pullback.snd n t) x) := by
        rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
      rw [heq]
      exact hx
    exact (hN (g x) hnot).trans (depth_le_of_flat_stalk g x)
  · let p : (∐ (fun _ : G ↦ T) : Scheme.{u}) ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
    have : Flat p := inferInstance
    have : LocallyOfFiniteType p :=
      IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)
    have : IsLocallyNoetherian (∐ (fun _ : G ↦ T) : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian p
    intro x hx
    exact (hT (p x) hx).trans (depth_le_of_flat_stalk p x)

end AlgebraicGeometry.Scheme
