/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundlePicardClassification
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The kernel of restriction to the fibres of a projective line

## References

* EGA II, Remark 4.2.7
* EGA II, Remark 4.2.7, degree-zero case of projective-bundle Picard classification
* Stacks, Tag 0B8W, for descent to finite-presentation models
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules ProjectiveBundleQuotientGeometry
open ProjectiveBundlePicardClassification

private def tensorComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

private theorem pic_map_class {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] :
    Scheme.Pic.map f (Scheme.Pic.ofIsInvertible M) =
      Scheme.Pic.ofIsInvertible ((pullback f).obj M) := by
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso M)⟩

private theorem pow_invertible {X : Scheme.{u}} (A : X.Modules) [A.IsInvertible]
    (n : ℕ) : (tensorPowNat A n).IsInvertible := by
  induction n with
  | zero => exact inferInstanceAs ((𝟙_ X.Modules).IsInvertible)
  | succ n ih =>
    have := ih
    exact inferInstanceAs ((A ⊗ tensorPowNat A n).IsInvertible)

private theorem pow_class {X : Scheme.{u}} (A : X.Modules) [A.IsInvertible]
    (n : ℕ) :
    @Scheme.Pic.ofIsInvertible X (tensorPowNat A n) (pow_invertible A n) =
      Scheme.Pic.ofIsInvertible A ^ n := by
  induction n with
  | zero => exact (pow_zero _).symm
  | succ n ih =>
    have := pow_invertible A n
    change Scheme.Pic.ofIsInvertible (A ⊗ tensorPowNat A n) = _
    rw [Scheme.Pic.ofIsInvertible_tensorObj, ih, pow_succ']

private theorem integer_invertible {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (m : ℤ) : (integerLinePower A hA m).IsInvertible := by
  have := hA
  cases m with
  | ofNat n => exact pow_invertible A n
  | negSucc n => exact pow_invertible (dual A) (n + 1)

private theorem integer_class {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (m : ℤ) :
    @Scheme.Pic.ofIsInvertible X (integerLinePower A hA m) (integer_invertible A hA m) =
      @Scheme.Pic.ofIsInvertible X A hA ^ m := by
  have := hA
  cases m with
  | ofNat n => exact (pow_class A n).trans (zpow_natCast _ _).symm
  | negSucc n =>
    have := pow_invertible (dual A) (n + 1)
    change @Scheme.Pic.ofIsInvertible X (tensorPowNat (dual A) (n + 1)) _ = _
    rw [pow_class, Scheme.Pic.ofIsInvertible_dual, inv_pow, zpow_negSucc]

private theorem pic_map_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (Scheme.Pic.map e.hom) := by
  intro M N h
  have h' := congrArg (Scheme.Pic.map e.inv) h
  simpa only [← Scheme.Pic.map_comp, e.inv_hom_id, Scheme.Pic.map_id] using h'

private def reflect_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (M N : Y.Modules) (a : (pullback e.hom).obj M ≅ (pullback e.hom).obj N) : M ≅ N :=
  (pullbackId Y).symm.app M ≪≫
    (pullbackCongr e.inv_hom_id.symm).app M ≪≫
    (pullbackComp e.inv e.hom).symm.app M ≪≫ (pullback e.inv).mapIso a ≪≫
    (pullbackComp e.inv e.hom).app N ≪≫
    (pullbackCongr e.inv_hom_id).app N ≪≫ (pullbackId Y).app N

private def restrict_pullback_iso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (hf : Set.range f ⊆ U) (M N : X.Modules)
    (a : (tensorPullback U.ι).obj M ≅ (tensorPullback U.ι).obj N) :
    (pullback f).obj M ≅ (pullback f).obj N := by
  let v := IsOpenImmersion.lift U.ι f (by simpa only [Scheme.Opens.range_ι] using hf)
  have hv : v ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  exact (pullbackCongr hv.symm).app M ≪≫ (pullbackComp v U.ι).symm.app M ≪≫
    (pullback v).mapIso ((tensorComparisonIso U.ι).symm.app M ≪≫ a ≪≫
      (tensorComparisonIso U.ι).app N) ≪≫
    (pullbackComp v U.ι).app N ≪≫ (pullbackCongr hv).app N

private theorem exists_standard_classification (S : Scheme.{u}) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S) (A : P.Modules) (hA : A.IsInvertible)
      (e : P ≅ ProjectiveLine S),
      e.hom ≫ (ProjectiveLine S ↘ S) = p ∧
      Nonempty ((pullback e.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1) ≅ A) ∧
      HasPicardClassification p A hA := by
  let E := RelativeProjectiveSpace.freeModule S 1
  have hfree : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 2 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_free 2
  obtain ⟨hE, hC⟩ := projective_bundle_picard_classification S E 2 (by decide)
  have := hE
  obtain ⟨D, _, _, _, _, _, _, hD⟩ := projective_bundle_quotient_geometry S E
  obtain ⟨_, e, t, _, he, _, _⟩ := hD 1 (Iso.refl E)
  exact ⟨_, _, D.line, D.invertible, e, he,
    ⟨(tensorComparisonIso e.hom).symm.app _ ≪≫ t⟩, hC D⟩

private theorem field_degree_zero (k : Type u) [Field k] (m : ℤ)
    (hm : Scheme.Pic.ofIsInvertible
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1) ^ m = 1) : m = 0 := by
  obtain ⟨P, p, A, hA, e, _, ⟨t⟩, hC⟩ := exists_standard_classification (Spec (.of k))
  have := hA
  have hAm : Scheme.Pic.ofIsInvertible A ^ m = 1 := by
    have h := congrArg (Scheme.Pic.map e.hom) hm
    rw [← Scheme.Pic.mapHom_apply, map_zpow, Scheme.Pic.mapHom_apply,
      pic_map_class, Scheme.Pic.ofIsInvertible_eq_of_iso t, Scheme.Pic.map_one] at h
    exact h
  have := integer_invertible A hA m
  have hpow : Scheme.Pic.ofIsInvertible (integerLinePower A hA m) = 1 := by
    exact (integer_class A hA m).trans hAm
  obtain ⟨a⟩ := Scheme.Pic.nonempty_iso_of_ofIsInvertible_eq hpow
  obtain ⟨d, _, hd⟩ := hC.field k (Iso.refl _) (𝟙_ P.Modules) inferInstance
  exact (hd m ⟨a.symm⟩).trans (hd 0 ⟨Iso.refl _⟩).symm

/-- An invertible class trivial on every residue-field fibre comes from the base. -/
theorem exists_base_class_of_fibrewise_trivial (S : Scheme.{u})
    (L : (ProjectiveLine S).Pic)
    (hL : ∀ s : S,
      Scheme.Pic.map (ProjectiveSpace.map (ULift.{u} (Fin 2))
        (S.fromSpecResidueField s)) L = 1) :
    ∃ B : S.Pic, Scheme.Pic.map (ProjectiveLine S ↘ S) B = L := by
  classical
  obtain ⟨P, p, A, hA, e, he, ⟨t⟩, hC⟩ := exists_standard_classification S
  have := hA
  let M := (fromSkeleton (ProjectiveLine S).Modules).obj L.val
  let M' := (pullback e.hom).obj M
  obtain ⟨d, N, ⟨hN, ⟨b⟩⟩, _⟩ := hC.classification M' inferInstance
  have := hN
  let W := locallyConstantLineTwist A hA (d.comap p.base.hom)
  -- Read the degree on each residue fibre through its open degree stratum.
  have hd (s : S) : d s = 0 := by
    let K := Spec (S.residueField s)
    let Q := ProjectiveLine K
    let j := S.fromSpecResidueField s
    let i := ProjectiveSpace.map (ULift.{u} (Fin 2)) j
    let a := i ≫ e.inv
    let q := Q ↘ K
    have hae : a ≫ e.hom = i := by simp [a]
    have hap : a ≫ p = q ≫ j := by
      rw [← he, ← Category.assoc, hae]
      exact ProjectiveSpace.map_over _ j
    obtain ⟨u⟩ := Scheme.Pic.nonempty_iso_unit_of_map_eq i (hL s)
    let u' : (pullback a).obj M' ≅ 𝟙_ Q.Modules :=
      (pullbackComp a e.hom).app M ≪≫ (pullbackCongr hae).app M ≪≫ u
    obtain ⟨n⟩ := IsInvertible.nonempty_iso_unit
      (IsLocalRing.closedPoint (S.residueField s)) ((pullback j).obj N)
    let n' : (pullback a).obj ((tensorPullback p).obj N) ≅ 𝟙_ Q.Modules :=
      (pullback a).mapIso ((tensorComparisonIso p).app N) ≪≫
      (pullbackComp a p).app N ≪≫ (pullbackCongr hap).app N ≪≫
      (pullbackComp q j).symm.app N ≪≫ (pullback q).mapIso n ≪≫ pullbackObjUnitIso q
    have hrange : Set.range a ⊆ p ⁻¹ᵁ lineDegreeOpen d (d s) := by
      rintro _ ⟨x, rfl⟩
      change d (p (a x)) = d s
      have hx := congrArg (fun f : Q ⟶ S ↦ f x) hap
      have hs : p (a x) = s := by
        change p (a x) = j (q x) at hx
        exact hx.trans (Scheme.fromSpecResidueField_apply s (q x))
      rw [hs]
    obtain ⟨r⟩ := hC.twist_restrict d (d s)
    let r' : (pullback a).obj W ≅ (pullback a).obj (integerLinePower A hA (d s)) :=
      restrict_pullback_iso a _ hrange W _ r
    obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso a W ((tensorPullback p).obj N)
    let v : (pullback a).obj (integerLinePower A hA (d s)) ≅ 𝟙_ Q.Modules :=
      r'.symm ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ n'.symm ≪≫ μ.symm ≪≫
        ((pullback a).mapIso b).symm ≪≫ u'
    have := integer_invertible A hA (d s)
    have hv : Scheme.Pic.map a (Scheme.Pic.ofIsInvertible A) ^ d s = 1 := by
      rw [← Scheme.Pic.mapHom_apply a, ← map_zpow, Scheme.Pic.mapHom_apply,
        ← integer_class A hA (d s), pic_map_class]
      exact (Scheme.Pic.ofIsInvertible_eq_of_iso v).trans Scheme.Pic.ofIsInvertible_unit
    let t' : (pullback a).obj A ≅ ProjectiveSpace.twist (ULift.{u} (Fin 2)) K 1 :=
      (pullback a).mapIso t.symm ≪≫ (pullbackComp a e.hom).app _ ≪≫
        (pullbackCongr hae).app _ ≪≫ ProjectiveSpace.pullbackMapTwistIso _ j 1
    rw [pic_map_class, Scheme.Pic.ofIsInvertible_eq_of_iso t'] at hv
    exact field_degree_zero (S.residueField s) (d s) hv
  -- The zero stratum is the entire bundle, so its twist is the tensor unit.
  have htop : p ⁻¹ᵁ lineDegreeOpen d 0 = ⊤ := by
    ext x
    change (d (p x) = 0) ↔ True
    exact ⟨fun _ ↦ trivial, fun _ ↦ hd (p x)⟩
  obtain ⟨r⟩ := hC.twist_restrict d 0
  rw [htop] at r
  let r' : (pullback (⊤ : P.Opens).ι).obj W ≅
      (pullback (⊤ : P.Opens).ι).obj (𝟙_ P.Modules) :=
    (tensorComparisonIso _).symm.app W ≪≫ r ≪≫ (tensorComparisonIso _).app _
  let w : W ≅ 𝟙_ P.Modules := reflect_pullback_iso P.topIso W _ r'
  let v : M' ≅ (pullback p).obj N :=
    b ≪≫ whiskerRightIso w _ ≪≫ λ_ _ ≪≫ (tensorComparisonIso p).app N
  -- Descend the class along the standard-model isomorphism.
  refine ⟨Scheme.Pic.ofIsInvertible N, pic_map_injective e ?_⟩
  rw [← Scheme.Pic.map_comp, he]
  conv_rhs => rw [← Scheme.Pic.ofIsInvertible_fromSkeleton L]
  rw [pic_map_class, pic_map_class]
  exact Scheme.Pic.ofIsInvertible_eq_of_iso v.symm

end AlgebraicGeometry.ProjectiveLine
