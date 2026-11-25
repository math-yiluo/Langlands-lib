/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The free telescope resolution of a localized ring sheaf

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af, displayed resolution
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section AlgebraicTelescope

variable {R : Type u} [CommRing R]

/-- Identity minus the weighted successor on finite sequences. -/
private noncomputable def localizationTelescopeD (f : R) : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.linearCombination R (fun n => Finsupp.single n 1 - Finsupp.single (n + 1) f)

/-- The fraction sum on finite sequences. -/
private noncomputable def localizationTelescopeQ (f : R) : (ℕ →₀ R) →ₗ[R] Localization.Away f :=
  Finsupp.linearCombination R (fun n => IsLocalization.Away.invSelf f ^ n)

@[simp] private lemma localizationTelescopeD_single (f a : R) (n : ℕ) :
    localizationTelescopeD f (Finsupp.single n a) =
      Finsupp.single n a - Finsupp.single (n + 1) (f * a) := by
  simp [localizationTelescopeD, smul_sub, Finsupp.smul_single, mul_comm]

@[simp] private lemma localizationTelescopeQ_single (f a : R) (n : ℕ) :
    localizationTelescopeQ f (Finsupp.single n a) =
      algebraMap R (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n := by
  simp [localizationTelescopeQ, Algebra.smul_def]

private lemma telescopeD_zero (f : R) (x : ℕ →₀ R) :
    localizationTelescopeD f x 0 = x 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single n a => simp [Finsupp.single_apply]

private lemma telescopeD_succ (f : R) (x : ℕ →₀ R) (n : ℕ) :
    localizationTelescopeD f x (n + 1) = x (n + 1) - f * x n := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]; ring
  | single m a =>
    simp only [localizationTelescopeD_single, Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> simp_all

private lemma telescopeD_injective (f : R) : Function.Injective (localizationTelescopeD f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  ext n
  change x n = 0
  induction n with
  | zero => simpa [hx] using (telescopeD_zero f x).symm
  | succ n ih => simpa [hx, ih] using (telescopeD_succ f x n).symm

private lemma telescopeQD (f : R) :
    (localizationTelescopeQ f).comp (localizationTelescopeD f) = 0 := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, localizationTelescopeD_single,
    map_sub, localizationTelescopeQ_single, map_mul, LinearMap.zero_apply]
  rw [pow_succ]
  have h := IsLocalization.Away.mul_invSelf
    (S := Localization.Away f) f
  calc
    _ = algebraMap R (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n *
        (1 - algebraMap R (Localization.Away f) f * IsLocalization.Away.invSelf f) := by ring
    _ = 0 := by rw [h]; ring

private lemma telescope_single_relation (f a : R) (n m : ℕ) (h : n ≤ m) :
    Finsupp.single n a - Finsupp.single m (f ^ (m - n) * a) ∈
      LinearMap.range (localizationTelescopeD f) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have hr := LinearMap.mem_range_self (localizationTelescopeD f)
      (Finsupp.single m (f ^ (m - n) * a))
    rw [localizationTelescopeD_single] at hr
    convert Submodule.add_mem _ ih hr using 1
    rw [Nat.succ_sub h, pow_succ]
    rw [show f ^ (m - n) * f * a = f * (f ^ (m - n) * a) by ring]
    abel

private lemma telescope_normal_form (f : R) (x : ℕ →₀ R) :
    ∃ (m : ℕ) (a : R), x - Finsupp.single m a ∈
      LinearMap.range (localizationTelescopeD f) := by
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | single n a => exact ⟨n, a, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, a, ha⟩ := hx
    obtain ⟨n, b, hb⟩ := hy
    refine ⟨max m n, f ^ (max m n - m) * a + f ^ (max m n - n) * b, ?_⟩
    have hm := telescope_single_relation f a m (max m n) (le_max_left _ _)
    have hn := telescope_single_relation f b n (max m n) (le_max_right _ _)
    convert Submodule.add_mem _ (Submodule.add_mem _ ha hm)
      (Submodule.add_mem _ hb hn) using 1
    rw [Finsupp.single_add]
    abel

/-- The weighted successor presents localization over any commutative ring, including
rings with zero divisors and localization at zero.

Source: Stacks Project, Tag 0997, lemma-hom-from-Af, sectionwise displayed resolution.
(auxiliary; not a blueprint node).

Proof: coordinate induction proves injectivity of D. The fractions telescope, giving QD=0.
Modulo the image of D, move each coordinate to a common later coordinate using
[e_n a]=[e_m f^(m-n)a]. A finite sum is therefore represented by e_m a. If its fraction is
zero, invertibility of f in the localization gives algebraMap(a)=0. The localization
relation supplies k with f^k a=0. Moving to coordinate m+k now kills this representative.
Every fraction is Q(e_n a), which proves surjectivity. No cancellation in R is used. -/
private theorem localization_telescope_exact (f : R) :
    Function.Injective (localizationTelescopeD f) ∧
      Function.Exact (localizationTelescopeD f) (localizationTelescopeQ f) ∧
      Function.Surjective (localizationTelescopeQ f) := by
  refine ⟨telescopeD_injective f, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨m, a, z, hz⟩ := telescope_normal_form f x
      have hq := congrArg (localizationTelescopeQ f) hz
      change (localizationTelescopeQ f).comp (localizationTelescopeD f) z =
        localizationTelescopeQ f (x - Finsupp.single m a) at hq
      rw [telescopeQD, LinearMap.zero_apply, map_sub, hx,
        localizationTelescopeQ_single] at hq
      have ha : algebraMap R (Localization.Away f) a = 0 := by
        have hzero : algebraMap R (Localization.Away f) a *
            IsLocalization.Away.invSelf f ^ m = 0 := by simpa using hq.symm
        calc
          _ = (algebraMap R (Localization.Away f) a *
              IsLocalization.Away.invSelf f ^ m) *
              algebraMap R (Localization.Away f) f ^ m := by
            rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf f),
              IsLocalization.Away.mul_invSelf, one_pow, mul_one]
          _ = 0 := by rw [hzero, zero_mul]
      obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq f
        (ha.trans (map_zero _).symm)
      simp only [mul_zero] at hk
      have hr := telescope_single_relation f a m (m + k) (Nat.le_add_right _ _)
      simp only [Nat.add_sub_cancel_left, hk, Finsupp.single_zero, sub_zero] at hr
      have hxrange := Submodule.add_mem _ (show x - Finsupp.single m a ∈
        LinearMap.range (localizationTelescopeD f) from ⟨z, hz⟩) hr
      rw [sub_add_cancel] at hxrange
      obtain ⟨y, hy⟩ := hxrange
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (telescopeQD f) y
  · intro x
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
    refine ⟨Finsupp.single n a, ?_⟩
    rw [localizationTelescopeQ_single]
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away f) f n).mul_right_cancel
    rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf f),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    exact ha.symm

end AlgebraicTelescope

private theorem slice_section_natural {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U)) {V W : (Over U)ᵒᵖ} (g : V ⟶ W) :
    O.obj.map g.unop.left.op (O.obj.map V.unop.hom.op f) =
      O.obj.map W.unop.hom.op f := by
  rw [← CommRingCat.comp_apply, ← O.obj.map_comp, ← op_comp, Over.w]

private noncomputable def slice_loc_map {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U)) {V W : (Over U)ᵒᵖ} (g : V ⟶ W) :
    Localization.Away (O.obj.map V.unop.hom.op f) →+*
      Localization.Away (O.obj.map W.unop.hom.op f) :=
  IsLocalization.Away.lift (O.obj.map V.unop.hom.op f)
    (g := (algebraMap _ _).comp (O.obj.map g.unop.left.op).hom)
    (by
      change IsUnit (algebraMap _ _
        (O.obj.map g.unop.left.op (O.obj.map V.unop.hom.op f)))
      rw [slice_section_natural]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] private theorem slice_loc_map_algebraMap {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U)) {V W : (Over U)ᵒᵖ} (g : V ⟶ W)
    (a : O.obj.obj (op V.unop.left)) :
    slice_loc_map O U f g (algebraMap _ _ a) =
      algebraMap _ _ (O.obj.map g.unop.left.op a) := by
  simp [slice_loc_map]

private theorem slice_loc_map_smul {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U)) {V W : (Over U)ᵒᵖ} (g : V ⟶ W)
    (a : O.obj.obj (op V.unop.left))
    (x : Localization.Away (O.obj.map V.unop.hom.op f)) :
    slice_loc_map O U f g (a • x) =
      O.obj.map g.unop.left.op a • slice_loc_map O U f g x := by
  simp only [Algebra.smul_def, map_mul, slice_loc_map_algebraMap]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def slice_localization {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    SliceAwayLocalization O U f where
  val := {
    obj := fun V => ModuleCat.of (O.obj.obj (op V.unop.left))
      (Localization.Away (O.obj.map V.unop.hom.op f))
    map := fun {V W} g => ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (O.obj.map g.unop.left.op).hom).obj
        (ModuleCat.of (O.obj.obj (op W.unop.left))
          (Localization.Away (O.obj.map W.unop.hom.op f)))) {
      toFun := slice_loc_map O U f g
      map_add' := map_add _
      map_smul' := slice_loc_map_smul O U f g }
    map_id := fun V => by
      ext x
      change slice_loc_map O U f (𝟙 V) x = x
      suffices slice_loc_map O U f (𝟙 V) = RingHom.id _ from congrArg (fun h => h x) this
      apply IsLocalization.ringHom_ext (Submonoid.powers (O.obj.map V.unop.hom.op f))
      ext a
      simp
    map_comp := fun {V W Z} g h => by
      ext x
      change slice_loc_map O U f (g ≫ h) x =
        slice_loc_map O U f h (slice_loc_map O U f g x)
      suffices slice_loc_map O U f (g ≫ h) =
          (slice_loc_map O U f h).comp (slice_loc_map O U f g) from
        congrArg (fun k => k x) this
      apply IsLocalization.ringHom_ext (Submonoid.powers (O.obj.map V.unop.hom.op f))
      ext a
      simp only [RingHom.comp_apply, slice_loc_map_algebraMap]
      rw [← CommRingCat.comp_apply, ← O.obj.map_comp]
      rfl }
  equiv := fun _ => LinearEquiv.refl _ _
  restriction := by
    intro V W g a n
    change slice_loc_map O U f g
      (algebraMap _ _ a * IsLocalization.Away.invSelf _ ^ n) = _
    rw [map_mul, slice_loc_map_algebraMap, map_pow]
    congr 2
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (O.obj.map W.unop.hom.op f))
      (O.obj.map W.unop.hom.op f)).mul_left_cancel
    rw [IsLocalization.Away.mul_invSelf]
    have h := congrArg (slice_loc_map O U f g)
      (IsLocalization.Away.mul_invSelf
        (S := Localization.Away (O.obj.map V.unop.hom.op f))
        (O.obj.map V.unop.hom.op f))
    simp only [map_mul, slice_loc_map_algebraMap, map_one, slice_section_natural] at h
    exact h

private noncomputable abbrev seqFree {C : Type uC} [Category.{vC} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) : PresheafOfModules.{u} R :=
  PresheafOfModules.freeObj ((Functor.const Cᵒᵖ).obj (ULift.{u} ℕ))

private noncomputable def seqι {C : Type uC} [Category.{vC} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (n : ULift.{u} ℕ) :
    PresheafOfModules.unit R ⟶ seqFree R :=
  (seqFree R).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun _ => ModuleCat.freeMk n) (by
      intro V W g
      simp [seqFree, PresheafOfModules.freeObj]))

private theorem seqι_apply {C : Type uC} [Category.{vC} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (n : ULift.{u} ℕ) (V : Cᵒᵖ) (a : R.obj V) :
    (seqι R n).app V a = Finsupp.single n a := by
  change a • Finsupp.single n (1 : R.obj V) = Finsupp.single n a
  simp [Finsupp.smul_single]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def seqDesc {C : Type uC} [Category.{vC} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R}
    (g : ULift.{u} ℕ → (PresheafOfModules.unit R ⟶ M)) : seqFree R ⟶ M :=
  PresheafOfModules.freeObjDesc {
    app := fun V => ↾fun n => (g n).app V (1 : R.obj V)
    naturality := fun V W h => by
      ext n
      change (g n).app W (1 : R.obj W) = M.map h ((g n).app V (1 : R.obj V))
      simpa only [PresheafOfModules.unit_map_one] using!
        PresheafOfModules.naturality_apply (g n) h (1 : R.obj V) }

set_option backward.isDefEq.respectTransparency false in
private theorem seqι_desc {C : Type uC} [Category.{vC} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R}
    (g : ULift.{u} ℕ → (PresheafOfModules.unit R ⟶ M)) (n : ULift.{u} ℕ) :
    seqι R n ≫ seqDesc g = g n := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change R.obj V at a
  rw [PresheafOfModules.comp_app]
  change (ModuleCat.freeDesc (↾fun n => (g n).app V (1 : R.obj V)))
    ((seqι R n).app V a) = (g n).app V a
  rw [seqι_apply]
  have h : Finsupp.single n a = a • ModuleCat.freeMk n := by
    exact (Finsupp.smul_single_one n a).symm
  rw [h, map_smul, ModuleCat.freeDesc_apply]
  simpa using (((g n).app V).hom.map_smul a (1 : R.obj V)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem seq_hom_ext {C : Type uC} [Category.{vC} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R}
    {g h : seqFree R ⟶ M} (he : ∀ n, seqι R n ≫ g = seqι R n ≫ h) : g = h := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.free_hom_ext
  intro n
  have h := congrArg (fun k : PresheafOfModules.unit R ⟶ M => k.app V (1 : R.obj V)) (he n)
  simpa only [PresheafOfModules.comp_app, ModuleCat.comp_apply, seqι_apply,
    ModuleCat.freeMk] using! h

private noncomputable def seqIsColimit {C : Type uC} [Category.{vC} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) : IsColimit (Cofan.mk (seqFree R) (seqι R)) :=
  Cofan.IsColimit.mk _ (fun s => seqDesc (fun n => s.inj n))
    (fun _s n => seqι_desc _ n)
    (fun _s _m hm => seq_hom_ext (fun n => (hm n).trans (seqι_desc _ n).symm))

private noncomputable abbrev sliceRing {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) : Sheaf (J.over U) RingCat.{u} :=
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U

private noncomputable def sliceMul {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    PresheafOfModules.unit (sliceRing O U).obj ⟶
      PresheafOfModules.unit (sliceRing O U).obj :=
  (PresheafOfModules.unit (sliceRing O U).obj).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun V => O.obj.map V.unop.hom.op f)
      (fun {_ _} g => slice_section_natural O U f g))

private theorem sliceMul_apply {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (a : O.obj.obj (op V.unop.left)) :
    (sliceMul O U f).app V a = O.obj.map V.unop.hom.op f * a := by
  change a * O.obj.map V.unop.hom.op f = O.obj.map V.unop.hom.op f * a
  exact mul_comm _ _

private noncomputable def sliceD {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    seqFree (sliceRing O U).obj ⟶ seqFree (sliceRing O U).obj :=
  seqDesc (fun n => seqι _ n - sliceMul O U f ≫ seqι _ (ULift.up (n.down + 1)))

set_option backward.isDefEq.respectTransparency false in
private theorem sliceD_single {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (n : ULift.{u} ℕ) (a : O.obj.obj (op V.unop.left)) :
    (sliceD O U f).app V (Finsupp.single n a) =
      Finsupp.single n a - Finsupp.single (ULift.up (n.down + 1))
        (O.obj.map V.unop.hom.op f * a) := by
  have h := congrArg (fun g => g.app V a)
    (seqι_desc (fun n => seqι (sliceRing O U).obj n -
      sliceMul O U f ≫ seqι _ (ULift.up (n.down + 1))) n)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply, seqι_apply,
    PresheafOfModules.sub_app] at h
  change (sliceD O U f).app V (Finsupp.single n a) =
    (seqι (sliceRing O U).obj n).app V a -
      (seqι (sliceRing O U).obj (ULift.up (n.down + 1))).app V
      ((sliceMul O U f).app V a) at h
  simpa only [seqι_apply, sliceMul_apply] using! h

private noncomputable def sliceFraction {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) (n : ℕ) :
    PresheafOfModules.unit (sliceRing O U).obj ⟶ (slice_localization O U f).val :=
  (slice_localization O U f).val.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V => (slice_localization O U f).equiv V |>.symm
        (IsLocalization.Away.invSelf (O.obj.map V.unop.hom.op f) ^ n)) (by
      intro V W g
      have h := (slice_localization O U f).restriction g (1 : O.obj.obj (op V.unop.left)) n
      apply ((slice_localization O U f).equiv W).injective
      simpa only [map_one, one_mul, LinearEquiv.apply_symm_apply] using h))

private noncomputable def sliceQ {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    seqFree (sliceRing O U).obj ⟶ (slice_localization O U f).val :=
  seqDesc (fun n => sliceFraction O U f n.down)

set_option backward.isDefEq.respectTransparency false in
private theorem sliceQ_single {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (n : ULift.{u} ℕ) (a : O.obj.obj (op V.unop.left)) :
    (sliceQ O U f).app V (Finsupp.single n a) =
      (algebraMap (O.obj.obj (op V.unop.left))
        (Localization.Away (O.obj.map V.unop.hom.op f))) a *
          IsLocalization.Away.invSelf (O.obj.map V.unop.hom.op f) ^ n.down := by
  have h := congrArg (fun g => g.app V a)
    (seqι_desc (fun n => sliceFraction O U f n.down) n)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply, seqι_apply] at h
  change (sliceQ O U f).app V (Finsupp.single n a) =
    a • (IsLocalization.Away.invSelf
      (S := Localization.Away (O.obj.map V.unop.hom.op f))
      (O.obj.map V.unop.hom.op f) ^ n.down) at h
  simpa only [Algebra.smul_def] using! h

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def seqEquiv (V : (Over U)ᵒᵖ) :
    (seqFree (sliceRing O U).obj).obj V ≃+ (ℕ →₀ O.obj.obj (op V.unop.left)) :=
  Finsupp.domCongr Equiv.ulift

private theorem seqEquiv_single (V : (Over U)ᵒᵖ) (n : ULift.{u} ℕ)
    (a : O.obj.obj (op V.unop.left)) :
    seqEquiv O U V (Finsupp.single n a) = Finsupp.single n.down a :=
  Finsupp.equivMapDomain_single Equiv.ulift n a

set_option backward.isDefEq.respectTransparency false in
private theorem seqEquiv_D (V : (Over U)ᵒᵖ)
    (x : (seqFree (sliceRing O U).obj).obj V) :
    seqEquiv O U V ((sliceD O U f).app V x) =
      localizationTelescopeD (O.obj.map V.unop.hom.op f) (seqEquiv O U V x) := by
  change ULift.{u} ℕ →₀ O.obj.obj (op V.unop.left) at x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single n a =>
    rw [sliceD_single]
    rw [map_sub, seqEquiv_single, seqEquiv_single, localizationTelescopeD_single]

set_option backward.isDefEq.respectTransparency false in
private theorem seqEquiv_Q (V : (Over U)ᵒᵖ)
    (x : (seqFree (sliceRing O U).obj).obj V) :
    (sliceQ O U f).app V x =
      localizationTelescopeQ (O.obj.map V.unop.hom.op f) (seqEquiv O U V x) := by
  change ULift.{u} ℕ →₀ O.obj.obj (op V.unop.left) at x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single n a =>
    rw [sliceQ_single]
    rw [seqEquiv_single, localizationTelescopeQ_single]

private theorem slice_section_exact (V : (Over U)ᵒᵖ) :
    Function.Injective ((sliceD O U f).app V) ∧
      Function.Exact ((sliceD O U f).app V) ((sliceQ O U f).app V) ∧
      Function.Surjective ((sliceQ O U f).app V) := by
  obtain ⟨hi, he, hs⟩ := localization_telescope_exact (O.obj.map V.unop.hom.op f)
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    apply (seqEquiv O U V).injective
    apply hi
    rw [← seqEquiv_D, ← seqEquiv_D, h]
  · intro x
    rw [seqEquiv_Q, he]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(seqEquiv O U V).symm y, ?_⟩
      apply (seqEquiv O U V).injective
      rw [seqEquiv_D, AddEquiv.apply_symm_apply, hy]
    · rintro ⟨y, rfl⟩
      exact ⟨seqEquiv O U V y, (seqEquiv_D O U f V y).symm⟩
  · intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨(seqEquiv O U V).symm y, by
      rw [seqEquiv_Q, AddEquiv.apply_symm_apply, hy]⟩

private theorem sliceDQ : sliceD O U f ≫ sliceQ O U f = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (slice_section_exact O U f V).2.1.apply_apply_eq_zero x

private noncomputable def sliceComplex :
    ShortComplex (PresheafOfModules.{u} (sliceRing O U).obj) :=
  ShortComplex.mk (sliceD O U f) (sliceQ O U f) (sliceDQ O U f)

private theorem slice_section_shortExact (V : (Over U)ᵒᵖ) :
    ((sliceComplex O U f).map (PresheafOfModules.evaluation _ V)).ShortExact := by
  obtain ⟨hi, he, hs⟩ := slice_section_exact O U f V
  exact ModuleCat.shortComplex_shortExact _ he hi hs

private theorem slice_shortExact : (sliceComplex O U f).ShortExact := by
  have hk : IsLimit (KernelFork.ofι (sliceD O U f) (sliceDQ O U f)) := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    refine (isLimitMapConeForkEquiv' (PresheafOfModules.evaluation _ V) _).symm ?_
    have he := slice_section_shortExact O U f V
    have := he.mono_f
    exact he.exact.fIsKernel
  have hm : Mono (sliceComplex O U f).f := mono_of_isLimit_fork hk
  refine { exact := (sliceComplex O U f).exact_of_f_is_kernel hk, epi_g := ?_ }
  constructor
  intro M g h hgh
  apply PresheafOfModules.hom_ext
  intro V
  have he := slice_section_shortExact O U f V
  have : Epi ((sliceQ O U f).app V) := he.epi_g
  apply (cancel_epi ((sliceQ O U f).app V)).mp
  exact congrArg (fun k => k.app V) hgh

end

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private noncomputable abbrev sh : PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R :=
  PresheafOfModules.sheafification (𝟙 R.obj)

private noncomputable abbrev adj :=
  PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)

private noncomputable def shUnitIso : (sh R).obj (PresheafOfModules.unit R.obj) ≅
    SheafOfModules.unit R :=
  asIso ((adj R).counit.app (SheafOfModules.unit R))

private noncomputable def freeIso : SheafOfModules.free (R := R) (ULift.{u} ℕ) ≅
    (sh R).obj (seqFree R.obj) :=
  (SheafOfModules.isColimitFreeCofan _).coconePointsIsoOfNatIso
    (isColimitOfPreserves (sh R) (seqIsColimit R.obj))
    (Discrete.natIso (fun _ => (shUnitIso R).symm))

private theorem freeIso_ι (n : ULift.{u} ℕ) :
    SheafOfModules.ιFree n ≫ (freeIso R).hom =
      (shUnitIso R).inv ≫ (sh R).map (seqι R.obj n) := by
  exact IsColimit.ι_map (SheafOfModules.isColimitFreeCofan _)
    ((sh R).mapCocone (Cofan.mk _ (seqι R.obj)))
    (Discrete.natTrans (fun _ => (shUnitIso R).inv)) (Discrete.mk n)

set_option backward.isDefEq.respectTransparency false in
private theorem unit_counit (V : Cᵒᵖ) (a : R.obj.obj V) :
    ((shUnitIso R).inv.val.app V a) =
      ((adj R).unit.app (PresheafOfModules.unit R.obj)).app V a := by
  have h := (adj R).right_triangle_components (SheafOfModules.unit R)
  have hm := congrArg (fun g => g.app V a) h
  change ((shUnitIso R).hom.val.app V)
    (((adj R).unit.app (PresheafOfModules.unit R.obj)).app V a) = a at hm
  apply_fun ((shUnitIso R).inv.val.app V) at hm
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.hom_inv_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using! hm.symm

set_option backward.isDefEq.respectTransparency false in
private theorem freeIso_ι_apply (n : ULift.{u} ℕ) (V : Cᵒᵖ) (a : R.obj.obj V) :
    (freeIso R).hom.val.app V ((SheafOfModules.ιFree n).val.app V a) =
      ((adj R).unit.app (seqFree R.obj)).app V (Finsupp.single n a) := by
  have h := congrArg (fun g : SheafOfModules.unit R ⟶ _ => g.val.app V a) (freeIso_ι R n)
  change (freeIso R).hom.val.app V ((SheafOfModules.ιFree n).val.app V a) =
    ((sh R).map (seqι R.obj n)).val.app V ((shUnitIso R).inv.val.app V a) at h
  rw [unit_counit] at h
  have hn := (adj R).unit.naturality (seqι R.obj n)
  have hna := congrArg (fun g => g.app V a) hn
  change ((adj R).unit.app (seqFree R.obj)).app V ((seqι R.obj n).app V a) =
    ((sh R).map (seqι R.obj n)).val.app V
      (((adj R).unit.app (PresheafOfModules.unit R.obj)).app V a) at hna
  rw [seqι_apply] at hna
  exact h.trans hna.symm

set_option backward.isDefEq.respectTransparency false in
private theorem sh_map_unit {P Q : PresheafOfModules.{u} R.obj} (g : P ⟶ Q)
    (V : Cᵒᵖ) (x : P.obj V) :
    ((sh R).map g).val.app V (((adj R).unit.app P).app V x) =
      ((adj R).unit.app Q).app V (g.app V x) := by
  exact (congrArg (fun k => k.app V x) ((adj R).unit.naturality g)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem freeIso_inv_unit (n : ULift.{u} ℕ) (V : Cᵒᵖ) (a : R.obj.obj V) :
    (freeIso R).inv.val.app V
        (((adj R).unit.app (seqFree R.obj)).app V (Finsupp.single n a)) =
      (SheafOfModules.ιFree n).val.app V a := by
  rw [← freeIso_ι_apply]
  change (((freeIso R).hom ≫ (freeIso R).inv).val.app V)
    ((SheafOfModules.ιFree n).val.app V a) = _
  rw [Iso.hom_inv_id]
  rfl

end

/-- The localization on a slice has the stated two-term free resolution. The formulas on
coordinate inclusions determine the maps uniquely and imply the finite-support formulas
on local representatives. Rings are commutative, as in the Stacks convention.

Source: Stacks Project, Tag 0997, lemma-hom-from-Af, displayed resolution.
(auxiliary; not a blueprint node).

Proof:
1. On the slice (def-pur-localized-ringed-site), form the presheaves P of finite-support
sequences and L of fractions, with the restriction maps on coefficients. Define D by
identity minus the f-weighted forward shift and Q by summing x_n/f^n.
2. Coordinate induction makes D injective. Telescoping gives QD = 0, and a single
coordinate gives every fraction, so Q is surjective sectionwise.
3. Modulo im D, move each coordinate a e_n to f^(m-n)a e_m for m ≥ n.
Induction on finite sequences then writes x - a e_m in im D. If Qx = 0,
invertibility of f in the localization gives algebraMap(a) = 0.
4. The localization relation supplies k with f^k a = 0, without cancelling f in R.
Move a e_m to coordinate m+k: it is zero there. Hence x lies in im D.
This includes k = 0, the zero sequence, and localization at zero.
5. Apply lem-weil-pbc-ringed-site-module-sheafification-exact to this exact sequence;
its Mathlib instances are imported through Presheaf.Sheafification.
6. The adjunction def-weil-presheaf-modules-sheafification identifies P's sheafification
with the countable coproduct of unit modules. The coordinate formulas descend to the
sheafification and give precisely d and q. -/
theorem sliceAwayLocalization_free_resolution {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U))
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ∃ L : SliceAwayLocalization O U f,
    ∃ d : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            O).over U))
            (ULift.{u} ℕ)),
    ∃ q : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (PresheafOfModules.sheafification (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            O).over U).obj)).obj L.val,
      (∃ h : d ≫ q = 0, (ShortComplex.mk
        (C := ringedSiteModules
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).over U))
        d q h).ShortExact) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        d.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up n)).val.app V a -
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up (n + 1))).val.app V
            (O.obj.map V.unop.hom.op f * a)) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        q.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (((sheafCompose J (forget₂ CommRingCat
              RingCat)).obj O).over U).obj)).unit.app
            L.val).app V ((L.equiv V).symm
              (algebraMap _ _ a * IsLocalization.Away.invSelf
                (O.obj.map V.unop.hom.op f) ^ n))) := by
  let R := sliceRing O U
  let F := sh R
  let e := freeIso R
  let L := slice_localization O U f
  let d := e.hom ≫ F.map (sliceD O U f) ≫ e.inv
  let q := e.hom ≫ F.map (sliceQ O U f)
  have hdq : d ≫ q = 0 := by
    dsimp [d, q]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp]
    rw [sliceDQ O U f, F.map_zero, comp_zero]
  refine ⟨L, d, q, ⟨hdq, ?_⟩, ?_, ?_⟩
  · have hs := (slice_shortExact O U f).map_of_exact F
    let ei : (sliceComplex O U f).map F ≅ ShortComplex.mk d q hdq :=
      ShortComplex.isoMk e.symm e.symm (Iso.refl _) (by
        dsimp [d]
        simp only [Iso.inv_hom_id_assoc]
        rfl) (by
        dsimp [q]
        simp only [Iso.inv_hom_id_assoc, Category.comp_id]
        rfl)
    exact ShortComplex.shortExact_of_iso ei hs
  · intro V n a
    change e.inv.val.app V
      ((F.map (sliceD O U f)).val.app V
        (e.hom.val.app V ((SheafOfModules.ιFree (ULift.up n)).val.app V a))) = _
    rw [freeIso_ι_apply, sh_map_unit, sliceD_single, map_sub, map_sub,
      freeIso_inv_unit, freeIso_inv_unit]
  · intro V n a
    change (F.map (sliceQ O U f)).val.app V
      (e.hom.val.app V ((SheafOfModules.ιFree (ULift.up n)).val.app V a)) = _
    rw [freeIso_ι_apply, sh_map_unit, sliceQ_single]
    rfl

end CategoryTheory
