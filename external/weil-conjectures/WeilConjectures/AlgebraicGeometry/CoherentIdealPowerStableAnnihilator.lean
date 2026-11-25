/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.AnnihilatorSubsheaf
import WeilConjectures.AlgebraicGeometry.AnnihilatorAffineCriterion
import WeilConjectures.AlgebraicGeometry.IdealDataRecursivePowerComparison
import WeilConjectures.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Stabilization of ideal-power annihilators

Source: Stacks Project, Tag 01YB, second paragraph, using Tags 01PO and 01Y8.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem annihilator_qc_noetherian {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (ι : G ⟶ F) [Mono ι]
    (himage : ∀ (U : X.affineOpens) (s : Γ(F, U.1)),
      s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0) :
    G.IsQuasicoherent := by
  classical
  have hinj (U : X.Opens) : Function.Injective (ι.app U) :=
    (ModuleCat.mono_iff_injective _).mp
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map_mono ι)
  have hnat (V W : X.Opens) (h : V ≤ W) (s : Γ(G, W)) :
      ι.app V (G.presheaf.map (homOfLE h).op s) =
        F.presheaf.map (homOfLE h).op (ι.app W s) := by
    exact ConcreteCategory.congr_hom (ι.mapPresheaf.naturality (homOfLE h).op) s
  apply isQuasicoherent_of_forall_isAffineOpen G
  · intro W hW f s
    obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen F hW f
      (ι.app (X.basicOpen f) s)
    have := IsLocallyNoetherian.component_noetherian (⟨W, hW⟩ : X.affineOpens)
    obtain ⟨g, hg⟩ := IsNoetherian.noetherian (J.ideal ⟨W, hW⟩)
    have hzero (j : g) : F.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (j.val • t) = 0 := by
      rw [map_smul, ht, smul_comm]
      have hj : j.val ∈ J.ideal ⟨W, hW⟩ := by
        rw [← hg]
        exact Ideal.subset_span j.property
      have ha : X.presheaf.map (homOfLE (X.basicOpen_le f)).op j.val ∈
          J.ideal ⟨X.basicOpen f, hW.basicOpen f⟩ :=
        J.ideal_le_comap_ideal (X.basicOpen_le f) hj
      rw [(himage ⟨X.basicOpen f, hW.basicOpen f⟩ _).mp ⟨s, rfl⟩ _ ha, smul_zero]
    choose d hd using fun j : g ↦ exists_pow_smul_eq_zero_of_isAffineOpen F hW f
      (j.val • t) (hzero j)
    let D := g.attach.sup d
    have hgen (j : g) : j.val • (f ^ D • t) = 0 := by
      have hj : d j ≤ D := Finset.le_sup (Finset.mem_attach g j)
      rw [smul_comm, ← Nat.sub_add_cancel hj, pow_add, mul_smul, hd j, smul_zero]
    have hann : ∀ a ∈ J.ideal ⟨W, hW⟩, a • (f ^ D • t) = 0 := by
      let q := LinearMap.toSpanSingleton Γ(X, W) Γ(F, W) (f ^ D • t)
      have hle : J.ideal ⟨W, hW⟩ ≤ q.ker := by
        rw [← hg]
        apply Submodule.span_le.mpr
        intro a ha
        exact hgen ⟨a, ha⟩
      exact fun a ha ↦ hle ha
    obtain ⟨v, hv⟩ := (himage ⟨W, hW⟩ (f ^ D • t)).mpr hann
    refine ⟨D + n, v, hinj _ ?_⟩
    rw [hnat, hv, map_smul, ht, Hom.app_smul, map_pow, pow_add, mul_smul]
  · intro W hW f t ht
    have hz : F.presheaf.map (homOfLE (X.basicOpen_le f)).op (ι.app W t) = 0 := by
      rw [← hnat, ht, map_zero]
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F hW f (ι.app W t) hz
    exact ⟨n, hinj W (by rw [Hom.app_smul, hn, map_zero])⟩

private theorem hom_zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0) :
    φ = 0 := by
  apply hom_ext
  intro W
  ext s
  change φ.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    have hn := congrArg (fun f ↦ f s)
      (φ.val.naturality (homOfLE i.2).op)
    change φ.app i.1.1 (M.presheaf.map (homOfLE i.2).op s) =
      N.presheaf.map (homOfLE i.2).op (φ.app W s) at hn
    rw [← hn, h, map_zero]

private theorem subobject_le_of_affine_range {X : Scheme.{u}} {M N P : X.Modules}
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ Limits.cokernel.π j = 0 := by
    apply hom_zero_of_affine
    intro V s
    obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
    change (Limits.cokernel.π j).app V.1 (i.app V.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app V.1 t) (Limits.cokernel.condition j)
  let k : M ⟶ Abelian.image j := Limits.kernel.lift (Limits.cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := Limits.kernel.lift_ι _ _ hz

open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
    Set.range ((idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  have := (quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) =
        (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (tmulSection s t)) = _
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (Opposite.op U.1)).hom =
      I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
  have hi : Set.range ((idealModuleProductι i M).app U.1) =
      Set.range ((Abelian.image.ι a).app U.1) := by
    let e := Abelian.imageIsoImage a
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.inv.app U.1 t, ?_⟩
      have h : e.inv ≫ Abelian.image.ι a = image.ι a := by
        calc
          _ = e.inv ≫ e.hom ≫ image.ι a :=
            congrArg (fun f ↦ e.inv ≫ f)
              (Abelian.imageIsoImage_hom_comp_image_ι a).symm
          _ = _ := by simp
      exact congrArg (fun f ↦ f.app U.1 t) h
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.app U.1 t, ?_⟩
      exact congrArg (fun f ↦ f.app U.1 t)
        (Abelian.imageIsoImage_hom_comp_image_ι a)
  rw [hi, hb.1]
  exact congrArg (fun P : Submodule Γ(X, U.1) Γ(M, U.1) ↦ (P : Set Γ(M, U.1))) ha


local instance localInst_CoherentIdealPowerStableAnnihilator_1 {X : Scheme.{u}} (H : X.Modules)
    {V W : X.Opens} (h : V ≤ W) :
    SMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (H.val.obj (op V))) :=
  inferInstanceAs (SMul (X.sheaf.obj.obj (op V)) (H.val.obj (op V)))

set_option backward.isDefEq.respectTransparency false in
/-- A coherent module has a quasi-coherent submodule containing every local
ideal-power annihilator and killed by one fixed ideal power.

Source: Stacks Project, Tag 01YB, second paragraph; Tags 01PO and 01Y8.
(blueprint: lem-pc-coherent-ideal-power-stable-annihilator)

Proof: Construct the subsheaves H_n of H whose sections on W are killed by every
section of I^n on every subopen of W. Addition, scalar multiplication and restriction
preserve this condition, and separatedness of H proves gluing. Powers of the ideal
are finite type on the Noetherian scheme, so the affine annihilator localization
criterion (01PO) proves H_n quasi-coherent. Since I^(n+1) is contained in I^n,
these subobjects form an increasing chain. Noetherian ACC (01Y8) supplies r with
H_n contained in H_r for every n, using monotonicity for n < r and stabilization
for n >= r. Take T = H_r with its actual subsheaf inclusion a. Its inclusion is
mono and T is quasi-coherent. By the defining condition every local section of
I^r kills every section of T: apply the condition to a(t) and use injectivity of a.
On an affine open, the multiplication image is generated by these scalar products,
so I^r T is zero there. Sheaf separatedness on an affine cover makes the product
inclusion zero globally. The range condition follows from H_n contained in T.
If r = 0 the annihilator of the unit ideal is zero. The zero ideal stabilizes
at most at its first power; the unit ideal and zero module give T = 0. The empty
scheme is covered by the empty affine family, so the same reasoning applies. -/
theorem exists_coherent_idealPower_stable_annihilator
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (H : X.Modules) [H.IsQuasicoherent]
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) :
    ∃ (r : ℕ) (T : X.Modules) (a : T ⟶ H),
      Mono a ∧ T.IsQuasicoherent ∧
      idealModuleProductι (idealSheafPower I.toModulesι r).2 T = 0 ∧
      ∀ (n : ℕ) (W : X.Opens) (s : H.val.obj (op W)),
        (∀ (V : X.Opens) (h : V ≤ W)
          (b : (idealSheafPower I.toModulesι n).1.val.obj (op V)),
          ((idealSheafPower I.toModulesι n).2.val.app (op V) b : Γ(X, V)) •
            H.val.map (homOfLE h).op s = 0) →
          s ∈ Set.range (a.app W) := by
  classical
  choose A a hm hl using fun n : ℕ ↦ exists_annihilator_subsheaf X (I ^ n) H
  have (n : ℕ) : Mono (a n) := hm n
  have haff (n : ℕ) (B : X.affineOpens) (s : Γ(H, B.1)) :
      s ∈ Set.range ((a n).app B.1) ↔ ∀ b ∈ (I ^ n).ideal B, b • s = 0 :=
    (hl n B.1 s).trans (annihilator_affine_criterion X (I ^ n) H B s)
  have hqc (n : ℕ) : (A n).IsQuasicoherent :=
    annihilator_qc_noetherian (I ^ n) H (A n) (a n) (haff n)
  let G : ℕ → Subobject H := fun n ↦ Subobject.mk (a n)
  have hG : Monotone G := by
    intro n m hnm
    apply subobject_le_of_affine_range (a n) (a m)
    intro B s hs
    apply (haff m B s).mpr
    intro b hb
    apply (haff n B s).mp hs b
    have hp : I.ideal B ^ m ≤ I.ideal B ^ n :=
      pow_le_pow_right_of_le_one' (by rw [Ideal.one_eq_top]; exact le_top) hnm
    exact hp hb
  have hGqc (n : ℕ) : (G n : X.Modules).IsQuasicoherent := by
    have := hqc n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (a n)).symm inferInstance
  obtain ⟨r, hr⟩ := (noetherian_quasicoherent_submodules X H hH).1 G hG hGqc
  have hle (n : ℕ) : G n ≤ G r := by
    by_cases hn : n ≤ r
    · exact hG hn
    · exact (hr n (by omega)).le
  have hrecRange (n : ℕ) (W : X.Opens) :
      Set.range ((I ^ n).toModulesι.app W) =
        Set.range ((idealSheafPower I.toModulesι n).2.app W) := by
    obtain ⟨_, e, he⟩ := idealData_recursive_power_comparison I n
    ext s
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨e.hom.app W b, ?_⟩
      exact (congrArg (fun f ↦ f.app W b) he).trans hb
    · rintro ⟨b, hb⟩
      refine ⟨e.inv.app W b, ?_⟩
      have hh : e.inv ≫ (I ^ n).toModulesι = (idealSheafPower I.toModulesι n).2 := by
        rw [← he, Iso.inv_hom_id_assoc]
      exact (congrArg (fun f ↦ f.app W b) hh).trans hb
  have hrecMem (n : ℕ) (W : X.Opens) (s : Γ(H, W)) :
      s ∈ Set.range ((a n).app W) ↔
        ∀ (V : X.Opens) (h : V ≤ W)
          (b : Γ((idealSheafPower I.toModulesι n).1, V)),
          (show Γ(X, V) from (idealSheafPower I.toModulesι n).2.app V b) •
            H.presheaf.map (homOfLE h).op s = 0 := by
    rw [hl]
    constructor
    · intro hs V h b
      apply hs V h _
      change _ ∈ ((I ^ n).idealOfOpens V : Set Γ(X, V))
      rw [← (I ^ n).range_toModulesι_app_eq_idealOfOpens, hrecRange]
      exact ⟨b, rfl⟩
    · intro hs V h b hb
      change b ∈ ((I ^ n).idealOfOpens V : Set Γ(X, V)) at hb
      rw [← (I ^ n).range_toModulesι_app_eq_idealOfOpens, hrecRange] at hb
      obtain ⟨b, rfl⟩ := hb
      exact hs V h b
  refine ⟨r, A r, a r, hm r, hqc r, ?_, ?_⟩
  · have : (A r).IsQuasicoherent := hqc r
    have hpqc : (idealSheafPower I.toModulesι r).1.IsQuasicoherent := by
      obtain ⟨hq, e, _⟩ := idealData_recursive_power_comparison I r
      have := hq
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
    let p := (idealSheafPower I.toModulesι r).2
    let q := idealModuleProductι p (A r)
    have hkill (W : X.Opens) (b : Γ((idealSheafPower I.toModulesι r).1, W))
        (y : Γ(A r, W)) : (show Γ(X, W) from p.app W b) • y = 0 := by
      have hi : Function.Injective ((a r).app W) :=
        (ModuleCat.mono_iff_injective _).mp
          ((SheafOfModules.evaluation X.ringCatSheaf (op W)).map_mono (a r))
      apply hi
      rw [Hom.app_smul, map_zero]
      have hh := (hrecMem r W ((a r).app W y)).mp ⟨y, rfl⟩ W le_rfl b
      simpa using hh
    have haffZero (B : X.affineOpens) (z : Γ(idealModuleProduct p (A r), B.1)) :
        q.app B.1 z = 0 := by
      have hz := (multiplication_range p (A r) B).subset ⟨z, rfl⟩
      change q.app B.1 z ∈
        (LinearMap.range (p.val.app (op B.1)).hom : Ideal Γ(X, B.1)) •
          (⊤ : Submodule Γ(X, B.1) Γ(A r, B.1)) at hz
      exact Submodule.smul_induction_on hz
        (fun b hb y _ ↦ by obtain ⟨b, rfl⟩ := hb; exact hkill B.1 b y)
        (fun x y hx hy ↦ by rw [hx, hy, add_zero])
    apply hom_zero_of_affine
    exact haffZero
  · intro n W s hs
    have hn := (hrecMem n W s).mpr hs
    obtain ⟨y, hy⟩ := hn
    let t := Subobject.ofMkLEMk (a n) (a r) (hle n)
    refine ⟨t.app W y, ?_⟩
    exact (congrArg (fun f ↦ f.app W y)
      (Subobject.ofMkLEMk_comp (hle n))).trans hy


end AlgebraicGeometry.Scheme.Modules
