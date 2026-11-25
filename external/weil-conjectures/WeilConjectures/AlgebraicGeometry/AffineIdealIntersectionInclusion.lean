/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Affine comparison of ideal intersection inclusions

Source: Stacks Project, Tags 01YA, 01I8 and 01IC.
(blueprint: lem-pc-affine-ideal-intersection-inclusion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem lift_basic_open {X : Scheme.{u}} (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W O : X.Opens}
    (hW : IsAffineOpen W) (g : Γ(X, W)) (hO : X.basicOpen g = O) (hOW : O ≤ W)
    (s : Γ(ℱ, O)) :
    ∃ (N : ℕ) (t : Γ(ℱ, W)), ℱ.presheaf.map (homOfLE hOW).op t =
      X.presheaf.map (homOfLE hOW).op g ^ N • s := by
  subst hO
  exact Modules.exists_map_eq_pow_smul_of_isAffineOpen ℱ hW g s

/-- A variant of `exists_pow_smul_eq_zero_of_isAffineOpen` for an open `O` equal to `D(g)`. -/
private theorem zero_basic_open {X : Scheme.{u}} (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W O : X.Opens}
    (hW : IsAffineOpen W) (g : Γ(X, W)) (hO : X.basicOpen g = O) (hOW : O ≤ W)
    (t : Γ(ℱ, W)) (ht : ℱ.presheaf.map (homOfLE hOW).op t = 0) :
    ∃ N : ℕ, g ^ N • t = 0 := by
  subst hO
  exact Modules.exists_pow_smul_eq_zero_of_isAffineOpen ℱ hW g t ht

private theorem affine_pushforward_qc {X T : Scheme.{u}} (f : X ⟶ T) [IsAffineHom f] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((Modules.pushforward f).obj ℱ).IsQuasicoherent := by
  refine Modules.isQuasicoherent_of_forall_isAffineOpen _
    (fun W hW g s ↦ ?_) (fun W hW g t ht ↦ ?_)
  · obtain ⟨n, t, ht⟩ := lift_basic_open ℱ (hW.preimage f) (f.app W g)
      (f.preimage_basicOpen g).symm (f.preimage_mono (T.basicOpen_le g)) s
    refine ⟨n, t, ht.trans ?_⟩
    have h : f.app (T.basicOpen g) (T.presheaf.map (homOfLE (T.basicOpen_le g)).op g) =
        X.presheaf.map (homOfLE (f.preimage_mono (T.basicOpen_le g))).op (f.app W g) := by
      rw [← ConcreteCategory.comp_apply, f.naturality]
      rfl
    rw [← h, ← map_pow]
    rfl
  · obtain ⟨n, hn⟩ := zero_basic_open ℱ (hW.preimage f) (f.app W g)
      (f.preimage_basicOpen g).symm (f.preimage_mono (T.basicOpen_le g)) t ht
    rw [← map_pow] at hn
    exact ⟨n, hn⟩


private theorem ideal_qc {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    affine_pushforward_qc J.subschemeι _
  exact Modules.isQuasicoherent_kernel J.toPushforwardSubscheme

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem product_qc {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [K.IsQuasicoherent] [M.IsQuasicoherent] :
    (idealModuleProduct i M).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Modules.quasiCoherent_tensor_product_affine_sections K M).1
  let a := i ▷ M ≫ (λ_ M).hom
  have hi := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) hi

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
  have := (Modules.quasiCoherent_tensor_product_affine_sections K M).1
  have ht := (Modules.quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (Opposite.op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) =
        (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [Modules.tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (Modules.tmulSection s t)) = _
    rw [Modules.whiskerRight_app_tmulSection, Modules.leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (Opposite.op U.1)).hom =
      I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨Modules.tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
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

set_option backward.isDefEq.respectTransparency false in
private theorem power_qc {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
  have := ideal_qc I
  induction n using Nat.twoStepInduction with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | one => assumption
  | more n _ ih => exact product_qc I.toModulesι _

set_option backward.isDefEq.respectTransparency false in
private theorem power_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    (LinearMap.range ((idealSheafPower I.toModulesι n).2.val.app (Opposite.op U.1)).hom :
      Ideal Γ(X, U.1)) = I.ideal U ^ n := by
  have := ideal_qc I
  have hI : (LinearMap.range (I.toModulesι.val.app (.op U.1)).hom :
      Ideal Γ(X, U.1)) = I.ideal U := SetLike.coe_injective (I.range_toModulesι_app U)
  induction n using Nat.twoStepInduction with
  | zero =>
    apply SetLike.coe_injective
    ext s
    change (∃ y : Γ(X, U.1), y = s) ↔ s ∈ (1 : Ideal Γ(X, U.1))
    simp
  | one => simpa only [idealSheafPower, pow_one] using hI
  | more n _ ih =>
    have := power_qc I (n + 1)
    change LinearMap.range
      (((idealSheafPower I.toModulesι (n + 1)).2.val.app (.op U.1)).hom.comp
        ((idealModuleProductι I.toModulesι
          (idealSheafPower I.toModulesι (n + 1)).1).val.app (.op U.1)).hom) = _
    have hr : LinearMap.range ((idealModuleProductι I.toModulesι
        (idealSheafPower I.toModulesι (n + 1)).1).val.app (.op U.1)).hom =
        I.ideal U • (⊤ : Submodule Γ(X, U.1)
          Γ((idealSheafPower I.toModulesι (n + 1)).1, U.1)) := by
      apply SetLike.coe_injective
      change Set.range ((idealModuleProductι I.toModulesι
        (idealSheafPower I.toModulesι (n + 1)).1).app U.1) =
        {s | s ∈ I.ideal U • (⊤ : Submodule Γ(X, U.1)
          Γ((idealSheafPower I.toModulesι (n + 1)).1, U.1))}
      simpa only [hI] using
        multiplication_range I.toModulesι (idealSheafPower I.toModulesι (n + 1)).1 U
    rw [LinearMap.range_comp, hr, Submodule.map_smul'', Submodule.map_top, ih,
      Ideal.smul_eq_mul]
    exact (pow_succ' (I.ideal U) (n + 1)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem power_product_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) (n : ℕ) :
    LinearMap.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 M).val.app
      (Opposite.op U.1)).hom = I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  have := power_qc I n
  apply SetLike.coe_injective
  change Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 M).app
    U.1) = {s | s ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))}
  simpa only [power_range] using
    multiplication_range (idealSheafPower I.toModulesι n).2 M U

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_qc {X : Scheme.{u}} {A B C : X.Modules}
    [A.IsQuasicoherent] [B.IsQuasicoherent] [C.IsQuasicoherent]
    (f : A ⟶ C) (g : B ⟶ C) : (pullback f g).IsQuasicoherent := by
  have := Modules.isQuasicoherent_biprod A B
  have := Modules.isQuasicoherent_kernel (biprod.desc f (-g))
  let e : pullback f g ≅ kernel (biprod.desc f (-g)) :=
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g).conePointUniqueUpToIso
      (limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_range {X : Scheme.{u}} {A B C : X.Modules}
    (f : A ⟶ C) (g : B ⟶ C) (W : X.Opens) :
    Set.range ((pullback.fst f g ≫ f).app W) =
      Set.range (f.app W) ∩ Set.range (g.app W) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op W) ⋙ CategoryTheory.forget _
  have hp := (IsPullback.of_hasPullback f g).map E
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨(pullback.fst f g).app W t, rfl⟩, ?_⟩
    refine ⟨(pullback.snd f g).app W t, ?_⟩
    exact congrArg (fun q ↦ q.app W t) (pullback.condition (f := f) (g := g)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h : (↾fun _ : PUnit.{u + 1} ↦ a) ≫ E.map f =
        (↾fun _ : PUnit.{u + 1} ↦ b) ≫ E.map g := by
      ext x
      exact ha.trans hb.symm
    obtain ⟨l, hl, _⟩ := hp.exists_lift
      (↾fun _ : PUnit.{u + 1} ↦ a) (↾fun _ : PUnit.{u + 1} ↦ b) h
    refine ⟨l PUnit.unit, ?_⟩
    have he : (pullback.fst f g).app W (l PUnit.unit) = a :=
      ConcreteCategory.congr_hom hl PUnit.unit
    change f.app W ((pullback.fst f g).app W (l PUnit.unit)) = s
    rw [he, ha]

set_option backward.isDefEq.respectTransparency false in
private theorem app_zero_below_affine {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ N) (U : X.affineOpens)
    (h : ∀ t : Γ(M, U.1), φ.app U.1 t = 0) (W : X.Opens) (hWU : W ≤ U.1) :
    ∀ s : Γ(M, W), φ.app W s = 0 := by
  intro s
  classical
  have hlocal (x : W) : ∃ (f : Γ(X, U.1)), X.basicOpen f ≤ W ∧ x.1 ∈ X.basicOpen f := by
    obtain ⟨f, hf, hx⟩ := U.2.exists_basicOpen_le x (hWU x.2)
    exact ⟨f, hf, hx⟩
  choose f hf hx using hlocal
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun x : W ↦ X.basicOpen (f x)) W (fun x ↦ homOfLE (hf x)) ?_ _ _ ?_
  · intro x hxW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩
  · intro x
    rw [map_zero, ← Modules.Hom.app_presheaf_map]
    obtain ⟨k, t, ht⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen M U.2 (f x)
      (M.presheaf.map (homOfLE (hf x)).op s)
    have hz : (X.presheaf.map (homOfLE (X.basicOpen_le (f x))).op (f x)) ^ k •
        φ.app (X.basicOpen (f x)) (M.presheaf.map (homOfLE (hf x)).op s) = 0 := by
      rw [← Modules.Hom.app_smul, ← ht, Modules.Hom.app_presheaf_map, h, map_zero]
    have hu : IsUnit ((X.presheaf.map
        (homOfLE (X.basicOpen_le (f x))).op (f x) : Γ(X, X.basicOpen (f x))) ^ k) :=
      (X.toRingedSpace.isUnit_res_basicOpen (f x)).pow k
    have he := congrArg (fun t : Γ(N, X.basicOpen (f x)) ↦ hu.unit⁻¹.val • t) hz
    simpa only [smul_smul, IsUnit.val_inv_mul, one_smul, smul_zero] using he

set_option backward.isDefEq.respectTransparency false in
private theorem range_le_below_affine {X : Scheme.{u}} {A B F : X.Modules}
    [A.IsQuasicoherent] (i : A ⟶ F) (j : B ⟶ F) [Mono j] (U : X.affineOpens)
    (h : Set.range (i.app U.1) ⊆ Set.range (j.app U.1))
    (W : X.Opens) (hWU : W ≤ U.1) : Set.range (i.app W) ⊆ Set.range (j.app W) := by
  have hz : ∀ a : Γ(A, U.1), (i ≫ cokernel.π j).app U.1 a = 0 := by
    intro a
    obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
    change (cokernel.π j).app U.1 (i.app U.1 a) = 0
    rw [← hb]
    exact congrArg (fun q : B ⟶ cokernel j ↦ q.app U.1 b) (cokernel.condition j)
  rintro s ⟨a, rfl⟩
  have hs : (cokernel.π j).app W (i.app W a) = 0 :=
    app_zero_below_affine (i ≫ cokernel.π j) U hz W hWU a
  obtain ⟨b, hb⟩ := (Set.ext_iff.mp (Modules.range_map_kernelι W (cokernel.π j))
    (i.app W a)).mpr hs
  refine ⟨(inv (Abelian.factorThruImage j)).app W b, ?_⟩
  have hj : inv (Abelian.factorThruImage j) ≫ j = Abelian.image.ι j := by
    calc
      _ = inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
        congrArg (fun q ↦ inv (Abelian.factorThruImage j) ≫ q) (Abelian.image.fac j).symm
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  exact (congrArg (fun q : Abelian.image j ⟶ F ↦ q.app W b) hj).trans hb


namespace Modules

set_option backward.isDefEq.respectTransparency false in
/-- An inclusion between affine section submodules gives the corresponding inclusion
of ideal products on every subopen. No bound, coherence or Noetherian hypothesis is used.
Source: Stacks Project, Tag 01YA, affine reduction; Tags 01I8 and 01IC.
(blueprint: lem-pc-affine-ideal-intersection-inclusion)

Proof: Restrict to the affine scheme U. Quasi-coherent modules are the sheaves associated
to their section modules. The affine equivalence is exact and respects tensor products
(01I8); consequently it respects images, kernels and intersections. The ideal I and its
recursive powers correspond to I(U) and its ordinary powers, including power zero,
which is the structure sheaf. Thus I^m F intersect G corresponds to
I(U)^m F(U) intersect image(g(U)), whereas the image of I^n G in F corresponds to
map(g(U), I(U)^n G(U)). The assumed inclusion factors the first inclusion into F
through the second. Apply the affine equivalence (01IC) and restrict the factorization
to W. A section in both ranges lifts uniquely to the intersection sheaf: the two
preimages satisfy the pullback condition, since their images agree. Its image under
the factorization is a preimage in I^n G, proving the range inclusion. This works for
an empty U or W, m=0, n=0, zero modules, and zero or unit ideals. -/
theorem affine_ideal_intersection_inclusion {X : Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : G ⟶ F) [Mono g] (I : X.IdealSheafData) (U : X.affineOpens) (m n : ℕ)
    (hmodule : I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range (g.val.app (.op U.1)).hom ≤
      Submodule.map (g.val.app (.op U.1)).hom
        (I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)))) :
    ∀ W : X.Opens, W ≤ U.1 →
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι m).2 F).app W) ∩
          Set.range (g.app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 G ≫ g).app W) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let p := idealModuleProductι (idealSheafPower I.toModulesι m).2 F
  let q := idealModuleProductι (idealSheafPower I.toModulesι n).2 G
  have hpqc : (idealModuleProduct (idealSheafPower I.toModulesι m).2 F).IsQuasicoherent := by
    have := power_qc I m
    exact product_qc (idealSheafPower I.toModulesι m).2 F
  have hq : Mono q := by
    dsimp [q, idealModuleProductι]
    infer_instance
  have := pullback_qc p g
  have ha : Set.range ((pullback.fst p g ≫ p).app U.1) ⊆
      Set.range ((q ≫ g).app U.1) := by
    rw [pullback_range]
    rintro s ⟨hs, ht⟩
    have hs' : s ∈ I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := by
      rw [← power_product_range I F U m]
      exact hs
    obtain ⟨t, ht, he⟩ := hmodule ⟨hs', ht⟩
    have ht' : t ∈ LinearMap.range (q.val.app (.op U.1)).hom := by
      rw [show LinearMap.range (q.val.app (.op U.1)).hom = _ from
        power_product_range I G U n]
      exact ht
    obtain ⟨b, hb⟩ := ht'
    refine ⟨b, ?_⟩
    change g.app U.1 (q.app U.1 b) = s
    change q.app U.1 b = t at hb
    change g.app U.1 t = s at he
    exact (congrArg (g.app U.1) hb).trans he
  intro W hWU
  rw [← pullback_range p g W]
  exact range_le_below_affine (pullback.fst p g ≫ p) (q ≫ g) U ha W hWU


end Modules

end AlgebraicGeometry.Scheme
