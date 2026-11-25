/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Affine comparison for ideal products and intersections

Source: Stacks Project, Cohomology of Schemes, Tag 01YA, affine reduction in the proof;
Algebra, Tag 00IN (blueprint: lem-weil-pbc-artin-rees-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme



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
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  cases n with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | succ n =>
    exact (Modules.ideal_times_quasiCoherent_affine_sections I
      (SheafOfModules.unit X.ringCatSheaf)).2.2.1 (n + 1) (Nat.succ_pos n)

set_option backward.isDefEq.respectTransparency false in
private theorem power_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    (LinearMap.range ((idealSheafPower I.toModulesι n).2.val.app (Opposite.op U.1)).hom :
      Ideal Γ(X, U.1)) = I.ideal U ^ n := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  cases n with
  | zero =>
    apply SetLike.coe_injective
    ext s
    change (∃ y : Γ(X, U.1), y = s) ↔ s ∈ (1 : Ideal Γ(X, U.1))
    simp
  | succ n =>
    exact SetLike.coe_injective
      (((Modules.ideal_times_quasiCoherent_affine_sections I
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 (n + 1)
          (Nat.succ_pos n))

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

set_option backward.isDefEq.respectTransparency false in
/-- An equality of ideal products and intersections of affine section modules yields
an equality of the corresponding subsheaves on that affine open. This is the geometric
comparison only; neither coherence, a Noetherian hypothesis, nor an Artin-Rees bound
is assumed.

Source: Stacks Project, Cohomology of Schemes, Tag 01YA, affine reduction in the proof;
Schemes, Tags 01I8 and 01IC
(blueprint: lem-weil-pbc-artin-rees-affine-comparison).

Proof: Products by the powers of I are quasi-coherent, including the zeroth power.
For every t, realize H_t = I^t F ∩ G as the kernel of G → F/(I^t F).
The quotient, kernel, and ideal products of this kernel are quasi-coherent.
Evaluation on the affine open is exact on quasi-coherent modules. Thus H_t(U)
is I(U)^t F(U) ∩ image(G(U) → F(U)), with its inclusion into F(U).
The affine product formula identifies the image of I^(n-c) H_c on U with
I(U)^(n-c) (I(U)^c F(U) ∩ image(G(U) → F(U))). The assumed module equality
therefore identifies the affine sections of I^(n-c) H_c and H_n, compatibly
with both inclusions into F. Restrict these quasi-coherent modules to U.
The affine tilde/global-sections equivalence transports the equality into an
isomorphism of the two submodules of F restricted to U, commuting with their
inclusions. Evaluate this isomorphism on any W ≤ U to obtain equality of ranges.
The empty open, zero modules, zero or unit ideal, and c=0 or n=0 need no exclusion:
exactness and the affine equivalence hold for them, and I^0 is the unit ideal. -/
theorem artin_rees_affine_comparison {X : Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : G ⟶ F) [Mono g] (I : X.IdealSheafData) (U : X.affineOpens) (c n : ℕ)
    (hmodule : I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range (g.val.app (.op U.1)).hom =
      I.ideal U ^ (n - c) • (I.ideal U ^ c •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range (g.val.app (.op U.1)).hom)) :
    ∀ W : X.Opens, W ≤ U.1 →
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
        (pullback (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g) ≫
          pullback.fst (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g ≫
            idealModuleProductι (idealSheafPower I.toModulesι c).2 F).app W) =
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) := by
  let P (t : ℕ) := idealModuleProduct (idealSheafPower I.toModulesι t).2 F
  let p (t : ℕ) : P t ⟶ F := idealModuleProductι (idealSheafPower I.toModulesι t).2 F
  have hP (t : ℕ) : (P t).IsQuasicoherent := by
    have := power_qc I t
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have := (Modules.quasiCoherent_tensor_product_affine_sections
      (idealSheafPower I.toModulesι t).1 F).1
    let a := MonoidalCategory.whiskerRight (idealSheafPower I.toModulesι t).2 F ≫
      (MonoidalCategory.leftUnitor F).hom
    have hi := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage a) hi
  have hp (t : ℕ) : Mono (p t) := by
    dsimp [p, idealModuleProductι]
    infer_instance
  let H := pullback (p c) g
  let h : H ⟶ F := pullback.fst (p c) g ≫ p c
  have : (P c).IsQuasicoherent := hP c
  have : (P n).IsQuasicoherent := hP n
  have : H.IsQuasicoherent := pullback_qc (p c) g
  have : Mono (p c) := hp c
  have : Mono (p n) := hp n
  have : Mono h := by dsimp [h]; infer_instance
  have := power_qc I (n - c)
  let L := idealModuleProduct (idealSheafPower I.toModulesι (n - c)).2 H
  let l : L ⟶ F := idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 H ≫ h
  have : L.IsQuasicoherent := by
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have := (Modules.quasiCoherent_tensor_product_affine_sections
      (idealSheafPower I.toModulesι (n - c)).1 H).1
    let a := MonoidalCategory.whiskerRight (idealSheafPower I.toModulesι (n - c)).2 H ≫
      (MonoidalCategory.leftUnitor H).hom
    have hi := (Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage a) hi
  have hprod : Mono (idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 H) := by
    dsimp [idealModuleProductι]
    infer_instance
  have : Mono l := by dsimp [l]; infer_instance
  let N := pullback (p n) g
  let j : N ⟶ F := pullback.fst (p n) g ≫ p n
  have : N.IsQuasicoherent := pullback_qc (p n) g
  have : Mono j := by dsimp [j]; infer_instance
  have hi (t : ℕ) :
      LinearMap.range ((pullback.fst (p t) g ≫ p t).val.app (Opposite.op U.1)).hom =
        I.ideal U ^ t • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range (g.val.app (Opposite.op U.1)).hom := by
    apply SetLike.coe_injective
    have he := pullback_range (p t) g U.1
    have hf := congrArg (fun Q : Submodule Γ(X, U.1) Γ(F, U.1) ↦
      (Q : Set Γ(F, U.1))) (power_product_range I F U t)
    change Set.range ((pullback.fst (p t) g ≫ p t).app U.1) =
      {s | s ∈ I.ideal U ^ t • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))} ∩
        Set.range (g.app U.1)
    rw [he]
    exact congrArg (fun Q ↦ Q ∩ Set.range (g.app U.1)) hf
  have hl : LinearMap.range (l.val.app (Opposite.op U.1)).hom =
      I.ideal U ^ (n - c) • (I.ideal U ^ c •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range (g.val.app (Opposite.op U.1)).hom) := by
    change LinearMap.range ((h.val.app (Opposite.op U.1)).hom.comp
      ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 H).val.app
        (Opposite.op U.1)).hom) = _
    rw [LinearMap.range_comp, power_product_range, Submodule.map_smul'',
      Submodule.map_top]
    exact congrArg (fun Q : Submodule Γ(X, U.1) Γ(F, U.1) ↦
      I.ideal U ^ (n - c) • Q) (hi c)
  have he : Set.range (l.app U.1) = Set.range (j.app U.1) := by
    have he' : LinearMap.range (l.val.app (Opposite.op U.1)).hom =
        LinearMap.range (j.val.app (Opposite.op U.1)).hom :=
      hl.trans (hmodule.symm.trans (hi n).symm)
    exact congrArg (fun Q : Submodule Γ(X, U.1) Γ(F, U.1) ↦
      (Q : Set Γ(F, U.1))) he'
  intro W hWU
  have heW : Set.range (l.app W) = Set.range (j.app W) :=
    Set.Subset.antisymm (range_le_below_affine l j U he.subset W hWU)
      (range_le_below_affine j l U he.symm.subset W hWU)
  exact heW.trans (pullback_range (p n) g W)

end AlgebraicGeometry.Scheme
