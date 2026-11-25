/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Blowup.Affine.ReesGrading
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

open CategoryTheory.Limits Scheme in
private theorem power_range_affine {X : Scheme.{v}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (U : X.affineOpens) :
    Set.range ((idealSheafPower J.toModulesι n).2.app U.1) =
      {a | a ∈ J.ideal U ^ n} := by
  cases n with
  | zero => simp [idealSheafPower]
  | succ n =>
    exact ((Modules.ideal_times_quasiCoherent_affine_sections J F).2.2.2.1 U).2.2.2 _
      (Nat.succ_pos n)

open CategoryTheory.Limits Scheme in
private theorem power_quasicoherent {X : Scheme.{v}} (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (idealSheafPower J.toModulesι n).1.IsQuasicoherent := by
  cases n with
  | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  | succ n =>
    exact (Modules.ideal_times_quasiCoherent_affine_sections J F).2.2.1 _ (Nat.succ_pos n)

set_option backward.isDefEq.respectTransparency false in
/-- Componentwise multiplication map; this is the affine gluing step in Tag 02O8.
Source: Stacks Project, coherent.tex, Tag 02O8, lines 5330--5400.
(blueprint: lem-weil-pbc-ideal-powers-rees-multiplication-component)

Proof: on each affine open, multiplication by the coefficient preserves the ideal-power
product by the ideal-power and extended-ideal section formulas. These local maps agree on
overlaps and glue to a module-sheaf morphism; the displayed formula is the resulting
coefficient identity.
-/
theorem idealPowersReesMultiplication_component {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent] :
    let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
    let graded := reesGrading I
    ∀ (m k : ℕ) (b : graded k), ∃ mu : G m ⟶ G (m + k),
      ∀ (U : X.Opens) (s : (G m).val.obj (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
          U).hom ((mu.app U) s) =
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
          (b.val.val.coeff k)) •
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
          U).hom s := open CategoryTheory.Limits Scheme in by
  classical
  dsimp only
  intro m k b
  have image_range_affine : ∀ {X : Scheme.{v}} {M N : X.Modules}
      (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] (U : X.affineOpens),
      Set.range ((image.ι φ).app U.1) = Set.range (φ.app U.1) := by
    intro X M N φ _ _ U
    let e := Abelian.imageIsoImage φ
    have he : Function.Surjective (e.hom.app U.1) :=
      (Modules.appLinearEquivOfIso e U.1).surjective
    have hf : e.hom ≫ image.ι φ = Abelian.image.ι φ :=
      Abelian.imageIsoImage_hom_comp_image_ι φ
    have hr : Set.range ((image.ι φ).app U.1) =
        Set.range ((Abelian.image.ι φ).app U.1) := by
      rw [← hf, Modules.Hom.comp_app]
      ext s
      constructor
      · rintro ⟨t, rfl⟩
        obtain ⟨a, rfl⟩ := he t
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨e.hom.app U.1 a, rfl⟩
    exact hr.trans ((Modules.quasiCoherent_cokernel_image φ).2.2.2.2.2.2.2.2 U).1
  have product_range_affine : ∀ {X : Scheme.{v}} {J : X.Modules}
      (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
      [J.IsQuasicoherent] [M.IsQuasicoherent] (U : X.affineOpens),
      Set.range ((idealModuleProductι ι M).app U.1) =
        (AddSubgroup.closure {s | ∃ (a : Γ(J, U.1)) (t : Γ(M, U.1)),
          s = (Modules.unitSectionsEquiv U.1).symm (ι.app U.1 a) • t} : Set Γ(M, U.1)) := by
    intro X J ι M _ _ U
    let ψ : MonoidalCategoryStruct.tensorObj J M ⟶ M :=
      MonoidalCategoryStruct.whiskerRight ι M ≫ (MonoidalCategoryStruct.leftUnitor M).hom
    have : (MonoidalCategoryStruct.tensorObj J M).IsQuasicoherent :=
      (Modules.quasiCoherent_tensor_product_affine_sections J M).1
    change Set.range ((image.ι ψ).app U.1) = _
    rw [image_range_affine ψ U]
    let H := AddSubgroup.closure {s | ∃ (a : Γ(J, U.1)) (t : Γ(M, U.1)),
      s = (Modules.unitSectionsEquiv U.1).symm (ι.app U.1 a) • t}
    have ht (a : Γ(J, U.1)) (t : Γ(M, U.1)) :
        ψ.app U.1 (Modules.tmulSection a t) =
          (Modules.unitSectionsEquiv U.1).symm (ι.app U.1 a) • t := by
      rw [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Modules.whiskerRight_app_tmulSection]
      exact Modules.leftUnitor_hom_app_tmulSection' _ _
    apply Set.Subset.antisymm
    · rintro _ ⟨s, rfl⟩
      obtain ⟨z, rfl⟩ :=
        (Modules.quasiCoherent_tensor_product_affine_sections J M).2 U.1 U.2 |>.2 s
      induction z using TensorProduct.inductionOn with
      | tmul a t =>
        rw [Modules.tensorSectionsMap_tmul, ht]
        exact AddSubgroup.subset_closure ⟨a, t, rfl⟩
      | add z z' hz hz' =>
        simp only [map_add]
        exact H.add_mem hz hz'
    · change H ≤ (ψ.val.app (op U.1)).hom.range.toAddSubgroup
      apply (AddSubgroup.closure_le _).mpr
      rintro s ⟨a, t, rfl⟩
      exact ⟨Modules.tmulSection a t, ht a t⟩
  have hom_zero_of_affine : ∀ {X : Scheme.{v}} {M N : X.Modules}
      (φ : M ⟶ N) (h : ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = 0),
      φ = 0 := by
    intro X M N φ h
    apply Modules.hom_ext
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
      rw [← Modules.Hom.app_presheaf_map, map_zero]
      exact h i.1 _
  let G := fun n ↦ idealModuleProduct (idealSheafPower J.toModulesι n).2 F
  let j := fun n ↦ idealModuleProductι (idealSheafPower J.toModulesι n).2 F
  let φ (U : X.Opens) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
  let a := b.val.val.coeff k
  have ha : a ∈ I ^ k := (mem_reesAlgebra_iff I b.val.val).mp b.val.property k
  let c : Γ(X, ⊤) := φ ⊤ a
  let α : G m ⟶ F := j m ≫ Modules.smulHom F c
  have hscalar (U : X.Opens) (s : Γ(G m, U)) :
      α.app U s = φ U a • (j m).app U s := by
    change X.presheaf.map (homOfLE (le_top (a := U))).op c • (j m).app U s = _
    congr 1
    change X.presheaf.map (homOfLE (le_top (a := U))).op (φ ⊤ a) = φ U a
    dsimp only [φ]
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]
  have hcoeff (U : X.affineOpens) : φ U.1 a ∈ J.ideal U ^ k := by
    have he : J.ideal U = Ideal.map (φ U.1) I := by
      rw [hJ, IdealSheafData.ideal_comap_appLE _ f
        ⟨⊤, isAffineOpen_top _⟩ U le_top, IdealSheafData.ideal_top_ofIdealTop,
        Ideal.map_map]
      rfl
    rw [he, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have hqc (n : ℕ) : (idealSheafPower J.toModulesι n).1.IsQuasicoherent :=
    power_quasicoherent J F n
  have hrange (U : X.affineOpens) (s : Γ(G m, U.1)) :
      α.app U.1 s ∈ Set.range ((j (m + k)).app U.1) := by
    let := hqc m
    let := hqc (m + k)
    rw [hscalar]
    rw [product_range_affine (idealSheafPower J.toModulesι (m + k)).2 F U]
    let H := AddSubgroup.closure {z | ∃ (d : Γ((idealSheafPower J.toModulesι
      (m + k)).1, U.1)) (t : Γ(F, U.1)),
      z = (Modules.unitSectionsEquiv U.1).symm
        ((idealSheafPower J.toModulesι (m + k)).2.app U.1 d) • t}
    have hs : (j m).app U.1 s ∈
        AddSubgroup.closure {z | ∃ (d : Γ((idealSheafPower J.toModulesι m).1, U.1))
          (t : Γ(F, U.1)), z = (Modules.unitSectionsEquiv U.1).symm
            ((idealSheafPower J.toModulesι m).2.app U.1 d) • t} := by
      exact (Set.ext_iff.mp
        (product_range_affine (idealSheafPower J.toModulesι m).2 F U) _).mp ⟨s, rfl⟩
    change φ U.1 a • (j m).app U.1 s ∈ H
    generalize (j m).app U.1 s = z at hs ⊢
    induction hs using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨d, t, rfl⟩ := hz
      have hd : (idealSheafPower J.toModulesι m).2.app U.1 d ∈ J.ideal U ^ m :=
        (Set.ext_iff.mp (power_range_affine J F m U) _).mp ⟨d, rfl⟩
      have hp : φ U.1 a *
          (show Γ(X, U.1) from (idealSheafPower J.toModulesι m).2.app U.1 d) ∈
          J.ideal U ^ (m + k) := by
        rw [pow_add, mul_comm (J.ideal U ^ m)]
        exact Ideal.mul_mem_mul (hcoeff U) hd
      obtain ⟨e, he⟩ := (Set.ext_iff.mp (power_range_affine J F (m + k) U) _).mpr hp
      apply AddSubgroup.subset_closure
      refine ⟨e, t, ?_⟩
      change φ U.1 a •
          ((show Γ(X, U.1) from (idealSheafPower J.toModulesι m).2.app U.1 d) • t) =
        (show Γ(X, U.1) from (idealSheafPower J.toModulesι (m + k)).2.app U.1 e) • t
      rw [← mul_smul, he]
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [smul_add] using H.add_mem ihx ihy
    | neg x hx ih => simpa only [smul_neg] using H.neg_mem ih
  have hz : α ≫ cokernel.π (j (m + k)) = 0 := by
    apply hom_zero_of_affine
    intro U s
    obtain ⟨t, ht⟩ := hrange U s
    change (cokernel.π (j (m + k))).app U.1 (α.app U.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app U.1 t) (cokernel.condition (j (m + k)))
  have : Mono (j (m + k)) := by
    dsimp [j, idealModuleProductι]
    infer_instance
  let l : G m ⟶ G (m + k) :=
    kernel.lift (cokernel.π (j (m + k))) α hz ≫ inv (Abelian.factorThruImage (j (m + k)))
  have hl : l ≫ j (m + k) = α := by
    dsimp only [l]
    let t := kernel.lift (cokernel.π (j (m + k))) α hz
    change t ≫ inv (Abelian.factorThruImage (j (m + k))) ≫ j (m + k) = α
    calc
      _ = t ≫ inv (Abelian.factorThruImage (j (m + k))) ≫
          Abelian.factorThruImage (j (m + k)) ≫ Abelian.image.ι (j (m + k)) :=
        congrArg (fun q ↦ t ≫ inv (Abelian.factorThruImage (j (m + k))) ≫ q)
          (Abelian.image.fac (j (m + k))).symm
      _ = t ≫ Abelian.image.ι (j (m + k)) := by rw [IsIso.inv_hom_id_assoc]
      _ = α := kernel.lift_ι _ _ hz
  refine ⟨l, fun U s ↦ ?_⟩
  exact (congrArg (fun q ↦ q.app U s) hl).trans (hscalar U s)

end AlgebraicGeometry
