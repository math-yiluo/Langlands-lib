/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Annihilation of kernels and cokernels of coherent formal module maps -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Shifting the sequential diagram gives surjectivity at every index.
private theorem projection_surjective {A : Type u} [CommRing A]
    (D : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hs : ∀ m : ℕ, Function.Surjective (D.map (homOfLE (Nat.le_succ m)).op))
    (n : ℕ) : Function.Surjective (limit.π D (op n)) := by
  let hm : Monotone (fun m : ℕ ↦ n + m) := fun _ _ h ↦ Nat.add_le_add_left h n
  let s := hm.functor
  have : s.Final := (Monotone.final_functor_iff hm).mpr
    (fun m ↦ ⟨m, Nat.le_add_left m n⟩)
  have : s.op.Initial := inferInstance
  have hp := Concrete.surjective_π_app_zero_of_surjective_map
    ((Functor.Initial.isLimitWhiskerEquiv s.op (limit.cone D)).symm (limit.isLimit D))
    (fun m ↦ hs (n + m))
  simpa [s, hm] using hp

set_option backward.isDefEq.respectTransparency false in
private theorem product_qc {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [J.IsQuasicoherent] [M.IsQuasicoherent] :
    (Scheme.idealModuleProduct ι M).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections J M).1
  let a := MonoidalCategoryStruct.whiskerRight ι M ≫
    (MonoidalCategoryStruct.leftUnitor M).hom
  have := Scheme.Modules.isQuasicoherent_cokernel a
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem formal_projection_surjective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (M : CoherentFormalModule X I) (V : X.affineOpens) (n : ℕ) :
    Function.Surjective
      (limit.π (M.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) (op n)) := by
  apply projection_surjective (A := Γ(X, V.1))
  intro m
  have hqc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X (M.obj.obj (op (m + 1)))).mp (M.property.1 (m + 1))
  have : (M.obj.obj (op (m + 1))).IsQuasicoherent := hqc.1
  have : (Scheme.idealSheafPower I.toModulesι (m + 1)).1.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
      (M.obj.obj (op (m + 1)))).2.2.1 (m + 1) (by omega)
  have := product_qc (Scheme.idealSheafPower I.toModulesι (m + 1)).2
    (M.obj.obj (op (m + 1)))
  obtain ⟨e, he⟩ := M.property.2.2 m
  have hp := (Scheme.Modules.quasiCoherent_cokernel_image
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (m + 1)).2
      (M.obj.obj (op (m + 1))))).2.2.2.2.2.2.2.2 V
  have hs := hp.2.1
  change Function.Surjective ((M.obj.map (homOfLE (Nat.le_succ m)).op).app V.1)
  rw [← he]
  exact ((Scheme.Modules.appLinearEquivOfIso e V.1).surjective).comp hs

set_option backward.isDefEq.respectTransparency false in
private theorem product_zero_on_affine_cover {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [J.IsQuasicoherent] [M.IsQuasicoherent]
    {r : ℕ} (V : Fin r → X.affineOpens) (hV : (⨆ i, (V i).1) = ⊤)
    (h : ∀ i (a : Γ(J, (V i).1)) (s : Γ(M, (V i).1)),
      (Scheme.Modules.unitSectionsEquiv (V i).1).symm (ι.app (V i).1 a) • s = 0) :
    IsZero (Scheme.idealModuleProduct ι M) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := MonoidalCategoryStruct.whiskerRight ι M ≫
    (MonoidalCategoryStruct.leftUnitor M).hom
  have ht := Scheme.Modules.quasiCoherent_tensor_product_affine_sections J M
  have : (MonoidalCategoryStruct.tensorObj J M).IsQuasicoherent := ht.1
  have ha (i : Fin r) : a.app (V i).1 = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := (ht.2 (V i).1 (V i).2).2 x
    induction y using TensorProduct.inductionOn with
    | tmul j s =>
      change a.app (V i).1 (Scheme.Modules.tmulSection j s) = 0
      dsimp only [a]
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.whiskerRight_app_tmulSection]
      erw [Scheme.Modules.leftUnitor_hom_app_tmulSection']
      exact h i j s
    | add x y hx hy => simp only [map_add, hx, hy]
  have haz : a = 0 := by
    apply Scheme.Modules.hom_eq_zero_of_restrict a (fun i ↦ (V i).1) hV
    intro i
    have : IsAffine (V i).1.toScheme := (V i).2
    have := Scheme.Modules.isQuasicoherent_restrictFunctor (V i).1.ι
      (MonoidalCategoryStruct.tensorObj J M)
    apply Scheme.Modules.hom_ext_of_isAffine
    intro x
    change a.app ((V i).1.ι ''ᵁ ⊤) x = 0
    have heq : (V i).1.ι ''ᵁ ⊤ = (V i).1 := by simp
    have hz : a.app ((V i).1.ι ''ᵁ ⊤) = 0 := by
      rw [heq]
      exact ha i
    exact ConcreteCategory.congr_hom hz x
  have : Mono (image.ι a) := inferInstance
  apply IsZero.of_mono_eq_zero (image.ι a)
  apply (cancel_epi (factorThruImage a)).1
  simpa only [image.fac, comp_zero] using haz

set_option backward.isDefEq.respectTransparency false in
/-- An intermediate cokernel-annihilation component of the affine-cover reduction.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power-cokernel).
The proof is the corresponding kernel/cokernel half of the finite affine-cover
argument. The finite affine cover is reduced modulo each power of the ideal, the
commutative-algebra annihilation lemma is applied, and local annihilation is glued
over the affine cover.
-/
theorem coherentFormalModule_annihilated_double_cokernel (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ)
    (hcover : (⨆ i, (U i).1) = ⊤) (ht : 1 ≤ t)
    (h : ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (α.hom.app (op n)))) := by
  -- Surjective limit projections pass the cokernel bound t to each level.
  -- The stated exponent follows from K^(2*t) ≤ K^t.
  intro n
  have hF : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  have hG : (G.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (G.property.1 n)).1
  have hQ := Scheme.Modules.isQuasicoherent_cokernel (α.hom.app (op n))
  have hK : (Scheme.idealSheafPower K.toModulesι (2 * t)).1.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections K
      (cokernel (α.hom.app (op n)))).2.2.1 (2 * t) (by omega)
  apply product_zero_on_affine_cover _ _ U hcover
  intro i a s
  let b : Γ(X, (U i).1) := (Scheme.Modules.unitSectionsEquiv (U i).1).symm
    ((Scheme.idealSheafPower K.toModulesι (2 * t)).2.app (U i).1 a)
  have hb₂ : b ∈ K.ideal (U i) ^ (2 * t) := by
    have hr := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections K
      (cokernel (α.hom.app (op n)))).2.2.2.1 (U i) |>.2.2.2 (2 * t) (by omega)
    exact Set.ext_iff.mp hr b |>.mp ⟨a, rfl⟩
  have hb : b ∈ K.ideal (U i) ^ t :=
    Ideal.pow_le_pow_right (by omega : t ≤ 2 * t) hb₂
  have hc₀ := Scheme.Modules.quasiCoherent_cokernel_image (α.hom.app (op n))
  have hc := hc₀.2.2.2.2.2.2.2.2 (U i)
  obtain ⟨y, rfl⟩ := hc.2.1 s
  obtain ⟨z, hz⟩ := formal_projection_surjective I G (U i) n y
  let D := G.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)
  let C := F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)
  let f := lim.map (Functor.whiskerRight α.hom
    (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))
  have hann := Module.mem_annihilator.mp ((h i).2 hb)
    ((LinearMap.range f.hom).mkQ z)
  have hmem : b • z ∈ LinearMap.range f.hom := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f.hom)).mp
    change (LinearMap.range f.hom).mkQ (b • z) = 0
    rw [map_smul]
    exact hann
  obtain ⟨x, hx⟩ := hmem
  have hn : (α.hom.app (op n)).app (U i).1 (limit.π C (op n) x) = b • y := by
    have hn := ConcreteCategory.congr_hom
      (limMap_π (Functor.whiskerRight α.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1))) (op n)) x
    change limit.π D (op n) (f x) =
      (α.hom.app (op n)).app (U i).1 (limit.π C (op n) x) at hn
    rw [hx, map_smul, hz] at hn
    exact hn.symm
  change b • (cokernel.π (α.hom.app (op n))).app (U i).1 y = 0
  rw [← Scheme.Modules.Hom.app_smul, ← hn]
  have hz := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.app (U i).1) (cokernel.condition (α.hom.app (op n))))
    (limit.π C (op n) x)
  exact hz

end AlgebraicGeometry
