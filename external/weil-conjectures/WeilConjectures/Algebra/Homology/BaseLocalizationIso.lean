/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import WeilConjectures.Algebra.Homology.BaseLocalizationMap
import WeilConjectures.Algebra.Homology.BaseLocalizationCohomologyIsIso
import WeilConjectures.Algebra.Homology.BaseLocalizationCohomologyAction
import WeilConjectures.Algebra.Homology.BaseLocalizationDLinearGlue
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-localization-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra Rp A] [Algebra Rp B]
  [tRpA : IsScalarTower R Rp A] [tRpB : IsScalarTower R Rp B]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [Algebra A D] [Algebra B D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] B) D]
  [tBpD : IsScalarTower B (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

include tRpA tRpB tAD tBD tApD tBpD in
/-- The canonical map is invertible after extension to D.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-base-localization-iso).

Proof: choose a K-flat Rp-resolution P of the underlying Rp-complex of Q.
Its restriction to R is K-flat: for an acyclic R-complex F, exact localization
Rp tensor_R F is acyclic, and tensor associativity identifies its tensor with
P with F tensor_R P. Both universal derived counits are invertible on these
K-flat complexes. Naturality with respect to the resolution augmentation,
which is a quasi-isomorphism both before and after restriction, therefore
shows that the universal lift defining baseLocalizationDerivedMap is
invertible at Q. Its counit equation identifies it with the pure-tensor
localization identity. Naturality for multiplication by a in A and
cohomologyIso_smul show that the cohomology map intertwines the two A-actions;
B-linearity is built in. The algebra isomorphism A tensor_Rp B = A tensor_R B
fixes pure tensors, so the cohomology map is an isomorphism after transporting
this tensor-algebra action. The maps to D agree on A and B by the scalar-tower
hypotheses. Extend the transported isomorphism to D. Tensor induction gives
the displayed generator equation and its uniqueness. For the identity
localization the universal lift is the unique model comparison. If S contains
zero, Rp, A, B and D are zero rings and the conclusion is the unique zero-module
isomorphism. No flatness of D or boundedness of Q is used. -/
theorem exists_baseLocalization_iso (S : Submonoid R) [IsLocalization S Rp] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :
    ∃ e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i),
      IsBaseLocalizationMap R Rp B A D S Q L K i e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    have hf := baseLocalizationCohomologyMap_isIso R Rp B A D S Q L K i
    have hA := baseLocalizationCohomologyMap_smul R Rp B A D S Q L K i
    let φ := (IsLocalization.algebraTensorEquiv S Rp A B).symm.toRingEquiv
    let f := (baseLocalizationCohomologyMap R Rp B A D S Q L K i).hom
    have hφ (a : A) (b : B) : φ (a ⊗ₜ[R] b) = a ⊗ₜ[Rp] b := rfl
    let N := (ModuleCat.restrictScalars φ.toRingHom).obj (K.cohomology i)
    let g : L.cohomology i ⟶ N := ModuleCat.ofHom (Y := N)
      { toFun := fun x ↦ f x
        map_add' := fun x y ↦ map_add f x y
        map_smul' := by
          intro z x
          change f (z • x) = φ z • f x
          induction z using TensorProduct.inductionOn with
          | tmul a b =>
            have hsplit : a ⊗ₜ[R] b =
                (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            have hsplitp : a ⊗ₜ[Rp] b =
                (a ⊗ₜ[Rp] (1 : B)) * ((1 : A) ⊗ₜ[Rp] b) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [hφ, hsplit, hsplitp, mul_smul, mul_smul]
            have ha := hA a ((1 : A) ⊗ₜ[R] b • x)
            change f ((a ⊗ₜ[R] (1 : B)) • _) =
              (a ⊗ₜ[Rp] (1 : B)) • f _ at ha
            rw [ha]
            congr 1
            exact f.map_smul b
              (show (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
                  (L.cohomology i) from x)
          | add z z' hz hz' =>
            simp only [add_smul, map_add, hz, hz'] }
    have hg : IsIso g := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective f
      exact (ConcreteCategory.isIso_iff_bijective _).mp hf
    have hD : (algebraMap (A ⊗[Rp] B) D).comp φ.toRingHom =
        algebraMap (A ⊗[R] B) D := by
      apply RingHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change algebraMap (A ⊗[Rp] B) D (φ (a ⊗ₜ[R] b)) = _
        rw [hφ]
        have hsplit (T : Type u) [CommRing T] [Algebra T A] [Algebra T B] :
            a ⊗ₜ[T] b = (a ⊗ₜ[T] (1 : B)) * ((1 : A) ⊗ₜ[T] b) := by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hsplit Rp, hsplit R, map_mul, map_mul]
        congr 1
        · exact (IsScalarTower.algebraMap_apply A (A ⊗[Rp] B) D a).symm.trans
            (IsScalarTower.algebraMap_apply A (A ⊗[R] B) D a)
        · exact (IsScalarTower.algebraMap_apply B (A ⊗[Rp] B) D b).symm.trans
            (IsScalarTower.algebraMap_apply B (A ⊗[R] B) D b)
      | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
    obtain ⟨e, he⟩ := ModuleCat.exists_extendScalars_iso_of_ringEquiv φ
      (algebraMap (A ⊗[R] B) D) (algebraMap (A ⊗[Rp] B) D) hD
      (L.cohomology i) (K.cohomology i) g hg
    exact ⟨e, he⟩

end RingTensorCohomology
