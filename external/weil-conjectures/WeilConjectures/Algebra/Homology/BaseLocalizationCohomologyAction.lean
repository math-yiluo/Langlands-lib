/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseLocalizationMap

/-! # The A-action on the canonical base-localization cohomology map

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-action).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R Rp B A D : Type u)
  [CommRing R] [CommRing Rp] [CommRing B] [CommRing A] [CommRing D]
  [Algebra R Rp] [Algebra R B] [Algebra Rp B] [IsScalarTower R Rp B]
  [Algebra R A] [Algebra Rp A] [IsScalarTower R Rp A]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The canonical B-linear comparison also intertwines multiplication from A.
Source: Stacks Project, Tag 06Y6, functoriality of lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-action).

Proof: apply naturality of the input restriction isomorphism and of the universal
left-derived lift to multiplication by a on Q. Their composite commutes with the
endomorphism obtained by applying each derived functor to that multiplication.
Apply B-homology and conjugate by the model cohomology isomorphisms. The equations
cohomologyIso_smul on L and K identify these endomorphisms with multiplication by
a tensor 1. Evaluating the resulting equality of B-linear maps at x yields the
formula. This uses neither invertibility of the lift nor any scalar towers into D.
For a = 0 and a = 1 the equations are respectively additivity and the identity;
zero complexes and zero coefficient rings satisfy the same calculation. -/
theorem baseLocalizationCohomologyMap_smul
    (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
    (i : ℤ) (a : A) (x : L.cohomology i) :
    baseLocalizationCohomologyMap R Rp B A D S Q L K i
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := Rp) a : A ⊗[Rp] B) •
        baseLocalizationCohomologyMap R Rp B A D S Q L K i x := by
  let T := (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory
  let η := baseLocalizationDerivedMap R Rp B A D S Q L K
  let FR := restrict R A ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
    DerivedCategory.Qh
  let FP := restrict Rp A ⋙ HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ) ⋙
    DerivedCategory.Qh
  let ar := FR.map (a • 𝟙 Q)
  let ap := FP.map (a • 𝟙 Q)
  let v := (baseLocalizationInputIso R Rp A Q).hom
  have hab : ar ≫ v = v ≫ T.map ap :=
    (baseLocalizationInputNatIso R Rp A).hom.naturality (a • 𝟙 Q)
  have hd : L.derived.map ar ≫ L.derived.map v ≫ η.app _ =
      L.derived.map v ≫ η.app _ ≫ K.derived.map ap := by
    rw [← Functor.map_comp_assoc, hab, Functor.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun t ↦ L.derived.map v ≫ t) (η.naturality ap)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let gl := (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) •
    𝟙 (L.cohomology i)
  let gk := (Algebra.TensorProduct.includeLeft (S := Rp) a : A ⊗[Rp] B) •
    𝟙 (K.cohomology i)
  have hb :
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map gl ≫
          baseLocalizationCohomologyMap R Rp B A D S Q L K i =
      baseLocalizationCohomologyMap R Rp B A D S Q L K i ≫
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).map gk := by
    apply (cancel_mono (K.cohomologyIso i).hom).1
    dsimp only [baseLocalizationCohomologyMap]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).map gk ≫
        (K.cohomologyIso i).hom = _ from K.cohomologyIso_smul i a]
    simp only [← Category.assoc]
    rw [show (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map gl ≫
        (L.cohomologyIso i).hom = _ from L.cohomologyIso_smul i a]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (L.cohomologyIso i).hom ≫ H.map (L.derived.map ar) ≫
      H.map (L.derived.map v) ≫ H.map (η.app _) =
        (L.cohomologyIso i).hom ≫ H.map (L.derived.map v) ≫ H.map (η.app _) ≫
          H.map (K.derived.map ap)
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (L.cohomologyIso i).hom ≫ H.map t) hd
  exact congrArg (fun t ↦ t x) hb

end RingTensorCohomology
