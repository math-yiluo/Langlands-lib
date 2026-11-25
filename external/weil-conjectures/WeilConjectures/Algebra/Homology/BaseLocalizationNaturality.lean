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
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-localization-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

/-- Naturality of the characterized base-localization map.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-base-localization-naturality).

Proof: write T for exact restriction from Rp to R on derived categories, and
eta and eta-prime for the universal lifts defining the two canonical maps.
The defining counit equations and the assumed counit compatibility of delta
and epsilon show that T whiskered with delta followed by eta-prime and eta
followed by epsilon have the same counit composite. Uniqueness of the
universal lift to Kprime therefore identifies these transformations.
The input isomorphism is a composite of restriction composition and the
homotopy and derived factorization isomorphisms. Naturality of each of these
three isomorphisms gives FR(f) followed by v-prime equals v followed by
T(FRp(f)). Apply L.derived, naturality of delta and eta, and the preceding
cocycle equation. This identifies the two composites of derived morphisms.
Apply degree-i B-linear homology and conjugate by the four cohomologyIso
isomorphisms. The given equations for g and h identify this equality with
naturality of baseLocalizationCohomologyMap. Finally evaluate the desired
D-linear equality on 1 tensor x. The generator equations he and he-prime,
and extendScalars.map_tmul, reduce it to that B-linear equality. The
extension-of-scalars hom_ext lemma proves equality on all elements. Zero
complexes, identity and zero chain maps, and zero D satisfy the same proof;
no invertibility of localizedComparison or flatness of D is used. -/
theorem baseLocalization_naturality (S : Submonoid R) [IsLocalization S Rp] (i : ℤ)
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
    (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
    (K' : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K.cohomology i))
    (e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L'.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj (K'.cohomology i))
    (he : IsBaseLocalizationMap R Rp B A D S Q L K i e.hom)
    (he' : IsBaseLocalizationMap R Rp B A D S Q' L' K' i e'.hom) :
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).map
                  ((restrict Rp A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
                  ((restrict Rp A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            e'.hom =
          e.hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).map h := by
  intro hδ hg hε hh
  let T := (ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategory
  let η := baseLocalizationDerivedMap R Rp B A D S Q L K
  let η' := baseLocalizationDerivedMap R Rp B A D S Q' L' K'
  let := K.universal
  let := K'.universal
  have hη : Functor.whiskerLeft DerivedCategory.Qh η ≫ K.counit =
      baseLocalizationCounit R Rp B A D S Q L := by
    exact Functor.leftDerived_fac K.derived K.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) _ _
  have hη' : Functor.whiskerLeft DerivedCategory.Qh η' ≫ K'.counit =
      baseLocalizationCounit R Rp B A D S Q' L' := by
    exact Functor.leftDerived_fac K'.derived K'.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) _ _
  have hc : Functor.whiskerLeft T δ ≫ η' = η ≫ ε := by
    apply Functor.leftDerived_ext K'.derived K'.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ))
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [hε]
    change Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerLeft T δ) ≫
        (Functor.whiskerLeft DerivedCategory.Qh η' ≫ K'.counit) =
      Functor.whiskerLeft DerivedCategory.Qh η ≫ K.counit
    rw [hη', hη]
    ext X
    dsimp only [baseLocalizationCounit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_obj]
    have hd := congrArg (fun t ↦ t.app
      (((ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapHomotopyCategory
        (.up ℤ)).obj X)) hδ
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hd
    dsimp only [T]
    simp only [Category.id_comp]
    rw [← δ.naturality_assoc]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ L.derived.map
        ((ModuleCat.restrictScalars.{u} (algebraMap R Rp)).mapDerivedCategoryFactorsh.hom.app X)
          ≫ k ≫ DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (baseLocalizationTensorIso R Rp B S)
              (.up ℤ)).hom.app X)) hd
  let FR := restrict R A ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
    DerivedCategory.Qh
  let FP := restrict Rp A ⋙ HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ) ⋙
    DerivedCategory.Qh
  let a := FR.map f
  let b := FP.map f
  let v := (baseLocalizationInputIso R Rp A Q).hom
  let v' := (baseLocalizationInputIso R Rp A Q').hom
  have hab : a ≫ v' = v ≫ T.map b :=
    (baseLocalizationInputNatIso R Rp A).hom.naturality f
  have hd : L.derived.map a ≫ δ.app _ ≫ L'.derived.map v' ≫ η'.app _ =
      L.derived.map v ≫ η.app _ ≫ K.derived.map b ≫ ε.app _ := by
    dsimp only [FR, FP, Functor.comp_obj]
    rw [← δ.naturality_assoc v']
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hab]
    simp only [Functor.map_comp, Category.assoc]
    have hn := η.naturality b
    dsimp only [FP, Functor.comp_obj, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    exact congrArg (fun t ↦ L.derived.map v ≫ L.derived.map (T.map b) ≫ t.app _) hc
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have hb :
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
          baseLocalizationCohomologyMap R Rp B A D S Q' L' K' i =
      baseLocalizationCohomologyMap R Rp B A D S Q L K i ≫
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).map h := by
    apply (cancel_mono (K'.cohomologyIso i).hom).1
    dsimp only [baseLocalizationCohomologyMap]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hh]
    simp only [← Category.assoc]
    rw [hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (L.cohomologyIso i).hom ≫ H.map (L.derived.map a) ≫ H.map (δ.app _) ≫
      H.map (L'.derived.map v') ≫ H.map (η'.app _) =
        (L.cohomologyIso i).hom ≫ H.map (L.derived.map v) ≫ H.map (η.app _) ≫
          H.map (K.derived.map b) ≫ H.map (ε.app _)
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (L.cohomologyIso i).hom ≫ H.map t) hd
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change e'.hom ((ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x)) =
    (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).map h
      (e.hom ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))
  rw [ModuleCat.ExtendScalars.map_tmul, he', he, ModuleCat.ExtendScalars.map_tmul]
  exact congrArg (fun y ↦ (1 : D) ⊗ₜ[A ⊗[Rp] B,algebraMap (A ⊗[Rp] B) D] y)
    (congrArg (fun t ↦ t x) hb)

end RingTensorCohomology
