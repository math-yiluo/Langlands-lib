/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
/-! # Naturality for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-naturality). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

-- Preserve the existing scalar-tower parameters even though the proof needs fewer.
set_option linter.unusedSectionVars false in
include tRB tAD tBD tApD tBpD tBBpD in
/-- Naturality of the characterized coefficient map on arbitrary models.
Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-second-localization-naturality).

Proof: leftDerived_ext applied to the target model K' proves that the derived
lift for L followed by epsilon equals delta extended to Bp followed by the
lift for L'. Their composites with K'.counit agree by the two given counit
compatibilities and naturality of the ordinary associator. Naturality of each
derived lift with respect to the image of f gives the full commuting derived
square. Apply homology and naturality of flatDerivedHomologyIso, then conjugate
by cohomologyIso. The characterizations of g and h give equality of the
underlying B-linear maps. On a generator 1 tensor x the two formulas he and he'
and ExtendScalars.map_tmul identify the D-linear composites with this equality.
ExtendScalars.hom_ext proves equality of the maps. This works for arbitrary
flat B to Bp and uses no localization or flatness of D. Zero maps, identity
maps and zero rings obey the same equations. -/
theorem secondLocalization_naturality (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L'.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K'.cohomology i))
    (he : IsSecondLocalizationMap R A B Bp D hflat Q L K i e.hom)
    (he' : IsSecondLocalizationMap R A B Bp D hflat Q' L' K' i e'.hom) :
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
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            e'.hom =
          e.hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).map h := by
  intro hδ hg hε hh
  have hb :
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
        secondLocalizationCohomologyMap R A B Bp D hflat Q' L' K' i =
      secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
        (ModuleCat.restrictScalars.{u}
          (algebraMap B Bp)).map ((ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map h) := by
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    let E := ModuleCat.extendScalars.{u} (algebraMap B Bp)
    let T := E.mapDerivedCategory
    let η := secondLocalizationDerivedMap R A B Bp D hflat Q L K
    let η' := secondLocalizationDerivedMap R A B Bp D hflat Q' L' K'
    let := K.universal
    let := K'.universal
    let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
    have hc : Functor.whiskerRight δ T ≫ η' = η ≫ ε := by
      apply Functor.leftDerived_ext K'.derived K'.counit W
      simp only [Functor.whiskerLeft_comp, Category.assoc]
      rw [hε]
      change Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight δ T) ≫
          (Functor.whiskerLeft DerivedCategory.Qh η' ≫ K'.counit) =
        Functor.whiskerLeft DerivedCategory.Qh η ≫ K.counit
      dsimp only [η, η', secondLocalizationDerivedMap]
      rw [Functor.leftDerived_fac, Functor.leftDerived_fac]
      ext X
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.comp_obj]
      have hd := congrArg (fun t ↦ t.app X) hδ
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hd
      dsimp only [T]
      rw [← Category.assoc, ← E.mapDerivedCategory.map_comp, hd]
    let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
    let a := V.map ((restrict R A).map f)
    have hd : T.map (L.derived.map a) ≫ T.map (δ.app _) ≫ η'.app _ =
        η.app _ ≫ K.derived.map a ≫ ε.app _ := by
      rw [← η.naturality_assoc a]
      exact congrArg (fun t ↦ T.map (L.derived.map a) ≫ t.app _) hc
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
    let φ := flatDerivedHomologyIso B Bp hflat i
    dsimp only [secondLocalizationCohomologyMap]
    apply (ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv_naturality_left_square
    apply (cancel_mono (K'.cohomologyIso i).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hh]
    simp only [← Category.assoc]
    rw [← E.map_comp, hg]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    change E.map (L.cohomologyIso i).hom ≫ E.map (H.map (L.derived.map a)) ≫
        E.map (H.map (δ.app _)) ≫ φ.inv.app _ ≫ Hp.map (η'.app _) =
      E.map (L.cohomologyIso i).hom ≫ φ.inv.app _ ≫ Hp.map (η.app _) ≫
        Hp.map (K.derived.map a) ≫ Hp.map (ε.app _)
    have hnδ := φ.inv.naturality (δ.app (V.obj ((restrict R A).obj Q')))
    have hna := φ.inv.naturality (L.derived.map a)
    dsimp only [Functor.comp_map] at hnδ hna
    rw [reassoc_of% hnδ, reassoc_of% hna]
    simpa only [T, E, Hp, V, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ E.map (L.cohomologyIso i).hom ≫ φ.inv.app _ ≫ Hp.map t) hd
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change e'.hom ((ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x)) =
    (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).map h
      (e.hom ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))
  rw [ModuleCat.ExtendScalars.map_tmul, he', he, ModuleCat.ExtendScalars.map_tmul]
  exact congrArg (fun y ↦ (1 : D) ⊗ₜ[A ⊗[R] Bp,algebraMap (A ⊗[R] Bp) D] y)
    (congrArg (fun t ↦ t x) hb)

end RingTensorCohomology
