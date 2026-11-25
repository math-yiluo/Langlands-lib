/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
import WeilConjectures.Algebra.Homology.SecondLocalizationRawCounitSquare
/-! # Ordinary comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-B-square). -/

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
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include tRB in
/-- The B-linear ordinary counit square, before forgetting module structures.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-ordinary-B-square).

Proof: install the target model's universal left-derived-functor instance.
The defining leftDerivedLift factorization of secondLocalizationDerivedMap
identifies its composite with K.counit with L.counit extended to Bp and the
ordinary scalar-extension associator. Evaluate at the restriction of Q to R,
apply degree-i homology, and use the defining localization factorization of
flatDerivedHomologyIso to commute the flat extension with homology. Transpose
along extension/restriction of scalars B to Bp: the unit sends x to 1 tensor x.
Substitute the two comparison_eq identities and cancel the cohomologyIso maps.
The ordinary associator sends b tensor x to image(b) tensor x; the given hφ
identifies its transpose, conjugated by ordinaryIso, with φB, by tensor
induction after precomposing with L.ordinaryIso. Naturality of the homology
factorization maps and of mapHomologyIso for restriction to B completes the
B-linear identity below. This calculation uses no forgetful functor, no
localizedComparison, and no hypothesis on flatness of D. -/
theorem secondLocalization_ordinary_B_square (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (φB : ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).obj
          Q) ⟶
      ((ModuleCat.restrictScalars (algebraMap B Bp)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
          Bp →ₐ[R] A ⊗[R] Bp).toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex (.up
            ℤ)).obj Q)))
    (hφ : ∀ (j : ℤ) (b : B) (x : Q.X j),
      φB.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x)) :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)).inv ≫
      HomologicalComplex.homologyMap φB i =
    secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
      (ModuleCat.restrictScalars (algebraMap B Bp)).map
        ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map
            (K.comparison i) ≫
          (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
            (.up ℤ)).obj Q).sc i).mapHomologyIso
              (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom)).inv) ≫
      (((((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          Bp →ₐ[R] A ⊗[R] Bp).toRingHom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex (.up
              ℤ)).obj Q)).sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap B Bp))).inv
                := by
  let T := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj Q
  let P := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
    (.up ℤ)).obj T
  let Pp := ((ModuleCat.extendScalars (algebraMap R Bp)).mapHomologicalComplex
    (.up ℤ)).obj T
  let U := ModuleCat.restrictScalars (algebraMap B Bp)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let qR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let qBp := HomotopyCategory.quotient (ModuleCat.{u} Bp) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
  let X := DerivedCategory.Qh.obj (qR.obj T)
  let c := H.map (L.counit.app (qR.obj T)) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app (qB.obj P) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app P
  let cp := Hp.map (K.counit.app (qR.obj T)) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app (qBp.obj Pp) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app Pp
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let d := (flatDerivedHomologyIso B Bp hflat i).inv.app (L.derived.obj X) ≫
    Hp.map ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)
  let χ : P ⟶ UC.obj Pp :=
    L.ordinaryIso.hom ≫ φB ≫ UC.map K.ordinaryIso.inv
  have hχ : ∀ (j : ℤ) (b : B) (x : Q.X j),
      χ.f j (b ⊗ₜ[R,algebraMap R B] (show T.X j from x)) =
        algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] (show T.X j from x) := by
    intro j b x
    change K.ordinaryIso.inv.f j (φB.f j
      (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x))) = _
    rw [hφ]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f j) K.ordinaryIso.hom_inv_id) _
  have hraw : c ≫ HomologicalComplex.homologyMap χ i =
      adj.homEquiv _ _ (d ≫ cp) ≫ ((Pp.sc i).mapHomologyIso U).inv :=
    secondLocalization_raw_counit_square R A B Bp D hflat i Q L K χ hχ
  have hchain : χ ≫ UC.map K.ordinaryIso.hom = L.ordinaryIso.hom ≫ φB := by
    dsimp only [χ]
    rw [Category.assoc, Category.assoc, ← UC.map_comp, K.ordinaryIso.inv_hom_id,
      UC.map_id, Category.comp_id]
  have hn : U.map (HomologicalComplex.homologyMap K.ordinaryIso.hom i) ≫
      (((((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).mapHomologicalComplex
          (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
              (.up ℤ)).obj Q)).sc i).mapHomologyIso U).inv =
      ((Pp.sc i).mapHomologyIso U).inv ≫
        HomologicalComplex.homologyMap (UC.map K.ordinaryIso.hom) i := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map K.ordinaryIso.hom) U
  have hm : secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
      U.map ((K.cohomologyIso i).hom ≫ cp) =
      (L.cohomologyIso i).hom ≫ adj.homEquiv _ _ (d ≫ cp) := by
    change adj.homEquiv _ _
      ((ModuleCat.extendScalars (algebraMap B Bp)).map (L.cohomologyIso i).hom ≫
        d ≫ (K.cohomologyIso i).inv) ≫ U.map ((K.cohomologyIso i).hom ≫ cp) = _
    rw [← adj.homEquiv_naturality_right]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact adj.homEquiv_naturality_left (L.cohomologyIso i).hom (d ≫ cp)
  rw [reassoc_of% L.comparison_eq i, K.comparison_eq i]
  change (L.cohomologyIso i).hom ≫ c ≫
      HomologicalComplex.homologyMap L.ordinaryIso.hom i ≫
        HomologicalComplex.homologyMap φB i =
    secondLocalizationCohomologyMap R A B Bp D hflat Q L K i ≫
      U.map ((K.cohomologyIso i).hom ≫ cp ≫
        HomologicalComplex.homologyMap K.ordinaryIso.hom i) ≫ _
  rw [← HomologicalComplex.homologyMap_comp, ← hchain,
    HomologicalComplex.homologyMap_comp]
  rw [← Category.assoc (K.cohomologyIso i).hom, U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hm, hn, ← reassoc_of% hraw]

end RingTensorCohomology
