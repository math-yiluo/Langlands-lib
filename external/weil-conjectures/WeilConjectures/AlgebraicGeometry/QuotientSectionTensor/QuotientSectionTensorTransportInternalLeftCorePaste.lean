/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! The categorical paste for internal-left scalar tensor transport.

## References

* Stacks Project, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

attribute [local irreducible] ModuleRingedComparison.tensor tensorComparison qTensor
  totalComparison totalScalar QuotientChange.compute Mod.extendScalars
  CondensedRing.internalScalarMonoidal Mod.monoidalCategoryStruct
  Localization.Monoidal.tensorBifunctor
  HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

private theorem paste_output_computation {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H J K : 𝒞}
    {l : A ⟶ B} {q : B ⟶ C}
    {a : A ⟶ D} {b : D ⟶ E} {c : E ⟶ F} {d : F ⟶ G} {e : G ⟶ B}
    {g : G ⟶ H} {h : H ⟶ C} {i : F ⟶ K} {j : K ⟶ J} {k : J ⟶ H}
    {v : D ⟶ K} {w : K ⟶ F} {r : A ⟶ J}
    (hl : l = a ≫ b ≫ c ≫ d ≫ e) (hq : e ≫ q = g ≫ h)
    (hn : d ≫ g = i ≫ j ≫ k) (ht : v ≫ w = b ≫ c)
    (hw : w ≫ i = 𝟙 K) (hr : a ≫ v ≫ j = r) :
    l ≫ q = r ≫ k ≫ h := by
  rw [hl]
  simp only [Category.assoc]
  rw [hq, reassoc_of% hn, ← reassoc_of% ht, reassoc_of% hw, reassoc_of% hr]

-- Prove the categorical identities before instantiating the large derived-category expressions.
private theorem paste_cancel_pair_inv {𝒜 ℬ 𝒞 : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞]
    (B : 𝒜 × ℬ ⥤ 𝒞) {X X' : 𝒜} {Y Y' : ℬ} (e : X ≅ X') (f : Y ≅ Y')
    {A D E H : 𝒞} {a : A ⟶ D} {b : D ⟶ E} {c : E ⟶ B.obj (X', Y')}
    {l : A ⟶ H} {m : H ⟶ B.obj (X, Y)}
    (h : l ≫ m = a ≫ b ≫ c ≫ B.map (Prod.mkHom e.inv f.inv)) :
    a ≫ b ≫ c = l ≫ m ≫ B.map (Prod.mkHom e.hom f.hom) := by
  rw [reassoc_of% h]
  simp only [← B.map_comp, prod_comp, Iso.inv_hom_id, ← prod_id,
    B.map_id, Category.comp_id]

private theorem paste_map_pair_three {𝒜 ℬ 𝒞 : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞]
    (B : 𝒜 × ℬ ⥤ 𝒞) {x₀ x₁ x₂ x₃ y₁ y₂ : 𝒜}
    {z₀ z₁ z₂ z₃ w₁ w₂ : ℬ}
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃}
    {d : x₀ ⟶ y₁} {e : y₁ ⟶ y₂} {f : y₂ ⟶ x₃}
    {a' : z₀ ⟶ z₁} {b' : z₁ ⟶ z₂} {c' : z₂ ⟶ z₃}
    {d' : z₀ ⟶ w₁} {e' : w₁ ⟶ w₂} {f' : w₂ ⟶ z₃}
    (h₁ : a ≫ b ≫ c = d ≫ e ≫ f) (h₂ : a' ≫ b' ≫ c' = d' ≫ e' ≫ f') :
    B.map (Prod.mkHom a a') ≫ B.map (Prod.mkHom b b') ≫ B.map (Prod.mkHom c c') =
      B.map (Prod.mkHom d d') ≫ B.map (Prod.mkHom e e') ≫ B.map (Prod.mkHom f f') := by
  simp only [← B.map_comp, prod_comp]
  exact congrArg B.map (congrArg₂ Prod.mkHom h₁ h₂)

private theorem paste_input_computation {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H I J K : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {t : C ⟶ D} {n' : D ⟶ E} {r : E ⟶ F}
    {n : C ⟶ G} {s : G ⟶ E} {d : A ⟶ H} {e : H ⟶ I} {f : I ⟶ G}
    {g : I ⟶ J} {h : J ⟶ K} {i : K ⟶ F}
    (hn : t ≫ n' = n ≫ s) (hs : a ≫ b ≫ n = d ≫ e ≫ f)
    (hp : f ≫ s ≫ r = g ≫ h ≫ i) :
    ((a ≫ b ≫ t) ≫ n') ≫ r = d ≫ e ≫ g ≫ h ≫ i := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hs, hp]

private theorem paste_cancel_pair_hom {𝒜 ℬ 𝒞 : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞]
    (B : 𝒜 × ℬ ⥤ 𝒞) {X X' : 𝒜} {Y Y' : ℬ} (e : X ≅ X') (f : Y ≅ Y')
    {Z : 𝒞} {q : B.obj (X', Y') ⟶ Z} {r : B.obj (X, Y) ⟶ Z}
    (h : q = B.map (Prod.mkHom e.inv f.inv) ≫ r) :
    B.map (Prod.mkHom e.hom f.hom) ≫ q = r := by
  rw [h, ← B.map_comp_assoc]
  simp only [prod_comp, Iso.hom_inv_id, ← prod_id, B.map_id, Category.id_comp]

private theorem paste_map_three {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) {A B C D : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : A ⟶ D}
    (h : a ≫ b ≫ c = d) : F.map a ≫ F.map b ≫ F.map c = F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

-- Preserve the existing binder names for the three inputs unused by this output-side proof.
set_option linter.unusedVariables false in
/--
The algebraic paste for internal-left scalar tensor transport, given the three normalization
equations as hypotheses.
-/
 theorem section_tensor_transport_internal_left_paste (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : TensorSectionCondition a T c b barB)
    (P Q : CochainComplex (Modules Λ T) ℤ)
    (hbn :
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj P)
              (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫ DerivedCategory.Q.map (totalScalar a T P Q))
    (hcn :
      c.derived.hom.app (DerivedCategory.Q.obj (P ⊗ Q)) ≫
          c.model.T.map (sectionLocalizationComparison Λ T (P ⊗ Q)).hom ≫
            c.model.ε.app
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q)) =
        (derivedFunctor Λ' T).map (compute a T (P ⊗ Q)) ≫
          (sectionLocalizationComparison Λ' T
            (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q))).hom ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app (P ⊗ Q)))
    (hqnorm :
      (qTensor Λ T).app
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P,
            ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q) =
        (tensor Λ T).map
            (Prod.mkHom (sectionLocalizationComparison Λ T P).inv
              (sectionLocalizationComparison Λ T Q).inv) ≫
          (tensorComparison Λ T).inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (derivedEquivalence Λ T).functor.map ((internalLocalizationTensorMap Λ T).app (P, Q)) ≫
          localizedTotalComparison Λ T P Q) :
    (scalarTensorSectionInput a T c P Q ≫
        barB.hom.app
          (DerivedCategory.Q.obj
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
          (tensor Λ' T).map
            (Prod.mkHom
              (c.model.ε.app (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P))
              (c.model.ε.app (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
          (qTensor Λ' T).app
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
                (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj
                (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) =
      scalarTensorSectionPath a T c P Q := by
  -- This output-side paste uses hc on P and Q, and the supplied tensor equation hbn.
  clear hb hcn hqnorm
  let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
  let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
  let P' := ((extension a T).mapHomologicalComplex (.up ℤ)).obj P
  let Q' := ((extension a T).mapHomologicalComplex (.up ℤ)).obj Q
  let F := (derivedEquivalence Λ' T).functor
  let B := tensor Λ' T
  let sP := sectionLocalizationComparison Λ T P
  let sQ := sectionLocalizationComparison Λ T Q
  let tP := sectionLocalizationComparison Λ' T P'
  let tQ := sectionLocalizationComparison Λ' T Q'
  let oP :
      ((equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)).obj P' ⟶
        (c.model.E.mapHomologicalComplex (.up ℤ)).obj EP :=
    (NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app P
  let oQ :
      ((equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)).obj Q' ⟶
        (c.model.E.mapHomologicalComplex (.up ℤ)).obj EQ :=
    (NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app Q
  have hn := barB.hom.naturality (Prod.mkHom sP.hom sQ.hom)
  simp only [Functor.comp_map, Functor.prod_map] at hn
  have hb' := hbarB (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
  have hstart :
      c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
          c.model.T.map ((tensorComparison Λ T).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          barB.hom.app ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P),
            (derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q)) =
        F.map (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          (tensorComparison Λ' T).hom.app
            ((D a T).obj (DerivedCategory.Q.obj P), (D a T).obj (DerivedCategory.Q.obj Q)) ≫
          B.map (Prod.mkHom (c.derived.hom.app (DerivedCategory.Q.obj P))
            (c.derived.hom.app (DerivedCategory.Q.obj Q))) := by
    exact paste_cancel_pair_inv B (c.derived.app (DerivedCategory.Q.obj P))
      (c.derived.app (DerivedCategory.Q.obj Q)) hb'
  have hP := section_scalar_normalization a T c hc P
  have hQ := section_scalar_normalization a T c hc Q
  have hpair :
      B.map (Prod.mkHom (c.derived.hom.app (DerivedCategory.Q.obj P))
          (c.derived.hom.app (DerivedCategory.Q.obj Q))) ≫
        B.map (Prod.mkHom (c.model.T.map sP.hom) (c.model.T.map sQ.hom)) ≫
        B.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) =
      B.map (Prod.mkHom (F.map (compute a T P)) (F.map (compute a T Q))) ≫
        B.map (Prod.mkHom tP.hom tQ.hom) ≫
        B.map (Prod.mkHom (DerivedCategory.Q.map oP) (DerivedCategory.Q.map oQ)) := by
    exact paste_map_pair_three B hP hQ
  have hinput :
      (scalarTensorSectionInput a T c P Q ≫
        barB.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ)) ≫
          B.map (Prod.mkHom (c.model.ε.app EP) (c.model.ε.app EQ)) =
      F.map (b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (tensorComparison Λ' T).hom.app
          ((D a T).obj (DerivedCategory.Q.obj P), (D a T).obj (DerivedCategory.Q.obj Q)) ≫
        B.map (Prod.mkHom (F.map (compute a T P)) (F.map (compute a T Q))) ≫
        B.map (Prod.mkHom tP.hom tQ.hom) ≫
        B.map (Prod.mkHom (DerivedCategory.Q.map oP) (DerivedCategory.Q.map oQ)) := by
    exact paste_input_computation hn hstart hpair
  have hqo := (qTensor Λ' T).naturality (Prod.mkHom oP oQ)
  simp only [Functor.comp_map, Functor.prod_map] at hqo
  have hqout := (section_derived_tensor_normalization
    (Λ := Λ') (X := T) (Y := T) (f := 𝟙 T)).1 T |>.1 P' Q'
  simp only [internalLocalizationTensorMap_app] at hqout
  have hq :
      B.map (Prod.mkHom tP.hom tQ.hom) ≫
        (qTensor Λ' T).app
          (((equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)).obj P',
            ((equivalence Λ' T).functor.mapHomologicalComplex (.up ℤ)).obj Q') =
      (tensorComparison Λ' T).inv.app (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q') ≫
        F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P' Q') ≫
        localizedTotalComparison Λ' T P' Q' := by
    exact paste_cancel_pair_hom B tP tQ hqout
  have htc := (tensorComparison Λ' T).hom.naturality
    (Prod.mkHom (compute a T P) (compute a T Q))
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    CondensedRing.derivedTensor, curriedTensor_obj_map, curriedTensor_map_app,
    ← MonoidalCategory.tensorHom_def] at htc
  have hpath : scalarTensorSectionPath a T c P Q =
      F.map ((D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        compute a T (P ⊗ Q) ≫ DerivedCategory.Q.map (totalScalar a T P Q)) ≫
      localizedTotalComparison Λ' T P' Q' ≫
      DerivedCategory.Q.map ((totalTensor Λ' T).map (Prod.mkHom oP oQ)) := by
    dsimp only [scalarTensorSectionPath, Functor.mapHomologicalComplexCompIso,
      Iso.trans_hom, Iso.symm_hom, NatIso.mapHomologicalComplex,
      Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app]
    simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.comp_id]
    rfl
  have hbn' := paste_map_three F hbn
  have hpaste := paste_output_computation hinput hqo hq htc
    ((tensorComparison Λ' T).hom_inv_id_app
      (DerivedCategory.Q.obj P', DerivedCategory.Q.obj Q')) hbn'
  exact (Category.assoc _ _ _).symm.trans (hpaste.trans hpath.symm)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
