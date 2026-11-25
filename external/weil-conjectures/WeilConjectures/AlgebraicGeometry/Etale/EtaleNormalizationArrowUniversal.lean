/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import all WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import WeilConjectures.CategoryTheory.Constant.ConstantDerivedNormalizationUniversalSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Sourcewise universality for constant normalization arrows

Source: Stacks Project, Tags 06YY and 03ED.
(blueprint: lem-weil-pbc-etale-constant-arrow-universal-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
section ConstantSlice
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
    (J : GrothendieckTopology C) (U : C)
    {R S : Type (t + 1)} [CommRing R] [CommRing S]

private theorem constantCoefficient_unit (q : R →+* S) (N : ModuleCat.{t + 1} S)
    (V : Cᵒᵖ) :
    (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q).map
        ((toSheafify J ((Functor.const Cᵒᵖ).obj N)).app V) ≫
      ((constantCommuteCompose J
        (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).hom.app N).hom.app V =
    (toSheafify J ((Functor.const Cᵒᵖ).obj
      ((ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q).obj N))).app V := by
  have h := sheafComposeIso_inv_fac J (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)
    ((Functor.const Cᵒᵖ).obj N)
  have hn := toSheafify_naturality J (Functor.constComp Cᵒᵖ N
    (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).hom
  rw [constantCommuteCompose_hom_app_hom]
  simp only [NatTrans.comp_app]
  rw [← Category.assoc]
  have hv := congr_app h V
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hv
  rw [hv]
  simpa only [NatTrans.comp_app, Functor.constComp_hom_app, Category.id_comp] using
    (congr_app hn V).symm

private def constantSliceIso (A : Type (t + 1)) [CommRing A] :
    constantSheaf (J.over U) (ModuleCat.{t + 1} A) ≅
      constantSheaf J (ModuleCat.{t + 1} A) ⋙ J.overPullback (ModuleCat.{t + 1} A) U :=
  NatIso.ofComponents (fun N ↦ constantSheafOverIso J (ModuleCat.{t + 1} A) U N) (by
    intro M N f
    apply ((constantSheafAdj (J.over U) (ModuleCat.{t + 1} A)
      Over.mkIdTerminal).homEquiv M _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [constantSheafOverIso, asIso_hom]
    dsimp only [Functor.comp_obj]
    rw [constantSheafAdj_homEquiv_constantSheafOverHom,
      constantSheafAdj_homEquiv_constantSheafOverHom]
    exact congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) (op U))

private theorem constantSlice_coefficients (q : R →+* S) (N : ModuleCat.{t + 1} S) :
    (sheafCompose (J.over U) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).map
        ((constantSliceIso J U S).hom.app N) ≫
      (J.overPullback (ModuleCat.{t + 1} R) U).map
        ((constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).hom.app N) =
    (constantCommuteCompose (J.over U)
      (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)).hom.app N ≫
      (constantSliceIso J U R).hom.app
        ((ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q).obj N) := by
  let r := ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q
  apply (cancel_epi ((constantCommuteCompose (J.over U) r).inv.app N)).mp
  simp only [r, Iso.inv_hom_id_app_assoc]
  apply ((constantSheafAdj (J.over U) (ModuleCat.{t + 1} R)
    Over.mkIdTerminal).homEquiv (r.obj N) _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  have hu := constantCoefficient_unit (J.over U) q N (op (Over.mk (𝟙 U)))
  have hv :
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj (r.obj N))).app
          (op (Over.mk (𝟙 U))) ≫
        ((constantCommuteCompose (J.over U) r).inv.app N).hom.app
          (op (Over.mk (𝟙 U))) =
      r.map ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj N)).app
        (op (Over.mk (𝟙 U)))) := by
    rw [← hu, Category.assoc]
    dsimp only [r]
    simp only [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    erw [Category.comp_id]
  rw [hv]
  have hc := congr_app (toSheafify_constantSheafOverHom_hom J
    (ModuleCat.{t + 1} S) U N) (op (Over.mk (𝟙 U)))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  have hcR := congr_app (toSheafify_constantSheafOverHom_hom J
    (ModuleCat.{t + 1} R) U (r.obj N)) (op (Over.mk (𝟙 U)))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hcR
  change r.map _ ≫ (r.map _ ≫ _) = _
  rw [← Category.assoc, ← r.map_comp]
  dsimp only [constantSliceIso, NatIso.ofComponents_hom_app, constantSheafOverIso,
    asIso_hom, ObjectProperty.ι_map]
  rw [hc, hcR]
  exact constantCoefficient_unit J q N (op U)

private def constantDerivedSliceIso (A : Type (t + 1)) [CommRing A] :
    normalizationConstant (R := A) (J.over U) ≅
      normalizationConstant (R := A) J ⋙ derivedSliceRestriction J A U :=
  Functor.mapDerivedCategoryTriangleIso (constantSliceIso J U A)

private theorem constantDerivedSlice_coefficients (q : R →+* S)
    (N : DerivedCategory (ModuleCat.{t + 1} S)) :
    (constantDerivedSliceIso J U R).hom.app ((normalizationModuleRestrict q).obj N) ≫
        (derivedSliceRestriction J R U).map ((normalizationConstantRestrict J q).inv.app N) ≫
        (sliceRestrictScalarsIso J R q U).inv.app ((normalizationConstant J).obj N) =
      (normalizationConstantRestrict (J.over U) q).inv.app N ≫
        (normalizationRestrict (J.over U) q).map ((constantDerivedSliceIso J U S).hom.app N) := by
  have hd := Functor.exactSquare_comp_forward
    (constantSheaf J (ModuleCat.{t + 1} S)) (J.overPullback (ModuleCat.{t + 1} S) U)
    (constantSheaf (J.over U) (ModuleCat.{t + 1} S))
    (constantSheaf J (ModuleCat.{t + 1} R)) (J.overPullback (ModuleCat.{t + 1} R) U)
    (constantSheaf (J.over U) (ModuleCat.{t + 1} R))
    (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q)
    (sheafCompose J (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
    (sheafCompose (J.over U) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
    (constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
    (sliceRestrictScalarsSheafIso J R q U)
    (constantCommuteCompose (J.over U) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q))
    (constantSliceIso J U S) (constantSliceIso J U R)
    (fun M ↦ by
      dsimp only [sliceRestrictScalarsSheafIso, NatIso.ofComponents_hom_app, Iso.refl_hom]
      erw [Category.id_comp]
      exact constantSlice_coefficients J U q M) N
  change
    (normalizationRestrict (J.over U) q).map ((constantDerivedSliceIso J U S).hom.app N) ≫
        (sliceRestrictScalarsIso J R q U).hom.app ((normalizationConstant J).obj N) ≫
        (derivedSliceRestriction J R U).map ((normalizationConstantRestrict J q).hom.app N) =
      (normalizationConstantRestrict (J.over U) q).hom.app N ≫
        (constantDerivedSliceIso J U R).hom.app ((normalizationModuleRestrict q).obj N) at hd
  exact (Functor.square_reverse (derivedSliceRestriction J R U)
    ((normalizationConstantRestrict (J.over U) q).app N)
    ((sliceRestrictScalarsIso J R q U).app ((normalizationConstant J).obj N))
    ((normalizationConstantRestrict J q).app N)
    ((normalizationRestrict (J.over U) q).map ((constantDerivedSliceIso J U S).hom.app N))
    ((constantDerivedSliceIso J U R).hom.app ((normalizationModuleRestrict q).obj N)) hd).symm

private theorem constantDerivedSlice_arrow (q : R →+* S)
    {E : DerivedCategory (ModuleCat.{t + 1} R)}
    {E' : DerivedCategory (ModuleCat.{t + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E') :
    (constantDerivedSliceIso J U R).hom.app E ≫
        ((derivedSliceRestriction J R U).map (normalizationConstantArrow J q d) ≫
          (sliceRestrictScalarsIso J R q U).inv.app ((normalizationConstant J).obj E')) =
      normalizationConstantArrow (J.over U) q d ≫
        (normalizationRestrict (J.over U) q).map
          ((constantDerivedSliceIso J U S).hom.app E') := by
  have hn := (constantDerivedSliceIso J U R).hom.naturality d
  dsimp only [Functor.comp_map] at hn
  dsimp only [normalizationConstantArrow]
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [constantDerivedSlice_coefficients J U q E']

private theorem constantDerivedSlice_universal (q : R →+* S)
    {E : DerivedCategory (ModuleCat.{t + 1} R)}
    {E' : DerivedCategory (ModuleCat.{t + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E')
    (h : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d))) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (T := normalizationRestrict (J.over U) q)
      ((derivedSliceRestriction J R U).map (normalizationConstantArrow J q d) ≫
        (sliceRestrictScalarsIso J R q U).inv.app ((normalizationConstant J).obj E')))) := by
  obtain ⟨hc⟩ := normalizationConstantArrow_isUniversal (J.over U) q d h
  let T := StructuredArrow.map₂
    (R := normalizationRestrict (J.over U) q) (R' := normalizationRestrict (J.over U) q)
    (F := 𝟭 _) (G := 𝟭 _) ((constantDerivedSliceIso J U R).inv.app E) (𝟙 _)
  have hi := hc.isInitialObj T _
  refine ⟨hi.ofIso (StructuredArrow.isoMk
    (f := T.obj (StructuredArrow.mk (normalizationConstantArrow (J.over U) q d)))
    (f' := StructuredArrow.mk (T := normalizationRestrict (J.over U) q)
      ((derivedSliceRestriction J R U).map (normalizationConstantArrow J q d) ≫
        (sliceRestrictScalarsIso J R q U).inv.app ((normalizationConstant J).obj E')))
    ((constantDerivedSliceIso J U S).app E') ?_)⟩
  change ((constantDerivedSliceIso J U R).inv.app E ≫
      normalizationConstantArrow (J.over U) q d ≫ 𝟙 _) ≫
      (normalizationRestrict (J.over U) q).map
        ((constantDerivedSliceIso J U S).hom.app E') = _
  rw [Category.comp_id, Category.assoc, ← constantDerivedSlice_arrow J U q d,
    Iso.inv_hom_id_app_assoc]
  rfl

end ConstantSlice
end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A universal constant coefficient arrow remains universal after restriction to an
etale source and transport through the canonical coefficient mate.

Source: Stacks Project, Tags 06YY and 03ED.
(blueprint: lem-weil-pbc-etale-constant-arrow-universal-transport).

The proof transports the initial structured arrow along the exact slice equivalence
and the coefficient mate. The mate is invertible by the inverse-image scalar
comparison, and the source and target constants are identified by the localization
comparison. Initial objects are preserved by these isomorphisms.
-/
theorem etaleNormalizationArrow_universal_of_constant
    (Y : Scheme.{t}) {R S : Type (t + 1)} [CommRing R] [CommRing S]
    (q : R →+* S)
    {E : DerivedCategory (ModuleCat.{t + 1} R)}
    {E' : DerivedCategory (ModuleCat.{t + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E')
    (h : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d)))
    (U : Y.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Y q
        (normalizationConstantArrow Y.smallEtaleTopology q d) U))) := by
  let C := (normalizationConstant Y.smallEtaleTopology).obj E
  let C' := (normalizationConstant Y.smallEtaleTopology).obj E'
  obtain ⟨hs⟩ := CategoryTheory.constantDerivedSlice_universal Y.smallEtaleTopology U q d h
  let T := StructuredArrow.map₂
    (R := normalizationRestrict (Y.smallEtaleTopology.over U) q)
    (R' := normalizationRestrict U.left.smallEtaleTopology q)
    (F := (etaleDerivedSliceEquivalence Y S U).functor)
    (G := (etaleDerivedSliceEquivalence Y R U).functor)
    ((etaleDerivedSliceRestrictionIso Y R U).inv.app C)
    (etaleDerivedSliceEquivalenceCoefficients Y U q).hom
  have hi := hs.isInitialObj T _
  refine ⟨hi.ofIso (StructuredArrow.isoMk
    (f := T.obj (StructuredArrow.mk
      (T := normalizationRestrict (Y.smallEtaleTopology.over U) q)
      ((derivedSliceRestriction Y.smallEtaleTopology R U).map
          (normalizationConstantArrow Y.smallEtaleTopology q d) ≫
        (sliceRestrictScalarsIso Y.smallEtaleTopology R q U).inv.app C')))
    (f' := StructuredArrow.mk (etaleIsomorphismNormalizationArrow Y q
      (normalizationConstantArrow Y.smallEtaleTopology q d) U))
    ((etaleDerivedSliceRestrictionIso Y S U).app C') ?_)⟩
  change
    (((etaleDerivedSliceRestrictionIso Y R U).inv.app C ≫
      (etaleDerivedSliceEquivalence Y R U).functor.map
        ((derivedSliceRestriction Y.smallEtaleTopology R U).map
            (normalizationConstantArrow Y.smallEtaleTopology q d) ≫
          (sliceRestrictScalarsIso Y.smallEtaleTopology R q U).inv.app C') ≫
      (etaleDerivedSliceEquivalenceCoefficients Y U q).hom.app
        ((derivedSliceRestriction Y.smallEtaleTopology S U).obj C')) ≫
      (normalizationRestrict U.left.smallEtaleTopology q).map
        ((etaleDerivedSliceRestrictionIso Y S U).hom.app C')) = _
  simp only [Category.assoc]
  rw [← etale_source_slice_normalization Y U q
    (normalizationConstantArrow Y.smallEtaleTopology q d), Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry.Scheme
