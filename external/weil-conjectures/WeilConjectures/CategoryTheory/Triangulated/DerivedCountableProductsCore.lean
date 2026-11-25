/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact limits commute with homology of short complexes. -/
private theorem shortComplexHomologyLimit
    (A : Type u) [Category.{v} A] [Abelian A]
    (J : Type*) [SmallCategory J] [HasLimitsOfShape J A]
    [HasExactLimitsOfShape J A] :
    PreservesLimitsOfShape J (ShortComplex.homologyFunctor A) := by
  let L := lim (J := J) (C := A)
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence J A).inverse.obj D
  let c : Cone D :=
    { pt := S.map L
      π :=
        { app := fun j ↦ S.mapNatTrans (lim.π j)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using (limit.w (D ⋙ ShortComplex.π₁) f).symm
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using (limit.w (D ⋙ ShortComplex.π₂) f).symm
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using (limit.w (D ⋙ ShortComplex.π₃) f).symm } }
  have hc : IsLimit c := ShortComplex.isLimitOfIsLimitπ c
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)
  apply preservesLimit_of_preserves_limit_cone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun j ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj j))
      (by
        intro i j f
        change ShortComplex.homologyMap
          (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
        rw [ShortComplex.homologyMap_mapNatTrans]
        simp)
  have h : IsLimit ((Cone.postcompose e.inv).obj (limit.cone S.homology)) :=
    (IsLimit.postcomposeHomEquiv e.symm _).symm (limit.isLimit _)
  apply IsLimit.ofIsoLimit h
  refine Cone.ext (S.mapHomologyIso L).symm ?_
  intro j
  dsimp only [Functor.mapCone, c, Cone.postcompose, limit.cone,
    Cone.functoriality, NatTrans.comp_app, Iso.symm_hom, ShortComplex.homologyFunctor_map]
  change limit.π S.homology j ≫ e.inv.app j =
    (S.mapHomologyIso L).inv ≫ ShortComplex.homologyMap (S.mapNatTrans (lim.π j))
  rw [ShortComplex.homologyMap_mapNatTrans]
  dsimp [e, L]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Reduce complex homology to its three terms. -/
private theorem complexHomologyLimit
    (A : Type u) [Category.{v} A] [Abelian A]
    (J : Type*) [SmallCategory J] [HasLimitsOfShape J A]
    [HasExactLimitsOfShape J A] (p : ℤ) :
    PreservesLimitsOfShape J
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) p) := by
  let H := HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) p
  have : PreservesLimitsOfShape J H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isLimitOfIsLimitπ (H.mapCone c)
      (isLimitOfPreserves
        (HomologicalComplex.eval A (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p)) hc)
      (isLimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) p) hc)
      (isLimitOfPreserves
        (HomologicalComplex.eval A (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next p)) hc)⟩⟩⟩
  have := shortComplexHomologyLimit A J
  change PreservesLimitsOfShape J (H ⋙ ShortComplex.homologyFunctor A)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Descend product preservation through an essentially surjective functor. -/
private theorem preservesProductsOfEssSurj
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {A : Type u} [Category.{v} A] (J : Type*) [HasProductsOfShape J C]
    (Q : C ⥤ D) [Q.EssSurj] (H : D ⥤ A)
    (hQ : ∀ K : J → C,
      Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor K)))))
    [PreservesLimitsOfShape (Discrete J) (Q ⋙ H)] :
    PreservesLimitsOfShape (Discrete J) H := by
  classical
  have h (E : J → D) : PreservesLimit (Discrete.functor E) H := by
    let K := fun j ↦ Q.objPreimage (E j)
    let e : Discrete.functor K ⋙ Q ≅ Discrete.functor E :=
      Discrete.natIso (fun j ↦ Q.objObjPreimageIso (E j.as))
    have : PreservesLimit (Discrete.functor K ⋙ Q) H :=
      preservesLimit_of_preserves_limit_cone (hQ K).some
        (isLimitOfPreserves (Q ⋙ H) (limit.isLimit (Discrete.functor K)))
    exact preservesLimit_of_iso_diagram H e
  let := h
  exact preservesLimitsOfShape_of_discrete H

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A localization with both calculi of fractions preserves products when its
inverted morphisms are stable under those products. -/
private theorem localizationPreservesProducts
    {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    (J : Type*) [HasProductsOfShape J C]
    (L : C ⥤ D) [L.Additive] (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [W.IsStableUnderProductsOfShape J] : PreservesLimitsOfShape (Discrete J) L := by
  classical
  have := Localization.essSurj L W
  have hz (K : J → C) (X : C) (a : X ⟶ ∏ᶜ K)
      (ha : ∀ j, L.map a ≫ L.map (Pi.π K j) = 0) : L.map a = 0 := by
    have h (j : J) : ∃ (Y : C) (s : K j ⟶ Y) (_ : W s), (a ≫ Pi.π K j) ≫ s = 0 := by
      have h := ha j
      rw [← L.map_comp, ← L.map_zero] at h
      obtain ⟨Y, s, hs, h⟩ := (MorphismProperty.map_eq_iff_postcomp L W _ _).mp h
      exact ⟨Y, s, hs, by simpa using h⟩
    choose Y s hs h using h
    have hWs : W (Limits.Pi.map s) :=
      W.limMap (Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor Y)
        (fun j ↦ s j.as)) (fun j ↦ hs j.as)
    have : IsIso (L.map (Limits.Pi.map s)) := Localization.inverts L W _ hWs
    apply (cancel_mono (L.map (Limits.Pi.map s))).1
    rw [← L.map_comp]
    have he : a ≫ Limits.Pi.map s = 0 := by
      ext j
      simpa using h j
    simp [he]
  have hzero (K : J → C) (X : C) (a : L.obj X ⟶ L.obj (∏ᶜ K))
      (ha : ∀ j, a ≫ L.map (Pi.π K j) = 0) : a = 0 := by
    obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction L W a
    have hφ (j : J) : L.map φ.f ≫ L.map (Pi.π K j) = 0 := by
      have := Localization.inverts L W φ.s φ.hs
      have h := ha j
      dsimp [MorphismProperty.RightFraction.map] at h
      simpa only [← cancel_epi (L.map φ.s), Category.assoc,
        IsIso.hom_inv_id_assoc, comp_zero] using h
    have := hz K φ.X' φ.f hφ
    simp [MorphismProperty.RightFraction.map, this]
  have hp (K : J → C) :
      Nonempty (IsLimit (L.mapCone (limit.cone (Discrete.functor K)))) := by
    have hex (s : Fan (fun j ↦ L.obj (K j))) :
        ∃ (a : s.pt ⟶ L.obj (∏ᶜ K)), ∀ j, a ≫ L.map (Pi.π K j) = s.proj j := by
      let e := L.objObjPreimageIso s.pt
      have h (j : J) := Localization.exists_leftFraction L W (e.hom ≫ s.proj j)
      choose φ hφ using h
      let g := Pi.lift (fun j ↦ (φ j).f)
      let r := Limits.Pi.map (fun j ↦ (φ j).s)
      have hr : W r :=
        W.limMap (Discrete.natTrans (F := Discrete.functor K)
          (G := Discrete.functor (fun j ↦ (φ j).Y')) (fun j ↦ (φ j.as).s))
          (fun j ↦ (φ j.as).hs)
      have : IsIso (L.map r) := Localization.inverts L W _ hr
      refine ⟨e.inv ≫ L.map g ≫ inv (L.map r), ?_⟩
      intro j
      have := Localization.inverts L W (φ j).s (φ j).hs
      apply (cancel_mono (L.map (φ j).s)).1
      have he : r ≫ Pi.π (fun j ↦ (φ j).Y') j = Pi.π K j ≫ (φ j).s := by
        simp [r]
      rw [Category.assoc, Category.assoc, ← L.map_comp, ← he, L.map_comp]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← L.map_comp]
      simp only [g, Pi.lift_comp_π]
      have h := congrArg (fun a ↦ e.inv ≫ a ≫ L.map (φ j).s) (hφ j)
      simpa [MorphismProperty.LeftFraction.map, Category.assoc] using h.symm
    choose lift fac using hex
    have hfan : IsLimit (Fan.mk (L.obj (∏ᶜ K)) (fun j ↦ L.map (Pi.π K j))) :=
      Fan.IsLimit.mk _ lift fac (by
        intro s m hm
        change ∀ j, m ≫ L.map (Pi.π K j) = s.proj j at hm
        let e := L.objObjPreimageIso s.pt
        apply (cancel_epi e.hom).1
        apply sub_eq_zero.mp
        apply hzero K (L.objPreimage s.pt)
        intro j
        simp [Preadditive.sub_comp, Category.assoc, hm j, fac s j])
    exact ⟨(isLimitMapConeFanMkEquiv L K _).symm hfan⟩
  have h (K : J → C) : PreservesLimit (Discrete.functor K) L :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hp K).some
  let := h
  exact preservesLimitsOfShape_of_discrete L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Product comparison conjugates the image of a product of morphisms. -/
private theorem isIsoMapProduct
    {C : Type*} [Category* C] {A : Type u} [Category.{v} A]
    (J : Type*) [HasProductsOfShape J C] [HasProductsOfShape J A]
    (H : C ⥤ A) [PreservesLimitsOfShape (Discrete J) H]
    (K M : J → C) (f : ∀ j, K j ⟶ M j) [∀ j, IsIso (H.map (f j))] :
    IsIso (H.map (Limits.Pi.map f)) := by
  have he : H.map (Limits.Pi.map f) =
      (PreservesProduct.iso H K).hom ≫ Limits.Pi.map (fun j ↦ H.map (f j)) ≫
        (PreservesProduct.iso H M).inv := by
    apply (cancel_mono (PreservesProduct.iso H M).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply limit.hom_ext
    rintro ⟨j⟩
    change (H.map (Limits.Pi.map f) ≫ (PreservesProduct.iso H M).hom) ≫ Pi.π _ j =
      ((PreservesProduct.iso H K).hom ≫ Limits.Pi.map (fun j ↦ H.map (f j))) ≫ Pi.π _ j
    simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
      Limits.Pi.map_π, ← H.map_comp]
    rw [← Category.assoc, piComparison_comp_π, H.map_comp]
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The quotient to the homotopy category preserves products of complexes. -/
private theorem quotientPreservesProducts
    (A : Type u) [Category.{v} A] [Abelian A]
    (J : Type*) [HasProductsOfShape J A] :
    PreservesLimitsOfShape (Discrete J) (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have h (K : J → CochainComplex A ℤ) : PreservesLimit (Discrete.functor K) Q := by
    apply preservesLimit_of_preserves_limit_cone (productIsProduct K)
    exact (isLimitMapConeFanMkEquiv Q K _).symm
      (HomotopyCategory.isLimitFanQuotient A (ComplexShape.up ℤ) (productIsProduct K))
  let := h
  exact preservesLimitsOfShape_of_discrete Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The image of the termwise product cone is limiting, without assuming that products
already exist in the derived category.
Source: Stacks Project, Derived Categories, Lemma 13.34.2 (Tag 07KC).

Proof: work first in the homotopy category, where termwise products are products:
chain maps and their homotopies into a product are given componentwise. Exact countable
products commute with homology, so a product of quasi-isomorphisms is a quasi-isomorphism.
For any complex L, represent each morphism from Q(L) to Q(C j) by a left fraction
L → M j ← C j. The product of the denominators is a quasi-isomorphism and the maps
from L assemble into a map to the product of the M j. This fraction is a lift of the
given family. For uniqueness, represent the difference of two lifts by a fraction
L → N ← ∏ C j. For each j, apply the left Ore condition to its denominator and the
projection ∏ C j → C j to obtain a fraction for the j-th component. Since that
component is zero, the equality criterion for fractions gives a further denominator
killing its numerator in the homotopy category. Thus there are maps a j : N → M' j
and quasi-isomorphisms t j : C j → M' j with s ≫ a j = π j ≫ t j and f ≫ a j = 0.
Assemble a : N → ∏ M' j. Then s ≫ a is the product of the t j, hence a
quasi-isomorphism. Since s is a quasi-isomorphism, so is a, by two-out-of-three.
All components of f ≫ a vanish; the product universal property makes f ≫ a = 0.
As a is inverted in the localization, the difference is zero there. Every derived object
is isomorphic to Q(L), so this proves the universal
property for all vertices. Empty and singleton families give the zero and identity
cones, respectively.
(blueprint: lem-weil-derived-countable-products-core) -/
theorem derivedCategory_termwiseProduct_isLimit
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (J : Type) [Countable J] (C : J → CochainComplex A ℤ) :
    Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C)))) := by
  classical
  have hQ (J : Type) [Countable J] :
      PreservesLimitsOfShape (Discrete J) (DerivedCategory.Q (C := A)) := by
    let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    have hq : PreservesLimitsOfShape (Discrete J) q := quotientPreservesProducts A J
    have hH (p : ℤ) : PreservesLimitsOfShape (Discrete J)
        (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p) := by
      have := complexHomologyLimit A (Discrete J) p
      have : PreservesLimitsOfShape (Discrete J)
          (q ⋙ HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p) :=
        preservesLimitsOfShape_of_natIso
          (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) p).symm
      exact preservesProductsOfEssSurj J q _
        (fun K ↦ ⟨isLimitOfPreserves q (limit.isLimit _)⟩)
    let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
    have : W.IsStableUnderProductsOfShape J :=
      MorphismProperty.IsStableUnderProductsOfShape.mk W J (by
        intro K M _ _ f hf
        change HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (Limits.Pi.map f)
        rw [HomotopyCategory.mem_quasiIso_iff]
        intro p
        let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) p
        have := hH p
        have (j : J) : IsIso (H.map (f j)) :=
          (HomotopyCategory.mem_quasiIso_iff (f j)).mp (hf j) p
        exact isIsoMapProduct J H K M f)
    have := localizationPreservesProducts J (DerivedCategory.Qh (C := A)) W
    have : PreservesLimitsOfShape (Discrete J) (q ⋙ DerivedCategory.Qh) := inferInstance
    exact preservesLimitsOfShape_of_natIso (DerivedCategory.quotientCompQhIso A)
  have := hQ J
  exact ⟨isLimitOfPreserves DerivedCategory.Q (limit.isLimit _)⟩

end CategoryTheory
