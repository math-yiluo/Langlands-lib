/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Passing from Hom comparison to Isom comparison by inverse pairs

Source: Stacks Project, Tag 00WJ, exactness of set sheafification, applied to inverse pairs.
(blueprint: lem-weil-pbc-derived-isom-comparison-from-hom)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
variable (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]
variable (A D G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

private noncomputable def presheafPairSection
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) : (P ⨯ Q).obj (op U) :=
  inv (prodComparison ((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)) P Q)
    ((Types.binaryProductIso _ _).inv (s, t))

omit [EssentiallySmall.{u + 1} C] in
private theorem presheafPairSection_fst
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) :
    (prod.fst : P ⨯ Q ⟶ P).app (op U) (presheafPairSection P Q U s t) = s := by
  unfold presheafPairSection
  change (((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.fst) _ = s
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_fst,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_fst]
  rfl

omit [EssentiallySmall.{u + 1} C] in
private theorem presheafPairSection_snd
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (U : C)
    (s : P.obj (op U)) (t : Q.obj (op U)) :
    (prod.snd : P ⨯ Q ⟶ Q).app (op U) (presheafPairSection P Q U s t) = t := by
  unfold presheafPairSection
  change (((evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.snd) _ = t
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_snd,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_snd]
  rfl

private noncomputable def rawComp :
    derivedLocalHomPresheaf J B A D ⨯ derivedLocalHomPresheaf J B D G ⟶
      derivedLocalHomPresheaf J B A G where
  app U := ↾fun z ↦ (prod.fst : derivedLocalHomPresheaf J B A D ⨯
    derivedLocalHomPresheaf J B D G ⟶ _).app U z ≫
      (prod.snd : derivedLocalHomPresheaf J B A D ⨯
        derivedLocalHomPresheaf J B D G ⟶ _).app U z
  naturality U V h := by
    apply ConcreteCategory.hom_ext
    intro z
    simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    erw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    simp only [derivedLocalHomPresheaf, TypeCat.ofHom_apply, derivedLocalHomRestriction,
      Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private noncomputable def rawId {P : Cᵒᵖ ⥤ Type (u + 1)} :
    P ⟶ derivedLocalHomPresheaf J B A A where
  app U := ↾fun _ ↦ 𝟙 _
  naturality U V h := by
    ext z
    simp [derivedLocalHomPresheaf, derivedLocalHomRestriction]

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local instance] preservesFiniteLimits_proEtaleSiteComparison

private theorem pairSection_ext {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C) (x y : (F ⨯ G).obj.obj (op U))
    (h₁ : (prod.fst : F ⨯ G ⟶ F).hom.app (op U) x =
      (prod.fst : F ⨯ G ⟶ F).hom.app (op U) y)
    (h₂ : (prod.snd : F ⨯ G ⟶ G).hom.app (op U) x =
      (prod.snd : F ⨯ G ⟶ G).hom.app (op U) y) : x = y := by
  let E := sheafToPresheaf J (Type (u + 1)) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (Type (u + 1))).obj (op U)
  apply (ConcreteCategory.bijective_of_isIso (prodComparison E F G)).injective
  apply (ConcreteCategory.bijective_of_isIso
    (Types.binaryProductIso (E.obj F) (E.obj G)).hom).injective
  apply _root_.Prod.ext
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.fst : (E.obj F × E.obj G) ⟶ E.obj F) = E.map prod.fst := by
      rw [Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
    change (E.map prod.fst) x = (E.map prod.fst) y at h₁
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₁.trans (ConcreteCategory.congr_hom ht y).symm)
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.snd : (E.obj F × E.obj G) ⟶ E.obj G) = E.map prod.snd := by
      rw [Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
    change (E.map prod.snd) x = (E.map prod.snd) y at h₂
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₂.trans (ConcreteCategory.congr_hom ht y).symm)

private theorem transpose_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {P : C} {Q : D}
    (f : P ⟶ G.obj Q) :
    adj.unit.app P ≫ G.map ((adj.homEquiv P Q).symm f) = f := by
  exact (adj.homEquiv P Q).apply_symm_apply f

private noncomputable abbrev originFunctor (X : Scheme.{u}) :=
  presheafToSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ comparisonSetUpperStar X

private noncomputable abbrev originAdjunction (X : Scheme.{u}) :=
  (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).comp
    (proEtaleSiteComparison X)

private noncomputable def productMap {C₁ C₂ D : Type*}
    [Category C₁] [Category C₂] [Category D]
    [HasBinaryProducts C₁] [HasBinaryProducts C₂] [HasBinaryProducts D]
    (F : C₁ ⥤ D) (G : C₂ ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    {P Q : C₁} {P' Q' : C₂} (a : F.obj P ⟶ G.obj P') (b : F.obj Q ⟶ G.obj Q') :
    F.obj (P ⨯ Q) ⟶ G.obj (P' ⨯ Q') :=
  prodComparison F P Q ≫ prod.map a b ≫ inv (prodComparison G P' Q')

private theorem productMap_fst {C₁ C₂ D : Type*}
    [Category C₁] [Category C₂] [Category D]
    [HasBinaryProducts C₁] [HasBinaryProducts C₂] [HasBinaryProducts D]
    (F : C₁ ⥤ D) (G : C₂ ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    {P Q : C₁} {P' Q' : C₂} (a : F.obj P ⟶ G.obj P') (b : F.obj Q ⟶ G.obj Q') :
    productMap F G a b ≫ G.map prod.fst = F.map prod.fst ≫ a := by
  simp only [productMap, Category.assoc, inv_prodComparison_map_fst, prod.map_fst]
  rw [← Category.assoc, prodComparison_fst]

private theorem productMap_snd {C₁ C₂ D : Type*}
    [Category C₁] [Category C₂] [Category D]
    [HasBinaryProducts C₁] [HasBinaryProducts C₂] [HasBinaryProducts D]
    (F : C₁ ⥤ D) (G : C₂ ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    {P Q : C₁} {P' Q' : C₂} (a : F.obj P ⟶ G.obj P') (b : F.obj Q ⟶ G.obj Q') :
    productMap F G a b ≫ G.map prod.snd = F.map prod.snd ≫ b := by
  simp only [productMap, Category.assoc, inv_prodComparison_map_snd, prod.map_snd]
  rw [← Category.assoc, prodComparison_snd]

private theorem hom_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedHomSheafComparison X B A D) =
      derivedComparisonHomPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedHomSheafComparison X B A D)) = _
  rw [derivedHomSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedIsoSheafComparison X B A D) =
      derivedComparisonIsoPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedIsoSheafComparison X B A D)) = _
  rw [derivedIsoSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private noncomputable def originSection (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ Type (u + 1)) (V : X.Etaleᵒᵖ) (x : P.obj V) :
    ((originFunctor X).obj P).obj.obj (op ((toProEt X).obj V.unop)) :=
  (((proEtaleSiteComparison X).unit.app
    ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj P)).hom.app V)
      ((toSheafify X.smallEtaleTopology P).app V x)

private theorem originSection_map (X : Scheme.{u})
    {P Q : X.Etaleᵒᵖ ⥤ Type (u + 1)} (f : P ⟶ Q) (V : X.Etaleᵒᵖ) (x : P.obj V) :
    ((originFunctor X).map f).hom.app (op ((toProEt X).obj V.unop))
        (originSection X P V x) = originSection X Q V (f.app V x) :=
  (ConcreteCategory.congr_hom (congr_app ((originAdjunction X).unit.naturality f) V) x).symm

private theorem hom_generator (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etaleᵒᵖ) (x : (derivedLocalHomPresheaf X.smallEtaleTopology B A D).obj V) :
    (derivedHomSheafComparison X B A D).hom.app (op ((toProEt X).obj V.unop))
        (originSection X _ V x) = derivedComparisonHomUnit X B A D V.unop x := by
  have hc := transpose_unit (proEtaleSiteComparison X)
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonHomPresheafMap X B A D))
  have hs := transpose_unit (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Q := ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X)).obj (derivedComparisonHomTarget X B A D))
    (derivedComparisonHomPresheafMap X B A D)
  exact (congrArg (fun k ↦ k.hom.app V
    ((toSheafify X.smallEtaleTopology
      (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app V x)) hc).trans
    (congrArg (fun k ↦ k.app V x) hs)

private theorem origin_ext (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ Type (u + 1)) (Q : Sheaf (ProEt.topology X) (Type (u + 1)))
    (f g : (originFunctor X).obj P ⟶ Q)
    (h : ∀ (V : X.Etaleᵒᵖ) (x : P.obj V),
      f.hom.app (op ((toProEt X).obj V.unop)) (originSection X P V x) =
        g.hom.app (op ((toProEt X).obj V.unop)) (originSection X P V x)) : f = g := by
  apply ((originAdjunction X).homEquiv P Q).injective
  ext V x
  exact h V x

private theorem product_generator (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D A₂ D₂ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etaleᵒᵖ)
    (z : (derivedLocalHomPresheaf X.smallEtaleTopology B A D ⨯
      derivedLocalHomPresheaf X.smallEtaleTopology B A₂ D₂).obj V) :
    let F := originFunctor X
    let G := presheafToSheaf (ProEt.topology X) (Type (u + 1))
    let P := derivedLocalHomPresheaf X.smallEtaleTopology B A D
    let Q := derivedLocalHomPresheaf X.smallEtaleTopology B A₂ D₂
    let P' := derivedLocalHomPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
    let Q' := derivedLocalHomPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A₂) ((derivedComparison X B).obj D₂)
    let z' := presheafPairSection P' Q' ((toProEt X).obj V.unop)
      (derivedComparisonLocalHom X B A D V.unop ((prod.fst : P ⨯ Q ⟶ P).app V z))
      (derivedComparisonLocalHom X B A₂ D₂ V.unop ((prod.snd : P ⨯ Q ⟶ Q).app V z))
    (productMap F G (derivedHomSheafComparison X B A D)
      (derivedHomSheafComparison X B A₂ D₂)).hom.app (op ((toProEt X).obj V.unop))
        (originSection X (P ⨯ Q) V z) =
      (toSheafify (ProEt.topology X) (P' ⨯ Q')).app (op ((toProEt X).obj V.unop)) z' := by
  dsimp only
  let F := originFunctor X
  let G := presheafToSheaf (ProEt.topology X) (Type (u + 1))
  let P := derivedLocalHomPresheaf X.smallEtaleTopology B A D
  let Q := derivedLocalHomPresheaf X.smallEtaleTopology B A₂ D₂
  let P' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
  let Q' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A₂) ((derivedComparison X B).obj D₂)
  let m := productMap F G (derivedHomSheafComparison X B A D)
    (derivedHomSheafComparison X B A₂ D₂)
  apply (ConcreteCategory.bijective_of_isIso
    ((prodComparison G P' Q').hom.app (op ((toProEt X).obj V.unop)))).injective
  apply pairSection_ext
  · change ((m ≫ prodComparison G P' Q' ≫ prod.fst).hom.app
      (op ((toProEt X).obj V.unop))) _ = _
    rw [prodComparison_fst, productMap_fst]
    change (derivedHomSheafComparison X B A D).hom.app _
      (((F.map prod.fst).hom.app _) (originSection X (P ⨯ Q) V z)) = _
    rw [originSection_map, hom_generator]
    change _ = ((prodComparison G P' Q' ≫ prod.fst).hom.app _) _
    rw [prodComparison_fst]
    have hn := toSheafify_naturality (ProEt.topology X) (prod.fst : P' ⨯ Q' ⟶ P')
    have h := ConcreteCategory.congr_hom
      (congr_app hn (op ((toProEt X).obj V.unop)))
        (presheafPairSection P' Q' ((toProEt X).obj V.unop)
          (derivedComparisonLocalHom X B A D V.unop ((prod.fst : P ⨯ Q ⟶ P).app V z))
          (derivedComparisonLocalHom X B A₂ D₂ V.unop ((prod.snd : P ⨯ Q ⟶ Q).app V z)))
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
      presheafPairSection_fst, derivedComparisonHomUnit, G, P', Q'] using h
  · change ((m ≫ prodComparison G P' Q' ≫ prod.snd).hom.app
      (op ((toProEt X).obj V.unop))) _ = _
    rw [prodComparison_snd, productMap_snd]
    change (derivedHomSheafComparison X B A₂ D₂).hom.app _
      (((F.map prod.snd).hom.app _) (originSection X (P ⨯ Q) V z)) = _
    rw [originSection_map, hom_generator]
    change _ = ((prodComparison G P' Q' ≫ prod.snd).hom.app _) _
    rw [prodComparison_snd]
    have hn := toSheafify_naturality (ProEt.topology X) (prod.snd : P' ⨯ Q' ⟶ Q')
    have h := ConcreteCategory.congr_hom
      (congr_app hn (op ((toProEt X).obj V.unop)))
        (presheafPairSection P' Q' ((toProEt X).obj V.unop)
          (derivedComparisonLocalHom X B A D V.unop ((prod.fst : P ⨯ Q ⟶ P).app V z))
          (derivedComparisonLocalHom X B A₂ D₂ V.unop ((prod.snd : P ⨯ Q ⟶ Q).app V z)))
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
      presheafPairSection_snd, derivedComparisonHomUnit, G, P', Q'] using h

private theorem composition_square (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    productMap (originFunctor X)
        (presheafToSheaf (ProEt.topology X) (Type (u + 1)))
        (derivedHomSheafComparison X B A D) (derivedHomSheafComparison X B D E) ≫
      (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
        (rawComp (ProEt.topology X) B ((derivedComparison X B).obj A)
          ((derivedComparison X B).obj D) ((derivedComparison X B).obj E)) =
    (originFunctor X).map (rawComp X.smallEtaleTopology B A D E) ≫
      derivedHomSheafComparison X B A E := by
  apply origin_ext X
  intro V z
  change ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map _).hom.app _
    ((productMap (originFunctor X)
      (presheafToSheaf (ProEt.topology X) (Type (u + 1)))
      (derivedHomSheafComparison X B A D) (derivedHomSheafComparison X B D E)).hom.app _
        (originSection X _ V z)) =
      (derivedHomSheafComparison X B A E).hom.app _
        (((originFunctor X).map _).hom.app _ (originSection X _ V z))
  rw [product_generator, originSection_map, hom_generator]
  let P := derivedLocalHomPresheaf X.smallEtaleTopology B A D
  let Q := derivedLocalHomPresheaf X.smallEtaleTopology B D E
  let P' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
  let Q' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj D) ((derivedComparison X B).obj E)
  let z' := presheafPairSection P' Q' ((toProEt X).obj V.unop)
    (derivedComparisonLocalHom X B A D V.unop ((prod.fst : P ⨯ Q ⟶ P).app V z))
    (derivedComparisonLocalHom X B D E V.unop ((prod.snd : P ⨯ Q ⟶ Q).app V z))
  have hn := toSheafify_naturality (ProEt.topology X)
    (rawComp (ProEt.topology X) B ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D) ((derivedComparison X B).obj E))
  have h := (ConcreteCategory.congr_hom
    (congr_app hn (op ((toProEt X).obj V.unop))) z').symm
  have hc : (rawComp (ProEt.topology X) B ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D) ((derivedComparison X B).obj E)).app
        (op ((toProEt X).obj V.unop)) z' =
      derivedComparisonLocalHom X B A E V.unop
        ((rawComp X.smallEtaleTopology B A D E).app V z) := by
    dsimp only [rawComp, TypeCat.ofHom_apply, z']
    rw [presheafPairSection_fst, presheafPairSection_snd]
    simp only [derivedComparisonLocalHom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    rfl
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact h.trans (congrArg ((toSheafify (ProEt.topology X)
    (derivedLocalHomPresheaf (ProEt.topology X) B ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj E))).app (op ((toProEt X).obj V.unop))) hc)

private theorem identity_square (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D E H K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    productMap (originFunctor X)
        (presheafToSheaf (ProEt.topology X) (Type (u + 1)))
        (derivedHomSheafComparison X B A D) (derivedHomSheafComparison X B E H) ≫
      (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
        (rawId (ProEt.topology X) B ((derivedComparison X B).obj K)) =
    (originFunctor X).map (rawId X.smallEtaleTopology B K) ≫
      derivedHomSheafComparison X B K K := by
  apply origin_ext X
  intro V z
  change ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map _).hom.app _
    ((productMap (originFunctor X)
      (presheafToSheaf (ProEt.topology X) (Type (u + 1)))
      (derivedHomSheafComparison X B A D) (derivedHomSheafComparison X B E H)).hom.app _
        (originSection X _ V z)) =
      (derivedHomSheafComparison X B K K).hom.app _
        (((originFunctor X).map _).hom.app _ (originSection X _ V z))
  rw [product_generator, originSection_map, hom_generator]
  let P := derivedLocalHomPresheaf X.smallEtaleTopology B A D
  let Q := derivedLocalHomPresheaf X.smallEtaleTopology B E H
  let P' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
  let Q' := derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj E) ((derivedComparison X B).obj H)
  let z' := presheafPairSection P' Q' ((toProEt X).obj V.unop)
    (derivedComparisonLocalHom X B A D V.unop ((prod.fst : P ⨯ Q ⟶ P).app V z))
    (derivedComparisonLocalHom X B E H V.unop ((prod.snd : P ⨯ Q ⟶ Q).app V z))
  have hn := toSheafify_naturality (ProEt.topology X)
    (rawId (ProEt.topology X) B ((derivedComparison X B).obj K) (P := P' ⨯ Q'))
  have h := (ConcreteCategory.congr_hom
    (congr_app hn (op ((toProEt X).obj V.unop))) z').symm
  have hc : (rawId (ProEt.topology X) B ((derivedComparison X B).obj K)
      (P := P' ⨯ Q')).app (op ((toProEt X).obj V.unop)) z' =
      derivedComparisonLocalHom X B K K V.unop
        ((rawId X.smallEtaleTopology B K).app V z) := by
    change 𝟙 _ = derivedComparisonLocalHom X B K K V.unop (𝟙 _)
    simp [derivedComparisonLocalHom]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact h.trans (congrArg ((toSheafify (ProEt.topology X)
    (derivedLocalHomPresheaf (ProEt.topology X) B ((derivedComparison X B).obj K)
      ((derivedComparison X B).obj K))).app (op ((toProEt X).obj V.unop))) hc)

private theorem iso_hom (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    derivedIsoSheafComparison X B A D ≫
        (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
          (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
            (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D)) =
      (originFunctor X).map
        (derivedLocalIsoToHomPresheaf (J := X.smallEtaleTopology) (B := B)
          (A := A) (D := D)) ≫ derivedHomSheafComparison X B A D := by
  apply ((originAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    iso_transpose, hom_transpose]
  ext V f
  have hn := toSheafify_naturality (ProEt.topology X)
    (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
      (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D))
  exact (ConcreteCategory.congr_hom (congr_app hn (op ((toProEt X).obj V.unop)))
    (derivedComparisonLocalIso X B A D V.unop f)).symm

end AlgebraicGeometry.Scheme
