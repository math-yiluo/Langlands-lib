/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapComparison
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-! # Target isomorphisms and module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Tags 013P, 013S and 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-target-iso-naturality).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

private theorem sectionsAdditive (X : Scheme.{u}) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
  inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)

-- Combine the derived-functor comparison with the forgetful homology comparison.
private def resolutionSectionsIso {A : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] {R : Type u} [Ring R]
    (Γ : A ⥤ ModuleCat.{u} R) [Γ.Additive] {F : A}
    (I : InjectiveResolution F) (p : ℕ) :=
  (forget₂ _ AddCommGrpCat.{u}).mapIso (I.isoRightDerivedObj Γ p) ≪≫
    ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm

private theorem resolutionSectionsIso_naturality {A : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] {R : Type u} [Ring R]
    (Γ : A ⥤ ModuleCat.{u} R) [Γ.Additive] {F : A}
    {F' : A} (b : F ⟶ F') (I : InjectiveResolution F) (I' : InjectiveResolution F') (p : ℕ) :
    (resolutionSectionsIso Γ I p).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (((Γ ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc b I' I)) =
      (forget₂ _ AddCommGrpCat.{u}).map ((Γ.rightDerived p).map b) ≫
      (resolutionSectionsIso Γ I' p).hom := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let α := InjectiveResolution.desc b I' I
  let S := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p
  let S' := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex).sc p
  have hn := I.isoRightDerivedObj_hom_naturality b I' α (by simp [α]) Γ p
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map α)) U
  change U.map ((Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map α) ≫
      (S'.mapHomologyIso U).inv =
    (S.mapHomologyIso U).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).map α) at hs
  change U.map (I.isoRightDerivedObj Γ p).hom ≫
      (S.mapHomologyIso U).inv ≫ _ =
    U.map ((Γ.rightDerived p).map b) ≫
      U.map (I'.isoRightDerivedObj Γ p).hom ≫ (S'.mapHomologyIso U).inv
  rw [← hs, ← Category.assoc, ← Functor.map_comp]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ U.map f ≫ (S'.mapHomologyIso U).inv) hn.symm

set_option backward.isDefEq.respectTransparency.types false in
-- Generalize the identity comparison to the actual target coefficient morphism.
private theorem target_comparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf} (φ : G ⟶ (pushforward h).obj F)
    (b : F ⟶ F') (C : ModuleCohomologyFMapData h G F φ)
    (C' : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) :
    ∃ e : C.K ⟶ C'.K,
      Nonempty (Homotopy (C.lambda ≫ e)
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc b C'.I C.I) ≫ C'.lambda)) ∧
      Nonempty (Homotopy (C.β ≫ e)
        (InjectiveResolution.desc (𝟙 G) C'.J C.J ≫ C'.β)) := by
  let P := pushforward h
  have : P.Additive := inferInstanceAs (pushforward h).Additive
  let PP := P.mapHomologicalComplex (ComplexShape.up ℕ)
  let αI := InjectiveResolution.desc b C'.I C.I
  let αJ := InjectiveResolution.desc (𝟙 G) C'.J C.J
  have : QuasiIso C.lambda := C.quasiIso
  obtain ⟨e, he⟩ := lift_nat_quasiIso C'.injective C.lambda (PP.map αI ≫ C'.lambda)
  refine ⟨e, he, ?_⟩
  let γ₀ := φ ≫ P.map (C.I.ι.f 0)
  have hγ₀ : γ₀ ≫ (PP.obj C.I.cocomplex).d 0 1 = 0 := by
    change (φ ≫ P.map (C.I.ι.f 0)) ≫ P.map (C.I.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← P.map_comp, C.I.ι_f_zero_comp_complex_d,
      P.map_zero, comp_zero]
  let γ := (CochainComplex.fromSingle₀Equiv (PP.obj C.I.cocomplex) G).symm ⟨γ₀, hγ₀⟩
  have hγ : γ.f 0 = γ₀ := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
  have hβ : C.J.ι ≫ C.β = γ ≫ C.lambda := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hγ]
    exact C.compatible
  have hβ' : C'.J.ι ≫ C'.β = γ ≫ PP.map αI ≫ C'.lambda := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      hγ, C'.compatible]
    change (φ ≫ P.map b) ≫ P.map (C'.I.ι.f 0) ≫ C'.lambda.f 0 =
      γ₀ ≫ P.map (αI.f 0) ≫ C'.lambda.f 0
    dsimp [γ₀, αI]
    simp only [Category.assoc]
    have hc := InjectiveResolution.desc_commutes_zero b C'.I C.I
    simpa only [P.map_comp, Category.assoc] using
      (congrArg (fun f ↦ φ ≫ P.map f ≫ C'.lambda.f 0) hc).symm
  apply unique_nat_quasiIso C'.injective C.J.ι (C.β ≫ e) (αJ ≫ C'.β)
  have hJ : C.J.ι ≫ αJ = C'.J.ι := by simp [αJ]
  have hleft : C.J.ι ≫ (C.β ≫ e) = γ ≫ (C.lambda ≫ e) := by
    rw [← Category.assoc, hβ, Category.assoc]
  have hright : C.J.ι ≫ (αJ ≫ C'.β) = γ ≫ (PP.map αI ≫ C'.lambda) := by
    rw [← Category.assoc, hJ, hβ']
  rw [hleft, hright]
  exact ⟨he.some.compLeft γ⟩

-- The sections square elaborates two scheme-module and complex functor composites.
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionsComparison_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf} {φ : G ⟶ (pushforward h).obj F}
    (b : F ⟶ F') (C : ModuleCohomologyFMapData h G F φ)
    (C' : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) :
    C.a.hom ≫
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc b C'.I C.I))) =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc b C'.I C.I)) ≫ C'.a.hom := by
  rw [← cancel_mono C'.a.inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← cancel_epi C.a.inv,
    Iso.inv_hom_id_assoc]
  ext1 n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, C.sections, C'.sections]
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    ((InjectiveResolution.desc b C'.I C.I).f n)).naturality _ |>.symm

-- The two homology squares imply naturality after cancelling the vertical maps.
private theorem target_diagram_cancel
    {A A' B C D E F K L : AddCommGrpCat.{u}}
    (rI : A ≅ B) (rI' : A' ≅ C) (rJ : D ≅ E) (rJ' : D ≅ F)
    (b : E ⟶ K) (b' : F ⟶ L) (m : B ⟶ K) (m' : C ⟶ L)
    [IsIso m] [IsIso m'] (i : B ⟶ C) (j : E ⟶ F) (q : K ⟶ L)
    (k : A ⟶ A') (hi : rI.hom ≫ i = k ≫ rI'.hom) (hj : rJ.hom ≫ j = rJ'.hom)
    (hlambda : m ≫ q = i ≫ m') (hβ : b ≫ q = j ≫ b') :
    rJ.hom ≫ b ≫ inv m ≫ rI.inv ≫ k = rJ'.hom ≫ b' ≫ inv m' ≫ rI'.inv := by
  rw [← cancel_mono rI'.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hi, Iso.inv_hom_id_assoc]
  have hm : inv m ≫ i ≫ m' = q := by
    rw [← hlambda, IsIso.inv_hom_id_assoc]
  rw [← cancel_mono m']
  simp only [Category.assoc]
  rw [hm, IsIso.inv_hom_id, Category.comp_id, hβ, ← Category.assoc, hj]

-- Compose a comparison square before specializing the objects to section complexes.
private theorem map_comparison_square {A B : Type*} [Category* A] [Category* B]
    (H : A ⥤ B) {X X' Y Y' Z Z' : A}
    (a : X ⟶ Y) (a' : X' ⟶ Y') (l : Y ⟶ Z) (l' : Y' ⟶ Z')
    (i : X ⟶ X') (j : Y ⟶ Y') (q : Z ⟶ Z')
    (ha : a ≫ j = i ≫ a') (hl : H.map l ≫ H.map q = H.map j ≫ H.map l') :
    H.map (a ≫ l) ≫ H.map q = H.map i ≫ H.map (a' ≫ l') := by
  rw [H.map_comp, Category.assoc, hl, ← Category.assoc, ← H.map_comp,
    ha, H.map_comp, H.map_comp, Category.assoc]

-- Resolution transports cross module-valued and additive-group-valued homology.
set_option backward.isDefEq.respectTransparency.types false in
private theorem data_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf} (φ : G ⟶ (pushforward h).obj F)
    (b : F ⟶ F') (C : ModuleCohomologyFMapData h G F φ)
    (C' : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) (p : ℕ) :
    C.map p ≫ (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map b) = C'.map p := by
  have : EnoughInjectives X.Modules := inferInstance
  have : EnoughInjectives Y.Modules := inferInstance
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive := sectionsAdditive X
  have : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).Additive := sectionsAdditive Y
  obtain ⟨e, hl, hb⟩ := target_comparison h φ b C C'
  let ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  let ΓY := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have : ΓY.Additive := by
    dsimp only [ΓY, RingedSpace.globalSectionsFunctor, SheafOfModules.evaluation]
    infer_instance
  let HX := ΓX.mapHomologicalComplex (ComplexShape.up ℕ)
  let HY := ΓY.mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let k := (forget₂ _ AddCommGrpCat.{u}).map
    ((RingedSpace.moduleCohomology X.toRingedSpace p).map b)
  let i := H.map (HX.map (InjectiveResolution.desc b C'.I C.I))
  let j := H.map (HY.map (InjectiveResolution.desc (𝟙 G) C'.J C.J))
  let q := H.map (HY.map e)
  let beta := H.map (HY.map C.β)
  let b' := H.map (HY.map C'.β)
  let m := H.map (C.a.hom ≫ HY.map C.lambda)
  let m' := H.map (C'.a.hom ≫ HY.map C'.lambda)
  have : IsIso m := C.invertible p
  have : IsIso m' := C'.invertible p
  have hβ : beta ≫ q = j ≫ b' := by
    have hh := (ΓY.mapHomotopy hb.some).homologyMap_eq p
    change H.map (HY.map (C.β ≫ e)) =
      H.map (HY.map (_ ≫ C'.β)) at hh
    simpa only [Functor.map_comp] using hh
  have hlambda : m ≫ q = i ≫ m' := by
    have hh := (ΓY.mapHomotopy hl.some).homologyMap_eq p
    change H.map (HY.map (C.lambda ≫ e)) =
      H.map (HY.map (_ ≫ C'.lambda)) at hh
    exact map_comparison_square H C.a.hom C'.a.hom
      (HY.map C.lambda) (HY.map C'.lambda)
      (HX.map (InjectiveResolution.desc b C'.I C.I))
      (HY.map (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc b C'.I C.I))) (HY.map e)
      (sectionsComparison_naturality h b C C')
      (by simpa only [Functor.map_comp] using hh)
  have hi := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) b C.I C'.I p
  have hj := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) (𝟙 G) C.J C'.J p
  change (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.I p).hom ≫ i =
    k ≫ (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) C'.I p).hom at hi
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hj
  change (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C.J p).hom ≫ j =
    (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C'.J p).hom at hj
  have hh := target_diagram_cancel
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.I p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) C'.I p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C.J p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C'.J p)
    beta b' m m' i j q k hi hj hlambda hβ
  simpa only [beta, b', m, m', k, H, HX, HY, ΓX, ΓY, resolutionSectionsIso,
    ModuleCohomologyFMapData.map,
    RingedSpace.globalSectionsComplex, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hh

/-- Target naturality for an isomorphism of the target module.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Tags 013P, 013S and 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-target-iso-naturality).

Proof (resolution comparison, independent of functoriality of h-maps):
1. Let D and E be the data chosen in the two occurrences of moduleCohomologyFMap.
   Write P = h_*. Lift e.hom to c : D.I -> E.I and the identity of G to
   d : D.J -> E.J. Their augmentation equations are I_D.ι c = e.hom I_E.ι
   and J_D.ι d = J_E.ι. Injective-resolution comparison gives these lifts.
2. Extend the natural-indexed complexes by zero to integer indices. E.K is bounded
   below and termwise injective, hence K-injective. Since D.lambda is a
   quasi-isomorphism, precomposition with it is bijective on homotopy classes
   into E.K (Tag 05TG). Lift P(c) followed by E.lambda to t : D.K -> E.K,
   with D.lambda followed by t homotopic to P(c) followed by E.lambda.
3. D.beta followed by t and d followed by E.beta have homotopic composites
   with D.J's augmentation: use D.compatible, the preceding lambda homotopy,
   c's augmentation equation, E.compatible and d's augmentation equation.
   The augmentation of D.J is a quasi-isomorphism, so uniqueness of lifts
   into the bounded below injective E.K makes these two maps homotopic.
4. Apply additive global sections and homology in degree p to these homotopies.
   Restriction from h inverse top to top is natural in the module, so the
   canonical sections comparisons D.a and E.a commute with c. Thus the vertical
   sections maps mu_D and mu_E satisfy H(mu_D) H(t) = H(Gamma(c)) H(mu_E),
   while the horizontal maps satisfy H(Gamma(D.beta)) H(t) =
   H(Gamma(d)) H(Gamma(E.beta)). Both H(mu_D) and H(mu_E) are invertible by
   the data's invertible fields. Cancelling them gives the corresponding square
   between the two horizontal-then-inverse-vertical cohomology maps.
5. Naturality of isoRightDerivedObj identifies the sections map of c with
   H^p(e.hom) and that of d with the identity of H^p(G). Naturality of the
   forgetful homology comparisons transports the square to additive groups.
   Substitution into ModuleCohomologyFMapData.map gives the displayed equation.
   This argument uses no restriction theorem and no h-map functoriality theorem.
-/
theorem moduleCohomologyFMap_target_iso_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F F' : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (e : F ≅ F') (p : ℕ) :
    moduleCohomologyFMap h φ p ≫ (forget₂ _ AddCommGrpCat).map
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map e.hom) =
      moduleCohomologyFMap h (φ ≫ (pushforward h).map e.hom) p := by
  exact data_target_naturality h φ e.hom
    (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ))
    (Classical.choice (moduleCohomologyFMapData_nonempty h G F'
      (φ ≫ (pushforward h).map e.hom))) p

end AlgebraicGeometry.Scheme.Modules
