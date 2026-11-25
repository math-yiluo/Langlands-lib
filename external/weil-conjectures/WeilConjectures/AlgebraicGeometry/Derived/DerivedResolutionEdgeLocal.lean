/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalClassEdgeMap
import all WeilConjectures.AlgebraicGeometry.Local.LocalHypercohomologyClassUnit
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ResolutionDirectImageClassModel
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryLocalClassCycles
import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology

/-! # Local description of the constructed resolution edge
Source: Stacks Project, cohomology.tex, Tags 0BKJ, 0D5X and 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
  AlgebraicGeometry.RingedSpace.topEdgeLocalClass
  AlgebraicGeometry.RingedSpace.topEdgeLocalLeray
  AlgebraicGeometry.RingedSpace.topEdgeDirectImageComparison
namespace AlgebraicGeometry

private theorem edge_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (S : ShortComplex C) :
    ShortComplex.leftExactHomologyEdge G (S.map F) ≫
        G.map (ShortComplex.leftExactHomologyEdge F S) =
      ShortComplex.leftExactHomologyEdge (F ⋙ G) S := by
  have hk : (ShortComplex.leftExactCyclesIso G (S.map F)).inv ≫
        G.map (ShortComplex.leftExactCyclesIso F S).inv =
      (ShortComplex.leftExactCyclesIso (F ⋙ G) S).inv := by
    apply (cancel_mono ((F ⋙ G).map S.iCycles)).1
    change (_ ≫ _) ≫ G.map (F.map S.iCycles) = _
    rw [Category.assoc, ← G.map_comp, ShortComplex.leftExactCyclesIso_inv_i]
    rw [ShortComplex.leftExactCyclesIso_inv_i, ShortComplex.leftExactCyclesIso_inv_i]
    rfl
  apply (cancel_epi ((S.map F).map G).homologyπ).1
  rw [← Category.assoc, ShortComplex.homologyπ_leftExactHomologyEdge,
    Category.assoc, ← G.map_comp, ShortComplex.homologyπ_leftExactHomologyEdge,
    G.map_comp, ← Category.assoc, hk]
  exact (ShortComplex.homologyπ_leftExactHomologyEdge (F ⋙ G) S).symm

private theorem edge_exact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [F.PreservesHomology]
    (S : ShortComplex C) :
    (S.mapHomologyIso F).hom = ShortComplex.leftExactHomologyEdge F S := by
  have hk : (S.mapCyclesIso F).hom = (ShortComplex.leftExactCyclesIso F S).inv := by
    apply (cancel_mono (F.map S.iCycles)).1
    rw [ShortComplex.mapCyclesIso_hom_iCycles, ShortComplex.leftExactCyclesIso_inv_i]
  apply (cancel_epi (S.map F).homologyπ).1
  rw [ShortComplex.homologyπ_mapHomologyIso_hom,
    ShortComplex.homologyπ_leftExactHomologyEdge, hk]

private theorem ordinary_class_edge {Y : RingedSpace.{u}}
    (I : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) (q : ℤ) :
    (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
        ((((RingedSpace.localAbelianSections Y).mapHomologicalComplex (.up ℤ)).obj I).homology q)
        ≫ (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (RingedSpace.localSectionComplexSheafificationIso Y q I).hom =
      ShortComplex.leftExactHomologyEdge (RingedSpace.localAbelianSections Y) (I.sc q) := by
  apply (cancel_epi ((I.sc q).map (RingedSpace.localAbelianSections Y)).homologyπ).1
  rw [ShortComplex.homologyπ_leftExactHomologyEdge]
  exact ordinaryLocalClass_cycles I q

private theorem fixed_model_class (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (q : ℤ) (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (RingedSpace.topEdgeLocalModel X q K).inv ≫ RingedSpace.topEdgeLocalClass X q K ≫
      (RingedSpace.localAbelianSections X).map
        ((DerivedCategory.homologyFunctor _ q).mapIso
            (RingedSpace.topEdgeResolutionIso X K).symm ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app _).hom =
      ShortComplex.leftExactHomologyEdge (RingedSpace.localAbelianSections X)
        ((RingedSpace.topEdgeResolution X K).sc q) := by
  let F := RingedSpace.localAbelianSections X
  let U := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let T := SheafOfModules.toSheaf.{u} (moduleRings X)
  let b := RingedSpace.topEdgeLocalModel X q K
  let d := (DerivedCategory.homologyFunctor _ q).mapIso
      (RingedSpace.topEdgeResolutionIso X K).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _
  have hc : (RingedSpace.localHypercohomologySheafificationAt q K).hom ≫
      (SheafOfModules.toSheaf (moduleRings X)).map d.hom =
    S.map b.hom ≫ (RingedSpace.localSectionComplexSheafificationIso X q
      (RingedSpace.topEdgeResolution X K)).hom := by
    have hn := sheafification_normalization q (RingedSpace.topEdgeResolution X K) K
      (RingedSpace.topEdgeResolutionIso X K).symm
    dsimp only [Functor.comp_map, RingedSpace.localHypercohomologySheafificationModel,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] at hn
    dsimp only [b, d, RingedSpace.topEdgeLocalModel, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [Functor.map_comp, ← Category.assoc, ← hn]
    simp only [Functor.map_comp, Category.assoc]
    erw [← T.map_comp
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (moduleRings X)) q).inv.app
            (RingedSpace.topEdgeResolution X K))
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (moduleRings X)) q).hom.app
            (RingedSpace.topEdgeResolution X K)),
      Iso.inv_hom_id_app, T.map_id, Category.comp_id]
    rfl
  rw [← ordinary_class_edge]
  unfold RingedSpace.topEdgeLocalClass
  change b.inv ≫ ((sheafificationAdjunction _ _).unit.app _ ≫
    U.map (RingedSpace.localHypercohomologySheafificationAt q K).hom) ≫
      U.map (T.map d.hom) = _
  simp only [Category.assoc]
  erw [← U.map_comp, hc, U.map_comp]
  erw [← (sheafificationAdjunction _ _).unit.naturality_assoc b.hom]
  erw [Iso.inv_hom_id_assoc]

private theorem complex_homology_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (I : CochainComplex C ℤ) (q : ℤ) :
    (F.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app I =
      ((I.sc q).mapHomologyIso F).hom := by
  simp only [Functor.mapHomologicalComplexHomologyIso,
    HomologicalComplex.homologyFunctorIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso,
    ShortComplex.homologyFunctorIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatIso.ofComponents_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [F.map_id, Category.comp_id, Category.id_comp, Category.id_comp]

private theorem iso_source {C : Type*} [Category C]
    {A B M N : C} (a : A ≅ B) (t : A ⟶ M) (s : M ⟶ N) (e : B ⟶ N)
    (h : a.inv ≫ t ≫ s = e) : t ≫ s = a.hom ≫ e := by
  rw [← h]
  simp only [Iso.hom_inv_id_assoc]

private theorem iso_target {C : Type*} [Category C]
    {A M N : C} (c : M ≅ N) (t : A ⟶ M) (e : A ⟶ N)
    (h : t ≫ c.hom = e) : e ≫ c.inv = t := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem paste_edges {C : Type*} [Category C]
    {A B M N P Q R Z : C}
    (l : A ⟶ B) (b : B ⟶ M) (m : M ⟶ N) (t : A ⟶ P) (d : P ⟶ Q)
    (r : M ⟶ Q) (e : Q ⟶ R) (v : R ⟶ Z) (p : N ⟶ R) (z : N ⟶ Z)
    (h₁ : t ≫ d = l ≫ b ≫ r) (h₂ : r ≫ e = m ≫ p) (h₃ : p ≫ v = z) :
    t ≫ d ≫ e ≫ v = l ≫ b ≫ m ≫ z := by
  rw [← Category.assoc t d, h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, h₃]

private theorem complex_edge_comp_exact
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [G.PreservesHomology]
    (I : CochainComplex C ℤ) (q : ℤ) :
    ShortComplex.leftExactHomologyEdge (F ⋙ G) (I.sc q) =
      (G.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.map (ShortComplex.leftExactHomologyEdge F (I.sc q)) := by
  rw [complex_homology_comparison]
  change _ = (((I.sc q).map F).mapHomologyIso G).hom ≫ _
  rw [edge_exact]
  exact (edge_comp F G (I.sc q)).symm

private theorem section_edge_square {T S : Scheme.{u}} (g : T ⟶ S)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ) (q : ℤ) :
    let D := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := RingedSpace.localAbelianSections S.toRingedSpace
    let G := RingedSpace.localAbelianSections T.toRingedSpace
    let W := (Functor.whiskeringLeft (Opens S)ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.toLRSHom.toShHom.hom.base).op
    ShortComplex.leftExactHomologyEdge F
        (((D.mapHomologicalComplex (.up ℤ)).obj I).sc q) ≫
        F.map (ShortComplex.leftExactHomologyEdge D (I.sc q)) =
      (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        W.map (ShortComplex.leftExactHomologyEdge G (I.sc q)) := by
  dsimp only
  exact (edge_comp (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (RingedSpace.localAbelianSections S.toRingedSpace) (I.sc q)).trans
      (complex_edge_comp_exact (RingedSpace.localAbelianSections T.toRingedSpace)
        ((Functor.whiskeringLeft (Opens S)ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj
          (Opens.map g.toLRSHom.toShHom.hom.base).op) I q)

-- Transport the section edge along arbitrary choices of homology models.
-- Keeping the complex and comparison isomorphisms as parameters avoids repeatedly
-- reducing the fixed derived resolutions in this ordinary categorical calculation.
private theorem section_edge_transport {T S : Scheme.{u}} (g : T ⟶ S)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ) (q : ℤ) :
    let D := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := RingedSpace.localAbelianSections S.toRingedSpace
    let G := RingedSpace.localAbelianSections T.toRingedSpace
    let W := (Functor.whiskeringLeft (Opens S)ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.toLRSHom.toShHom.hom.base).op
    let J := (D.mapHomologicalComplex (.up ℤ)).obj I
    ∀ {H : SheafOfModules.{u} (moduleRings S.toRingedSpace)}
      {H' : SheafOfModules.{u} (moduleRings T.toRingedSpace)}
      {L M : (Opens S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {N : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}}
      (d : H ≅ J.homology q) (c : H' ≅ I.homology q) (l : L ≅ M)
      (b : M ≅ ((F.mapHomologicalComplex (.up ℤ)).obj J).homology q)
      (a : N ≅ ((G.mapHomologicalComplex (.up ℤ)).obj I).homology q)
      (m : ((F.mapHomologicalComplex (.up ℤ)).obj J).homology q ⟶
        W.obj (((G.mapHomologicalComplex (.up ℤ)).obj I).homology q))
      (s : L ⟶ F.obj H) (t : N ⟶ G.obj H'),
      b.inv ≫ l.inv ≫ s ≫ F.map d.hom = ShortComplex.leftExactHomologyEdge F (J.sc q) →
      a.inv ≫ t ≫ G.map c.hom = ShortComplex.leftExactHomologyEdge G (I.sc q) →
      ShortComplex.leftExactHomologyEdge F (J.sc q) ≫
          F.map (ShortComplex.leftExactHomologyEdge D (I.sc q)) =
        m ≫ W.map (ShortComplex.leftExactHomologyEdge G (I.sc q)) →
      s ≫ F.map (d.hom ≫ ShortComplex.leftExactHomologyEdge D (I.sc q) ≫ D.map c.inv) =
        l.hom ≫ b.hom ≫ m ≫ W.map (a.inv ≫ t) := by
  dsimp only
  intro H H' L M N d c l b a m s t hd hc hs
  let D := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let F := RingedSpace.localAbelianSections S.toRingedSpace
  let G := RingedSpace.localAbelianSections T.toRingedSpace
  let W := (Functor.whiskeringLeft (Opens S)ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map g.toLRSHom.toShHom.hom.base).op
  let J := (D.mapHomologicalComplex (.up ℤ)).obj I
  have ht : s ≫ F.map d.hom =
      l.hom ≫ b.hom ≫ ShortComplex.leftExactHomologyEdge F (J.sc q) := by
    simpa only [Iso.trans_hom, Category.assoc] using
      iso_source (l ≪≫ b) s (F.map d.hom)
        (ShortComplex.leftExactHomologyEdge F (J.sc q))
        (by simpa only [Iso.trans_inv, Category.assoc] using hd)
  have hc' : ShortComplex.leftExactHomologyEdge G (I.sc q) ≫ G.map c.inv = a.inv ≫ t := by
    exact iso_target (G.mapIso c) (a.inv ≫ t)
      (ShortComplex.leftExactHomologyEdge G (I.sc q))
      (by simpa only [Functor.mapIso_hom, Category.assoc] using hc)
  have hw : W.map (ShortComplex.leftExactHomologyEdge G (I.sc q)) ≫ F.map (D.map c.inv) =
      W.map (a.inv ≫ t) := by
    change W.map (ShortComplex.leftExactHomologyEdge G (I.sc q)) ≫ W.map (G.map c.inv) = _
    exact (W.map_comp _ _).symm.trans (congrArg W.map hc')
  simpa only [Functor.map_comp] using
    paste_edges l.hom b.hom m s (F.map d.hom)
      (ShortComplex.leftExactHomologyEdge F (J.sc q))
      (F.map (ShortComplex.leftExactHomologyEdge D (I.sc q))) (F.map (D.map c.inv))
      (W.map (ShortComplex.leftExactHomologyEdge G (I.sc q))) (W.map (a.inv ≫ t)) ht hs hw

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The kernel/cokernel resolution edge has the fixed local-class description.
Source: Stacks Project, cohomology.tex, Tags 0BKJ and 0D5X, the cycle-class
construction and local Leray comparison; Tag 079W, normalization by the derived unit.
(blueprint: lem-weil-pbc-resolution-local-class-edge-local).

Proof: Write I for the fixed K-injective representative of K and B for g_*I.
The direct-image homology identification in resolutionLocalClassEdge transports
H^q(Rg_*K) to H^q(B). The corresponding local comparison transports local derived
sections to H^q of the section complex of B: this follows from the universal-unit
equation defining localLerayComparison, after evaluating both derived direct-image
comparisons on I. The specified hom of unboundedDirectImage_sectionPresheaf identifies
its chosen isomorphism with this comparison; thus there is no choice of local Leray map.

On an arbitrary complex B the sheafification unit followed by
localSectionComplexSheafificationIso sends a section cocycle to its class in the
underlying cohomology sheaf. This is the kernel/cokernel universal property: precompose
with the quotient from cycles, use the exact-sheafification homology comparison, and
then its counit identity. Apply this observation to B and to I. Preservation of kernels
by g_* identifies cycles of B with g_* of cycles of I, and the definition of
leftExactHomologyEdge makes the two maps from these cycles equal after taking their
cohomology classes. Precomposition by inverse-image opens preserves homology, so its
published homology comparison makes this equality the inverse-open local-class map.

Finally localHypercohomologySheafificationAt is normalized on fixed representatives
by localHypercohomologySheafificationModel. Naturality of that comparison transports
the preceding equation along the resolution isomorphisms on S and T and along the
direct-image comparison, cancelling the homology-factorization isomorphisms. This is
the displayed equation of presheaf maps. Evaluation at V proves the assertion.
The argument uses only kernels, cokernels and isomorphisms; it requires neither
acyclicity of B for module homology nor any boundedness, and also covers empty opens,
zero complexes and negative q. -/
theorem resolutionLocalClassEdge_local {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (K : schemeDerivedCategory T) (V : (TopologicalSpace.Opens S)ᵒᵖ) :
    (RingedSpace.topEdgeLocalClass S.toRingedSpace q
      ((schemeDerivedDirectImage g).obj K)).app V ≫
        ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map
          (resolutionLocalClassEdge g q K)).hom.app V =
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
        (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V := by
  let f := g.toLRSHom.toShHom
  let D := RingedSpace.moduleDirectImage f
  let F := RingedSpace.localAbelianSections S.toRingedSpace
  let G := RingedSpace.localAbelianSections T.toRingedSpace
  let W := (Functor.whiskeringLeft (Opens S)ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj
    (Opens.map f.hom.base).op
  let I := RingedSpace.topEdgeResolution T.toRingedSpace K
  let J := (D.mapHomologicalComplex (.up ℤ)).obj I
  let b := RingedSpace.topEdgeInverseModel f q K
  let a := RingedSpace.topEdgeLocalModel T.toRingedSpace q K
  let l := RingedSpace.topEdgeLocalLeray f q K
  let c := localClassResolutionHomologyIso T q K
  let d := localClassDirectImageHomologyIso g q K
  have hd : b.inv ≫ l.inv ≫
      RingedSpace.topEdgeLocalClass S.toRingedSpace q ((schemeDerivedDirectImage g).obj K) ≫
        F.map d.hom = ShortComplex.leftExactHomologyEdge F (J.sc q) := by
    exact resolutionDirectImageClassModel g q K
  have hc : a.inv ≫ RingedSpace.topEdgeLocalClass T.toRingedSpace q K ≫
      G.map c.hom = ShortComplex.leftExactHomologyEdge G (I.sc q) :=
    fixed_model_class T.toRingedSpace q K
  let m : ((F.mapHomologicalComplex (.up ℤ)).obj J).homology q ⟶
      W.obj (((G.mapHomologicalComplex (.up ℤ)).obj I).homology q) :=
    (W.mapHomologicalComplexHomologyIso (.up ℤ) q).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj I)
  have h : RingedSpace.topEdgeLocalClass S.toRingedSpace q
        ((schemeDerivedDirectImage g).obj K) ≫ F.map (resolutionLocalClassEdge g q K) =
      l.hom ≫ RingedSpace.topEdgeInverseLocalClass f q K := by
    exact section_edge_transport g I q d c l b a m
      (RingedSpace.topEdgeLocalClass S.toRingedSpace q ((schemeDerivedDirectImage g).obj K))
      (RingedSpace.topEdgeLocalClass T.toRingedSpace q K) hd hc (section_edge_square g I q)
  exact NatTrans.congr_app h V

end AlgebraicGeometry
