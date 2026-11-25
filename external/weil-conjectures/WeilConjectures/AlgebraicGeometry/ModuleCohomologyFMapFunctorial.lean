/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapCompData
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-! # Functoriality of cohomology maps induced by scheme maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Lemma 01F8 and Remark 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

The comparison maps below account for the canonical identifications of successive
pushforwards. The unit equations specify the pullback comparison and the restricted
module map without choosing another implementation of either notion.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

private instance schemeEnoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules :=
  inferInstance

private instance sectionsAdditive (X : Scheme.{u}) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
  inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)

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
    (I I' : InjectiveResolution F) (p : ℕ) :
    (resolutionSectionsIso Γ I p).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        (((Γ ⋙ forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (𝟙 F) I' I)) =
      (resolutionSectionsIso Γ I' p).hom := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let α := InjectiveResolution.desc (𝟙 F) I' I
  let S := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p
  let S' := ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex).sc p
  have hn := I.isoRightDerivedObj_hom_naturality (𝟙 F) I' α (by simp [α]) Γ p
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
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
    U.map (I'.isoRightDerivedObj Γ p).hom ≫ (S'.mapHomologyIso U).inv
  rw [← hs, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f ↦ U.map f ≫ (S'.mapHomologyIso U).inv) hn.symm

private theorem independence_diagram_cancel
    {A B C D E F K L : AddCommGrpCat.{u}}
    (rI : A ≅ B) (rI' : A ≅ C) (rJ : D ≅ E) (rJ' : D ≅ F)
    (b : E ⟶ K) (b' : F ⟶ L) (m : B ⟶ K) (m' : C ⟶ L)
    [IsIso m] [IsIso m'] (i : B ⟶ C) (j : E ⟶ F) (q : K ⟶ L)
    (hi : rI.hom ≫ i = rI'.hom) (hj : rJ.hom ≫ j = rJ'.hom)
    (hlambda : m ≫ q = i ≫ m') (hβ : b ≫ q = j ≫ b') :
    rJ.hom ≫ b ≫ inv m ≫ rI.inv = rJ'.hom ≫ b' ≫ inv m' ≫ rI'.inv := by
  rw [← cancel_mono rI'.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hi, Iso.inv_hom_id_assoc]
  have hm : inv m ≫ i ≫ m' = q := by
    rw [← hlambda, IsIso.inv_hom_id_assoc]
  rw [← cancel_mono m']
  simp only [Category.assoc]
  rw [hm, IsIso.inv_hom_id, Category.comp_id, hβ, ← Category.assoc, hj]

-- The sections square elaborates two scheme-module and complex functor composites.
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionsComparison_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} {φ : G ⟶ (pushforward h).obj F}
    (C C' : ModuleCohomologyFMapData h G F φ) :
    C.a.hom ≫
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (𝟙 F) C'.I C.I))) =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (𝟙 F) C'.I C.I)) ≫ C'.a.hom := by
  rw [← cancel_mono C'.a.inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← cancel_epi C.a.inv,
    Iso.inv_hom_id_assoc]
  ext1 n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, C.sections, C'.sections]
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    ((InjectiveResolution.desc (𝟙 F) C'.I C.I).f n)).naturality _ |>.symm

-- Resolution transports cross module-valued and additive-group-valued homology.
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_independent {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (pushforward h).obj F)
    (C C' : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    C.map p = C'.map p := by
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive := sectionsAdditive X
  have : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).Additive := sectionsAdditive Y
  obtain ⟨e, hl, hb⟩ := moduleCohomologyFMapData_comparison h φ C C'
  let ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  let ΓY := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have : ΓY.Additive := inferInstanceAs
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}).Additive
  let HX := ΓX.mapHomologicalComplex (ComplexShape.up ℕ)
  let HY := ΓY.mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let i := H.map (HX.map (InjectiveResolution.desc (𝟙 F) C'.I C.I))
  let j := H.map (HY.map (InjectiveResolution.desc (𝟙 G) C'.J C.J))
  let q := H.map (HY.map e)
  let b := H.map (HY.map C.β)
  let b' := H.map (HY.map C'.β)
  let m := H.map (C.a.hom ≫ HY.map C.lambda)
  let m' := H.map (C'.a.hom ≫ HY.map C'.lambda)
  have : IsIso m := C.invertible p
  have : IsIso m' := C'.invertible p
  have hβ : b ≫ q = j ≫ b' := by
    have hh := (ΓY.mapHomotopy hb.some).homologyMap_eq p
    change H.map (HY.map (C.β ≫ e)) =
      H.map (HY.map (_ ≫ C'.β)) at hh
    simpa only [Functor.map_comp] using hh
  have hlambda : m ≫ q = i ≫ m' := by
    have hh := (ΓY.mapHomotopy hl.some).homologyMap_eq p
    change H.map (HY.map (C.lambda ≫ e)) =
      H.map (HY.map (_ ≫ C'.lambda)) at hh
    dsimp [m, q, i, m']
    rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, ← HY.map_comp,
      hh, HY.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
      sectionsComparison_naturality, Functor.map_comp, Category.assoc]
    rw [Functor.map_comp]
  have hi := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.I C'.I p
  have hj := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C.J C'.J p
  change (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.I p).hom ≫ i =
    (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) C'.I p).hom at hi
  change (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C.J p).hom ≫ j =
    (resolutionSectionsIso
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C'.J p).hom at hj
  have hh := independence_diagram_cancel
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) C.I p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) C'.I p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C.J p)
    (resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) C'.J p)
    b b' m m' i j q hi hj hlambda hβ
  simpa only [b, b', m, m', H, HX, HY, ΓX, ΓY, resolutionSectionsIso,
    ModuleCohomologyFMapData.map,
    RingedSpace.globalSectionsComplex, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hh


private theorem composition_diagram_cancel
    {A B C D E F I J K L M N Q : AddCommGrpCat.{u}}
    (rj : A ≅ B) (rk : A ≅ C) (rc : D ≅ E) (rh : D ≅ F)
    (rg : I ≅ J) (rg' : I ≅ K)
    (bc : B ⟶ L) (bk : C ⟶ M) (bh : K ⟶ N)
    (mc : E ⟶ L) (mk : J ⟶ M) (mh : F ⟶ N)
    [IsIso mc] [IsIso mk] [IsIso mh]
    (i : E ⟶ F) (j : B ⟶ C) (g : J ⟶ K)
    (qc : L ⟶ Q) (qk : M ⟶ Q) (s : N ⟶ Q) [IsIso s]
    (hi : rc.hom ≫ i = rh.hom) (hj : rj.hom ≫ j = rk.hom)
    (hg : rg.hom ≫ g = rg'.hom) (hb : bc ≫ qc = j ≫ bk ≫ qk)
    (hc : mc ≫ qc = i ≫ mh ≫ s) (hk : mk ≫ qk = g ≫ bh ≫ s) :
    rj.hom ≫ bc ≫ inv mc ≫ rc.inv =
      (rk.hom ≫ bk ≫ inv mk ≫ rg.inv) ≫ (rg'.hom ≫ bh ≫ inv mh ≫ rh.inv) := by
  rw [← cancel_mono rh.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hi, Iso.inv_hom_id_assoc]
  rw [← cancel_mono (mh ≫ s)]
  simp only [Category.assoc]
  have hqc : inv mc ≫ i ≫ mh ≫ s = qc := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  have hqk : inv mk ≫ g ≫ bh ≫ s = qk := by
    rw [← hk, IsIso.inv_hom_id_assoc]
  rw [hqc, IsIso.inv_hom_id_assoc, ← hg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hqk, hb, ← Category.assoc, hj]

set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleCohomologyFMap_comp_aux {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (k : Y ⟶ Z) {H : Z.Modules} {G : Y.Modules} {F : X.Modules}
    (ψ : H ⟶ (pushforward k).obj G) (φ : G ⟶ (pushforward h).obj F)
    (Ck : ModuleCohomologyFMapData k H G ψ)
    (Ch : ModuleCohomologyFMapData h G F φ)
    (Cc : ModuleCohomologyFMapData (h ≫ k) H F
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F)) (p : ℕ) :
    Cc.map p = Ck.map p ≫ Ch.map p := by
  let HX := (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let HY := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let HZ := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let Hp := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let i := Hp.map (HX.map (InjectiveResolution.desc (𝟙 F) Ch.I Cc.I))
  let j := Hp.map (HZ.map (InjectiveResolution.desc (𝟙 H) Ck.J Cc.J))
  let g := Hp.map (HY.map (InjectiveResolution.desc (𝟙 G) Ch.J Ck.I))
  let bc := Hp.map (HZ.map Cc.β)
  let bk := Hp.map (HZ.map Ck.β)
  let bh := Hp.map (HY.map Ch.β)
  let mc := Hp.map (Cc.a.hom ≫ HZ.map Cc.lambda)
  let mk := Hp.map (Ck.a.hom ≫ HZ.map Ck.lambda)
  let mh := Hp.map (Ch.a.hom ≫ HY.map Ch.lambda)
  have : IsIso mc := Cc.invertible p
  have : IsIso mk := Ck.invertible p
  have : IsIso mh := Ch.invertible p
  have hd := moduleCohomologyFMap_comp_data h k ψ φ Ck Ch Cc p
  dsimp only at hd
  obtain ⟨Q, qk, qc, s, hs, hb, hc, hk⟩ := hd
  change bc ≫ qc = j ≫ bk ≫ qk at hb
  change mc ≫ qc = i ≫ mh ≫ s at hc
  change mk ≫ qk = g ≫ bh ≫ s at hk
  have : IsIso s := hs
  have hi := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) Cc.I Ch.I p
  have hj := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor Z.toRingedSpace) Cc.J Ck.J p
  have hg := resolutionSectionsIso_naturality
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace) Ck.I Ch.J p
  let rc := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) Cc.I p
  let rh := resolutionSectionsIso (RingedSpace.globalSectionsFunctor X.toRingedSpace) Ch.I p
  let rj := resolutionSectionsIso (RingedSpace.globalSectionsFunctor Z.toRingedSpace) Cc.J p
  let rk := resolutionSectionsIso (RingedSpace.globalSectionsFunctor Z.toRingedSpace) Ck.J p
  let rg := resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) Ck.I p
  let rg' := resolutionSectionsIso (RingedSpace.globalSectionsFunctor Y.toRingedSpace) Ch.J p
  change rc.hom ≫ i = rh.hom at hi
  change rj.hom ≫ j = rk.hom at hj
  change rg.hom ≫ g = rg'.hom at hg
  have hh := composition_diagram_cancel rj rk rc rh rg rg' bc bk bh mc mk mh
    i j g qc qk s hi hj hg hb hc hk
  simpa only [rc, rh, rj, rk, rg, rg', bc, bk, bh, mc, mk, mh, HX, HY, HZ, Hp,
    resolutionSectionsIso, RingedSpace.globalSectionsComplex,
    ModuleCohomologyFMapData.map, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hh


set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} {F : X.Modules}
    (ψ : H ⟶ (pushforward k).obj G) (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    moduleCohomologyFMap (h ≫ k)
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F) p =
        moduleCohomologyFMap k ψ p ≫ moduleCohomologyFMap h φ p := by
  exact moduleCohomologyFMap_comp_aux h k ψ φ
    (Classical.choice (moduleCohomologyFMapData_nonempty k H G ψ))
    (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ))
    (Classical.choice (moduleCohomologyFMapData_nonempty (h ≫ k) H F
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F))) p

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_source_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G' G : Y.Modules} {F : X.Modules} (a : G' ⟶ G)
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology Y.toRingedSpace p).map a) ≫
        moduleCohomologyFMap h φ p = moduleCohomologyFMap h (a ≫ φ) p := by
  have hi := (moduleCohomologyFMap_basic_properties (𝟙 Y) a p).2.2.1 Y G' G a
  have hh := moduleCohomologyFMap_comp h (𝟙 Y) a φ p
  rw [hi] at hh
  have he : a ≫ (pushforward (𝟙 Y)).map φ ≫
      (pushforwardComp h (𝟙 Y)).hom.app F = a ≫ φ := by
    ext U
    rfl
  rw [he] at hh
  exact hh.symm

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F F' : X.Modules} (b : F ⟶ F')
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    moduleCohomologyFMap h φ p ≫ (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map b) =
        moduleCohomologyFMap h (φ ≫ (pushforward h).map b) p := by
  have hi := (moduleCohomologyFMap_basic_properties (𝟙 X) b p).2.2.1 X F F' b
  have hh := moduleCohomologyFMap_comp (𝟙 X) h φ b p
  rw [hi] at hh
  have he : φ ≫ (pushforward h).map b ≫
      (pushforwardComp (𝟙 X) h).hom.app F' = φ ≫ (pushforward h).map b := by
    ext U
    rfl
  rw [he] at hh
  exact hh.symm

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyPullback_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (H : Z.Modules)
    (c : (tensorPullback h).obj ((tensorPullback k).obj H) ⟶
      (tensorPullback (h ≫ k)).obj H)
    (hc : (Classical.choose (exists_tensorPullbackAdjunction k)).unit.app H ≫
      (pushforward k).map
        ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app
          ((tensorPullback k).obj H)) ≫
      (pushforwardComp h k).hom.app
        ((tensorPullback h).obj ((tensorPullback k).obj H)) ≫
      (pushforward (h ≫ k)).map c =
        (Classical.choose (exists_tensorPullbackAdjunction (h ≫ k))).unit.app H)
    (p : ℕ) :
    moduleCohomologyPullback (h ≫ k) H p = moduleCohomologyPullback k H p ≫
      moduleCohomologyPullback h ((tensorPullback k).obj H) p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology X.toRingedSpace p).map c) := by
  unfold moduleCohomologyPullback
  rw [← Category.assoc]
  rw [← moduleCohomologyFMap_comp h k]
  rw [moduleCohomologyFMap_target_naturality]
  simp only [Category.assoc, hc]


private theorem moduleCohomologyFMap_congr {X Y : Scheme.{u}}
    {h k : X ⟶ Y} (e : h = k) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    moduleCohomologyFMap h φ p =
      moduleCohomologyFMap k (φ ≫ (pushforwardCongr e).hom.app F) p := by
  subst k
  have hc : (pushforwardCongr (rfl : h = h)).hom.app F = 𝟙 _ := by
    ext U
    simp
  rw [hc, Category.comp_id]

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_restriction {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} (ψ : H ⟶ (pushforward k).obj G) (V : Z.Opens) :
    ∃ ψV : (restrictFunctor V.ι).obj H ⟶
      (pushforward (k.resLE V (k ⁻¹ᵁ V) le_rfl)).obj
        ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G),
      (restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV ≫
        (pushforwardComp (k.resLE V (k ⁻¹ᵁ V) le_rfl) V.ι).hom.app
          ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) ≫
        (pushforwardCongr (k.resLE_comp_ι (U := V) (V := k ⁻¹ᵁ V) le_rfl)).hom.app
          ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) =
        ψ ≫ (pushforward k).map ((restrictAdjunction (k ⁻¹ᵁ V).ι).unit.app G) ≫
          (pushforwardComp (k ⁻¹ᵁ V).ι k).hom.app
            ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) ∧
      ∀ p : ℕ, moduleCohomologyFMap k ψ p ≫
        moduleCohomologyRestriction (k ⁻¹ᵁ V) G p =
        moduleCohomologyRestriction V H p ≫
          moduleCohomologyFMap (k.resLE V (k ⁻¹ᵁ V) le_rfl) ψV p := by
  let W := k ⁻¹ᵁ V
  let r := k.resLE V W le_rfl
  let GV := (restrictFunctor W.ι).obj G
  let a := (pushforwardComp r V.ι).hom.app GV
  let b := (pushforwardCongr (k.resLE_comp_ι (U := V) (V := W) le_rfl)).hom.app GV
  let t := ψ ≫ (pushforward k).map ((restrictAdjunction W.ι).unit.app G) ≫
    (pushforwardComp W.ι k).hom.app GV
  let ψV := ((restrictAdjunction V.ι).homEquiv H ((pushforward r).obj GV)).symm
    (t ≫ inv b ≫ inv a)
  have hv : (restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV =
      t ≫ inv b ≫ inv a := by
    exact ((restrictAdjunction V.ι).homEquiv H
      ((pushforward r).obj GV)).apply_symm_apply _
  have hs : (restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV ≫
      a ≫ b = t := by
    rw [← Category.assoc, ← Category.assoc, hv]
    simp [Category.assoc]
  refine ⟨ψV, hs, ?_⟩
  intro p
  unfold moduleCohomologyRestriction
  rw [← moduleCohomologyFMap_comp, ← moduleCohomologyFMap_comp]
  have he := moduleCohomologyFMap_congr
    (k.resLE_comp_ι (U := V) (V := W) le_rfl)
    ((restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV ≫ a) p
  change moduleCohomologyFMap (W.ι ≫ k) t p =
    moduleCohomologyFMap (r ≫ V.ι)
      ((restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV ≫ a) p
  rw [he]
  congr 1
  exact hs.symm

end AlgebraicGeometry.Scheme.Modules
