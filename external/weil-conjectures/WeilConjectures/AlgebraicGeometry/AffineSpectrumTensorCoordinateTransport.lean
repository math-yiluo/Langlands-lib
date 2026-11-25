/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumTensorCoherentCoordinateData

/-! # Affine coordinate transport of the localized tensor comparison

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local irreducible] isoPullbackAdditiveStalkIso
  Scheme.Modules.tensorPullbackCompositionIso


/-- Ordinary pullback transports additive stalk homology along an isomorphism.
This is constructed from the restriction-stalk isomorphism on complexes and exact
stalk homology factors; it uses no derived pullback or derived pullback counit.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport). -/
def ordinaryIsoPullbackStalkHomologyIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :=
  letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  letI : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  let E := Scheme.Modules.tensorPullback j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  F.mapIso (comparisonStalkHomologyIso Z (j y) P i).symm ≪≫
    (additiveStalkCohomologyFactors Z (j y) i).app P ≪≫
    H.mapIso ((NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y)
      (.up ℤ)).app P) ≪≫
    H.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S))
      (.up ℤ)).symm.app P) ≪≫
    (additiveStalkCohomologyFactors Y y i).symm.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    F0.mapIso (comparisonStalkHomologyIso Y y
      ((E.mapHomologicalComplex (.up ℤ)).obj P) i)

private theorem restrict_forget_homology {R S : Type u} [CommRing R] [CommRing S] (e : R →+* S)
    (V : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    let T := ModuleCat.restrictScalars.{u} e
    let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
    H.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ F)) (.up ℤ)).hom.app V) ≫
      ((complexForgetHomologyIso S i).app V).hom =
    ((complexForgetHomologyIso R i).app ((T.mapHomologicalComplex (.up ℤ)).obj V)).hom ≫
      F.map ((V.sc i).mapHomologyIso T).hom := by
  dsimp only
  let T := ModuleCat.restrictScalars.{u} e
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let h := (V.sc i).homologyData.left
  change H.map ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (T ⋙ F)) (.up ℤ)).hom.app V) ≫ ((V.sc i).mapHomologyIso F0).hom =
    (((V.sc i).map T).mapHomologyIso F).hom ≫ F.map ((V.sc i).mapHomologyIso T).hom
  have hk : (h.map F0).cyclesIso.hom = ((h.map T).map F).cyclesIso.hom := by
    apply (cancel_mono (F0.map h.i)).mp
    exact (h.map F0).cyclesIso_hom_comp_i.trans
      ((h.map T).map F).cyclesIso_hom_comp_i.symm
  have hm : (h.map F0).homologyIso.hom = ((h.map T).map F).homologyIso.hom := by
    apply (cancel_epi (((V.sc i).map F0).homologyπ)).mp
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
    exact congrArg (fun k ↦ k ≫ F0.map h.π) hk
  rw [h.mapHomologyIso_eq T, (h.map T).mapHomologyIso_eq F, h.mapHomologyIso_eq F0]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hm]
  erw [F.map_id, Category.id_comp]
  congr 1

-- The expanded stalk comparison requires a larger elaboration budget.
private theorem ordinary_homology_eq {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    let SZ := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
    let SY := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
    let E := Scheme.Modules.tensorPullback j
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
    (ordinaryIsoPullbackStalkHomologyIso j y i P).hom =
      ((complexForgetHomologyIso _ i).app
        ((SZ.mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      H.map (ordinaryIsoPullbackStalkComplexIso j y P).hom ≫
      ((complexForgetHomologyIso _ i).app
        ((SY.mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P))).hom := by
  dsimp only [ordinaryIsoPullbackStalkHomologyIso, ordinaryIsoPullbackStalkComplexIso,
    additiveStalkCohomologyFactors, comparisonStalkHomologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [show (Functor.mapHomologicalComplexCompIso
    (Iso.refl (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y) ⋙
      forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}))
      (.up ℤ)).hom.app P = 𝟙 _ by ext k; rfl, Category.id_comp]


attribute [local irreducible] ordinaryIsoPullbackStalkComplexIso
  ordinaryIsoPullbackStalkHomologyIso

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- Transport a commuting diagram with three arrows along its vertex isomorphisms. -/
private theorem transport_three_comp_of_coherence
    {D : Type u} [Category.{w} D]
    {A B C Z E F A' B' C' Z' E' F' : D}
    (c : A ≅ A') (cr : B ≅ B') (c0 : C ≅ C')
    (ca : Z ≅ Z') (cs : E ≅ E') (ce : F ≅ F')
    (t : A ⟶ B) (v : B ⟶ C) (s0 : C ⟶ Z)
    (s : A ⟶ E) (u : E ⟶ F) (a : F ⟶ Z)
    (t' : A' ⟶ B') (v' : B' ⟶ C') (s0' : C' ⟶ Z')
    (s' : A' ⟶ E') (u' : E' ⟶ F') (a' : F' ⟶ Z')
    (nt : t ≫ cr.hom = c.hom ≫ t')
    (nr : v ≫ c0.hom = cr.hom ≫ v')
    (ns0 : s0 ≫ ca.hom = c0.hom ≫ s0')
    (ns : s ≫ cs.hom = c.hom ≫ s')
    (na : a ≫ ca.hom = ce.hom ≫ a')
    (nu : u' = cs.inv ≫ u ≫ ce.hom)
    (hc : t ≫ v ≫ s0 = s ≫ u ≫ a) :
    t' ≫ v' ≫ s0' = s' ≫ u' ≫ a' := by
  apply (cancel_epi c.hom).mp
  rw [← reassoc_of% nt, ← reassoc_of% nr, ← ns0, nu, ← reassoc_of% ns]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← na]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ ca.hom) hc

/-- The homology transport equation for supplied affine coordinate data.
Source: Stacks Project, Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-homology-pointwise).
Proof: apply homology to the supplied canonical chain coherence. Naturality of the
exact forget-homology comparison moves each chain map across that comparison.
Restriction followed by forgetting agrees with forgetting at the level of homology
data. The ordinary pullback homology map is the conjugate of its chain comparison.
Cancel the source comparison and evaluate on each class. -/
theorem affineSpectrum_tensor_coordinate_homology_transport_pointwise
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let j := X'.isoSpec.inv
    let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let alpha := (NatIso.mapHomologicalComplex
      ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso j g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
      (.up ℤ)).app P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    ∀ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      ((∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x))) →
      (F.mapHomologicalComplex (.up ℤ)).map t.hom ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.restrictScalars.{u} eD.toRingHom ⋙ F)) (.up ℤ)).hom.app V0 ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom =
        (F.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso f f' g g' sq z P).hom ≫
          (ordinaryIsoPullbackStalkComplexIso j z0 Pg).hom ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) →
      ∀ x, (F.map (HomologicalComplex.homologyMap t.hom i) ≫
          F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} eD.toRingHom)).hom ≫
          F0.map (HomologicalComplex.homologyMap
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom i)).hom x =
        (F.map (HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i) ≫
          (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom ≫
          F0.map (HomologicalComplex.homologyMap
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i)).hom x := by
  intro z P0 Pg j S0 F F0 alpha R0 A0 B0 D0 Q Q0 V0
    eR eA eB eD q t h hc x
  let V := tensorComplex f f' g g' sq z P
  let s := (tensorStalkIso f f' g g' sq z P).hom
  let s0 := (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom
  let a := (S0.mapHomologicalComplex (.up ℤ)).map alpha.inv
  let T := ModuleCat.restrictScalars.{u} eD.toRingHom
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let F0c := F0.mapHomologicalComplex (.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let c := (complexForgetHomologyIso (C z) i).app V
  let cr := (complexForgetHomologyIso (C z) i).app
    ((T.mapHomologicalComplex (.up ℤ)).obj V0)
  let c0 := (complexForgetHomologyIso (C z0) i).app V0
  let cs := (complexForgetHomologyIso (C z) i).app
    (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)).obj Pg)
  let ce := (complexForgetHomologyIso (C z0) i).app
    ((S0.mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Pg))
  let ca := (complexForgetHomologyIso (C z0) i).app
    ((S0.mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj P0))
  let v := (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ F)) (.up ℤ)).hom.app V0
  let u := (ordinaryIsoPullbackStalkComplexIso j z0 Pg).hom
  have nt : H.map (Fc.map t.hom) ≫ cr.hom =
      c.hom ≫ F.map (HomologicalComplex.homologyMap t.hom i) :=
    (complexForgetHomologyIso (C z) i).hom.naturality t.hom
  have ns : H.map (Fc.map s) ≫ cs.hom =
      c.hom ≫ F.map (HomologicalComplex.homologyMap s i) :=
    (complexForgetHomologyIso (C z) i).hom.naturality s
  have ns0 : H.map (F0c.map s0) ≫ ca.hom =
      c0.hom ≫ F0.map (HomologicalComplex.homologyMap s0 i) :=
    (complexForgetHomologyIso (C z0) i).hom.naturality s0
  have na : H.map (F0c.map a) ≫ ca.hom =
      ce.hom ≫ F0.map (HomologicalComplex.homologyMap a i) :=
    (complexForgetHomologyIso (C z0) i).hom.naturality a
  have nr : H.map v ≫ c0.hom =
      cr.hom ≫ F.map ((V0.sc i).mapHomologyIso T).hom :=
    restrict_forget_homology eD.toRingHom V0 i
  have nu : (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom =
      cs.inv ≫ H.map u ≫ ce.hom := ordinary_homology_eq j z0 i Pg
  have hh : F.map (HomologicalComplex.homologyMap t.hom i) ≫
      F.map ((V0.sc i).mapHomologyIso T).hom ≫
      F0.map (HomologicalComplex.homologyMap s0 i) =
      F.map (HomologicalComplex.homologyMap s i) ≫
      (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom ≫
      F0.map (HomologicalComplex.homologyMap a i) := by
    apply transport_three_comp_of_coherence c cr c0 ca cs ce
      (H.map (Fc.map t.hom)) (H.map v) (H.map (F0c.map s0))
      (H.map (Fc.map s)) (H.map u) (H.map (F0c.map a))
      _ _ _ _ _ _ nt nr ns0 ns na nu
    simpa only [Functor.map_comp] using congrArg H.map hc
  exact congrArg (fun k ↦ k.hom x) hh


/-- (blueprint: lem-pc-affine-spectrum-tensor-coordinate-homology)
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport) -/
theorem affineSpectrum_tensor_coordinate_homology_transport
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let j := X'.isoSpec.inv
    let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let alpha := (NatIso.mapHomologicalComplex
      ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso j g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
      (.up ℤ)).app P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    ∀ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      ((∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x))) →
      (F.mapHomologicalComplex (.up ℤ)).map t.hom ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.restrictScalars.{u} eD.toRingHom ⋙ F)) (.up ℤ)).hom.app V0 ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom =
        (F.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso f f' g g' sq z P).hom ≫
          (ordinaryIsoPullbackStalkComplexIso j z0 Pg).hom ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) →
      F.map (HomologicalComplex.homologyMap t.hom i) ≫
          F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} eD.toRingHom)).hom ≫
          F0.map (HomologicalComplex.homologyMap
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom i) =
        F.map (HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i) ≫
          (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom ≫
          F0.map (HomologicalComplex.homologyMap
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i) := by
  dsimp
  intro eR eA eB eD q t h hc
  ext x
  exact affineSpectrum_tensor_coordinate_homology_transport_pointwise
    f f' g g' sq sq0 z0 i P eR eA eB eD q t h hc x


/-- Affine spectrum tensor coordinate transport, assembled from the data and homology sublemmas.
Source: Stacks Project, Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport). -/
theorem exists_affineSpectrum_tensor_coordinates
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let j := X'.isoSpec.inv
    let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let alpha := (NatIso.mapHomologicalComplex
      ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso j g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
      (.up ℤ)).app P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) ∧
      F.map (HomologicalComplex.homologyMap t.hom i) ≫
          F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} eD.toRingHom)).hom ≫
          F0.map (HomologicalComplex.homologyMap
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom i) =
        F.map (HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i) ≫
          (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom ≫
          F0.map (HomologicalComplex.homologyMap
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i) := by
  obtain ⟨eR, eA, eB, eD, q, t, hA, hB, hD, ht, hc⟩ :=
    exists_affineSpectrum_tensor_coherent_coordinate_data f f' g g' sq sq0 z0 i P
  refine ⟨eR, eA, eB, eD, q, t, hA, hB, hD, ht, ?_⟩
  exact affineSpectrum_tensor_coordinate_homology_transport f f' g g' sq sq0 z0 i P
    eR eA eB eD q t ⟨hA, hB, hD, ht⟩ hc

end AlgebraicGeometry.SingleComplexBaseChange
