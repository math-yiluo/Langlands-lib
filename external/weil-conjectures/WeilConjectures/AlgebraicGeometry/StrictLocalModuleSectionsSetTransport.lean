/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-! # Coefficient and symmetry transport for strict-local sections
Source: Stacks Project, Tags 03D3, 03D7, and 03Q9.
(blueprint: lem-weil-pbc-strict-local-module-sections-set-transport)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The canonical equivalence of strict-local terminal sections after forgetting module
coefficients and interchanging the two pullback factors.
Source: Stacks Project, Tags 03D3, 03D7, and 03Q9.
(blueprint: def-weil-pbc-strict-local-module-sections-set-equiv).
The coefficient comparison, composition of inverse images, restriction along the
pullback symmetry, and terminal/global section comparisons are all actual isomorphisms.
The composition comparison is determined by its unit identity and fixed-sheaf uniqueness.
No existence theorem about sections or stalks is used to choose the equivalence. -/
noncomputable def strictLocalModuleSectionsSetEquiv
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
    ((Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F)) ≃
      ((Scheme.etaleSetPullback
        (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj H).obj.obj
          (op (Scheme.Etale.mk (𝟙 _))) := by
  classical
  let ρ := Scheme.strictLocalizationToBase s
  let A := pullback f ρ
  let B := pullback ρ f
  let g : A ⟶ X := pullback.fst f ρ
  let h : B ⟶ X := pullback.snd ρ f
  let σ : A ⟶ B := (pullbackSymmetry f ρ).hom
  have hσ : σ ≫ h = g := pullbackSymmetry_hom_comp_snd f ρ
  let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
  let M := (upperStar (ModuleCat.{u + 1} Λ) g).obj F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g) (Type (u + 1))
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (A.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let q := (adj.homEquiv H
    ((sheafCompose A.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj M)).symm
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F))
  have : IsIso q := isIso_upperStar_forget_comparison Λ g F
  let c := Classical.choose (etaleSetInverseImageCompositionUnits.{u}).2.2
  let r := Classical.choose (etaleSetInverseImageRestriction σ)
  let T := Scheme.Etale.mk (𝟙 A)
  let T' := Scheme.Etale.mk (𝟙 B)
  let d : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale σ)).obj T ≅
      T' := MorphismProperty.Over.isoMk (pullbackSymmetry f ρ) (by
        change σ ≫ 𝟙 B = 𝟙 A ≫ σ
        exact (Category.comp_id σ).trans (Category.id_comp σ).symm)
  let t := IsTerminal.isTerminalOfObj
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ A) T Over.mkIdTerminal
  let eΓ := (Sheaf.ΓNatIsoSheafSections A.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) t).app M
  let V := sheafToPresheaf A.smallEtaleTopology (Type (u + 1))
  let eq := (V.mapIso (asIso q)).app (op T)
  let eg : (Scheme.etaleSetPullback (σ ≫ h)).obj H ≅
      (Scheme.etaleSetPullback g).obj H :=
    eqToIso (congrArg (fun k ↦ (Scheme.etaleSetPullback k).obj H) hσ)
  let ec := (V.mapIso (((c X B A h σ).app H) ≪≫ eg)).app (op T)
  let er := (V.mapIso (r.app ((Scheme.etaleSetPullback h).obj H))).app (op T)
  let ed := ((Scheme.etaleSetPullback h).obj H).obj.mapIso d.op
  let e0 := (forget (ModuleCat.{u + 1} Λ)).mapIso eΓ
  let e1 := e0 ≪≫ eq.symm ≪≫ ec.symm ≪≫ er ≪≫ ed.symm
  exact e1.toEquiv

private noncomputable abbrev setPullback {R S : Scheme.{u}} (f : S ⟶ R) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev sitePullback {R S : Scheme.{u}} (f : S ⟶ R) :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

private noncomputable abbrev inverseImageUnit (S T : Scheme.{u}) (e : T ⟶ S)
    [(sitePullback e).IsContinuous (S.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (T.smallGrothendieckTopology @AlgebraicGeometry.Etale)] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (sitePullback e)
    (Type (u + 1)) (S.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (T.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The composite unit, restricted along a diagonal, equals the two successive units.
private lemma terminal_unit_lift
    {R S T : Scheme.{u}} (e : S ⟶ R)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale)
    (t : T ⟶ U.left) (v : T ⟶ S) (hp : t ≫ U.hom = v ≫ e) :
    let d : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback (v ≫ e)).obj U :=
      MorphismProperty.Over.homMk (pullback.lift t (𝟙 T) hp) (pullback.lift_snd _ _ _)
    let D : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback v).obj ((sitePullback e).obj U) :=
      MorphismProperty.Over.homMk
        (pullback.lift (pullback.lift t v hp) (𝟙 T)
          (by exact (pullback.lift_snd t v hp).trans (Category.id_comp v).symm))
        (pullback.lift_snd _ _ _)
    ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
        ((setPullback (v ≫ e)).obj H).obj.map d.op ≫
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          R S T e v).app H).inv.hom.app (op (Scheme.Etale.mk (𝟙 T))) =
      ((inverseImageUnit R S e).app H).hom.app (op U) ≫
        ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback
      e).obj U)) ≫
        ((setPullback v).obj ((setPullback e).obj H)).obj.map D.op := by
  dsimp only
  let D : Scheme.Etale.mk (𝟙 T) ⟶ (sitePullback v).obj ((sitePullback e).obj U) :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.lift t v hp) (𝟙 T)
          (by exact (pullback.lift_snd t v hp).trans (Category.id_comp v).symm))
      (pullback.lift_snd _ _ _)
  let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T e v).hom.app H
  change ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
      ((setPullback (v ≫ e)).obj H).obj.map _ ≫
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        R S T e v).app H).inv.hom.app (op (Scheme.Etale.mk (𝟙 T))) =
    ((inverseImageUnit R S e).app H).hom.app (op U) ≫
      ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback e).obj U)) ≫
      ((setPullback v).obj ((setPullback e).obj H)).obj.map D.op
  apply (cancel_mono (β.hom.app (op (Scheme.Etale.mk (𝟙 T))))).1
  have hc : ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
      R S T e v).app H).inv.hom.app (op (Scheme.Etale.mk (𝟙 T))) ≫
      β.hom.app (op (Scheme.Etale.mk (𝟙 T))) = 𝟙 _ :=
    NatTrans.congr_app (congrArg (fun m ↦ m.hom)
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        R S T e v).app H).inv_hom_id) (op (Scheme.Etale.mk (𝟙 T)))
  simp only [Category.assoc, hc, Category.comp_id]
  erw [β.hom.naturality D.op]
  have hu : ((inverseImageUnit R S e).app H).hom.app (op U) ≫
      ((inverseImageUnit S T v).app ((setPullback e).obj H)).hom.app (op ((sitePullback e).obj U)) ≫
      β.hom.app (op ((sitePullback v).obj ((sitePullback e).obj U))) =
    ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
      ((setPullback (v ≫ e)).obj H).obj.map
        ((MorphismProperty.Over.pullbackComp
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v e).inv.app U).op := by
    ext s
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      R S T e v H U s
  erw [Category.assoc, reassoc_of% hu, ← Functor.map_comp, ← op_comp]
  apply congrArg (fun z ↦ ((inverseImageUnit R T (v ≫ e)).app H).hom.app (op U) ≫
    ((setPullback (v ≫ e)).obj H).obj.map z)
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift t (𝟙 T) hp =
    pullback.lift (pullback.lift t v hp) (𝟙 T) _ ≫
      ((MorphismProperty.Over.pullbackComp
        (P := @AlgebraicGeometry.Etale) (Q := ⊤) v e).inv.app U).left
  rw [MorphismProperty.Over.pullbackComp_inv_app_left]
  apply pullback.hom_ext <;> simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Composition and étale restriction transport terminal units along an isomorphism.
private lemma symmetry_unit_transport
    {X A B : Scheme.{u}} (σ : A ≅ B) (h : B ⟶ X) (g : A ⟶ X)
    (hg : σ.hom ≫ h = g) (H : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Etale) (v : B ⟶ U.left) (hv : v ≫ U.hom = h) :
    let dA : Scheme.Etale.mk (𝟙 A) ⟶ (sitePullback g).obj U :=
      MorphismProperty.Over.homMk
        (pullback.lift (σ.hom ≫ v) (𝟙 A) (by
          exact (Category.assoc σ.hom v U.hom).trans
            ((congrArg (fun k ↦ σ.hom ≫ k) hv).trans
              (hg.trans (Category.id_comp g).symm))))
        (pullback.lift_snd _ _ _)
    let dB : Scheme.Etale.mk (𝟙 B) ⟶ (sitePullback h).obj U :=
      MorphismProperty.Over.homMk
        (pullback.lift v (𝟙 B) (by exact hv.trans (Category.id_comp h).symm))
        (pullback.lift_snd _ _ _)
    let c := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 X B A h σ.hom).app H
    let eg : (setPullback (σ.hom ≫ h)).obj H ≅ (setPullback g).obj H :=
      eqToIso (congrArg (fun k ↦ (setPullback k).obj H) hg)
    let r := (Classical.choose (etaleSetInverseImageRestriction σ.hom)).app
      ((setPullback h).obj H)
    let d : (MorphismProperty.Over.map ⊤ (inferInstance : Etale σ.hom)).obj
        (Scheme.Etale.mk (𝟙 A)) ≅ Scheme.Etale.mk (𝟙 B) :=
      MorphismProperty.Over.isoMk σ (by
        change σ.hom ≫ 𝟙 B = 𝟙 A ≫ σ.hom
        exact (Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)
    ((inverseImageUnit X A g).app H).hom.app (op U) ≫
        ((setPullback g).obj H).obj.map dA.op ≫
        eg.inv.hom.app (op (Scheme.Etale.mk (𝟙 A))) ≫
        c.inv.hom.app (op (Scheme.Etale.mk (𝟙 A))) ≫
        r.hom.hom.app (op (Scheme.Etale.mk (𝟙 A))) ≫
        ((setPullback h).obj H).obj.map d.inv.op =
      ((inverseImageUnit X B h).app H).hom.app (op U) ≫
        ((setPullback h).obj H).obj.map dB.op := by
  subst g
  dsimp only
  simp only [eqToIso_refl, Iso.refl_inv, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, Category.id_comp]
  let K := (setPullback h).obj H
  let W := (sitePullback h).obj U
  let D : Scheme.Etale.mk (𝟙 A) ⟶ (sitePullback σ.hom).obj W :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.lift (σ.hom ≫ v) σ.hom
        (by rw [Category.assoc, hv])) (𝟙 A)
        (by
          change pullback.lift (σ.hom ≫ v) σ.hom _ ≫ pullback.snd U.hom h =
            𝟙 A ≫ σ.hom
          rw [pullback.lift_snd, Category.id_comp])) (pullback.lift_snd _ _ _)
  let r := (Classical.choose (etaleSetInverseImageRestriction σ.hom)).app K
  have hu := terminal_unit_lift h H U (σ.hom ≫ v) σ.hom (by rw [Category.assoc, hv])
  dsimp only at hu
  change ((inverseImageUnit X A (σ.hom ≫ h)).app H).hom.app (op U) ≫
      ((setPullback (σ.hom ≫ h)).obj H).obj.map _ ≫
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        X B A h σ.hom).app H).inv.hom.app (op (Scheme.Etale.mk (𝟙 A))) =
    ((inverseImageUnit X B h).app H).hom.app (op U) ≫
      ((inverseImageUnit B A σ.hom).app K).hom.app (op W) ≫
      ((setPullback σ.hom).obj K).obj.map D.op at hu
  rw [reassoc_of% hu]
  erw [reassoc_of% r.hom.hom.naturality D.op]
  have hr : ((inverseImageUnit B A σ.hom).app K).hom.app (op W) ≫
      r.hom.hom.app (op ((sitePullback σ.hom).obj W)) =
    K.obj.map ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ σ.hom
      inferInstance trivial).counit.app W).op := by
    ext z
    exact Classical.choose_spec (etaleSetInverseImageRestriction σ.hom) K W z
  erw [reassoc_of% hr]
  change _ ≫ K.obj.map _ ≫ K.obj.map _ ≫ K.obj.map _ = _ ≫ K.obj.map _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Functor.op_map]
  simp only [← op_comp, Quiver.Hom.unop_op]
  congr 2
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  dsimp [D, MorphismProperty.Over.mapPullbackAdj]
  apply pullback.hom_ext <;> simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting coefficients and interchanging the two pullback factors identifies terminal
sections, compatibly with restriction of a section from any affine pointed neighbourhood.
Source: Stacks Project, Tags 03D3 and 03D7 (inverse images), and Tag 03Q9 (degree zero).
(blueprint: lem-weil-pbc-strict-local-module-sections-set-transport).

Proof: Put S = Spec of the strict henselization, A = X ×_Y S, B = S ×_Y X,
g = A → X, h = B → X, and σ : A → B the pullback symmetry, so σ ≫ h = g.
Write H for the underlying set sheaf and K = h⁻¹H. Expand the equivalence in
strictLocalModuleSectionsSetEquiv. Its global-section comparison cancels the inverse
comparison at the end of the displayed module restriction map. Let q : g⁻¹H → U(g*F)
be the coefficient comparison. By Adjunction.homEquiv_unit, the forgotten module unit
is the set unit followed by q. Naturality of q⁻¹ therefore sends the restricted module
section to the g-unit section restricted to the terminal object of A.
The chosen composition isomorphism c : σ⁻¹(h⁻¹H) ≅ (σ ≫ h)⁻¹H satisfies its unit
formula by Classical.choose_spec etaleSetInverseImageCompositionUnits. After transport
along σ ≫ h = g, naturality of c⁻¹ sends that restricted g-unit section to the iterated
h-unit and σ-unit section, restricted along the terminal-to-iterated-pullback map.
The chosen restriction comparison r : σ⁻¹K ≅ K restricted along σ satisfies the unit
formula of Classical.choose_spec (etaleSetInverseImageRestriction σ). Use its naturality
to move the preceding restriction past r; its unit formula replaces the σ-unit by
restriction along the fibre-product projection. Finally the inverse sheaf map at the
terminal-object isomorphism induced by σ transports evaluation from A → B to B → B.
The composite restriction map is strictHenselizationSectionMap f s j: compare both
projections using pullback.lift_fst, pullback.lift_snd, the pullbackComp projection
identities, and pullbackSymmetry_hom_comp_snd. Functoriality gives the displayed equation.
No step uses qcqs, nonempty schemes, or nonzero coefficients. -/
theorem strictLocalModuleSections_set_transport
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
    ∀ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))
        (z : F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)))),
        strictLocalModuleSectionsSetEquiv Λ f s F (ConcreteCategory.hom (
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) z) =
          ((Scheme.etaleSetPullback
            (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj H).obj.map
              (Scheme.strictHenselizationSectionMap f s j).op
                (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                  (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
                    (pullback.snd (Scheme.strictLocalizationToBase s) f))
                  (Type (u + 1)) (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
                ((pullback (Scheme.strictLocalizationToBase s) f).smallGrothendieckTopology
                    @AlgebraicGeometry.Etale)).unit.app H).hom.app
                      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
                        ((equivSmallModel.{u}
                          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) z)
    := by
  classical
  dsimp only
  intro j z
  let ρ := Scheme.strictLocalizationToBase s
  let A := pullback f ρ
  let B := pullback ρ f
  let g : A ⟶ X := pullback.fst f ρ
  let h : B ⟶ X := pullback.snd ρ f
  let σ : A ⟶ B := (pullbackSymmetry f ρ).hom
  have hσ : σ ≫ h = g := pullbackSymmetry_hom_comp_snd f ρ
  let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
  let M := (upperStar (ModuleCat.{u + 1} Λ) g).obj F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g) (Type (u + 1))
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (A.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let q := (adj.homEquiv H
    ((sheafCompose A.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj M)).symm
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F))
  have : IsIso q := isIso_upperStar_forget_comparison Λ g F
  let c := Classical.choose (etaleSetInverseImageCompositionUnits.{u}).2.2
  let r := Classical.choose (etaleSetInverseImageRestriction σ)
  let T := Scheme.Etale.mk (𝟙 A)
  let T' := Scheme.Etale.mk (𝟙 B)
  let d : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale σ)).obj T ≅
      T' := MorphismProperty.Over.isoMk (pullbackSymmetry f ρ) (by
        change σ ≫ 𝟙 B = 𝟙 A ≫ σ
        exact (Category.comp_id σ).trans (Category.id_comp σ).symm)
  let t := IsTerminal.isTerminalOfObj
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ A) T Over.mkIdTerminal
  let eΓ := (Sheaf.ΓNatIsoSheafSections A.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) t).app M
  let V := sheafToPresheaf A.smallEtaleTopology (Type (u + 1))
  let eq := (V.mapIso (asIso q)).app (op T)
  let eg : (Scheme.etaleSetPullback (σ ≫ h)).obj H ≅
      (Scheme.etaleSetPullback g).obj H :=
    eqToIso (congrArg (fun k ↦ (Scheme.etaleSetPullback k).obj H) hσ)
  let ec := (V.mapIso (((c X B A h σ).app H) ≪≫ eg)).app (op T)
  let er := (V.mapIso (r.app ((Scheme.etaleSetPullback h).obj H))).app (op T)
  let ed := ((Scheme.etaleSetPullback h).obj H).obj.mapIso d.op
  let e0 := (forget (ModuleCat.{u + 1} Λ)).mapIso eΓ
  let e1 := e0 ≪≫ eq.symm ≪≫ ec.symm ≪≫ er ≪≫ ed.symm
  let U := f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
  let v := Scheme.strictHenselizationBaseChangeMap f s j
  have hv : v ≫ U.hom = h := by
    exact pullback.lift_snd _ _ _
  let dA : T ⟶ (sitePullback g).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift (σ ≫ v) (𝟙 A) (by
        exact (Category.assoc σ v U.hom).trans
          ((congrArg (fun k ↦ σ ≫ k) hv).trans
            (hσ.trans (Category.id_comp g).symm))))
      (pullback.lift_snd _ _ _)
  let ηm := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app
    (op U)
  let ηg := ((inverseImageUnit X A g).app H).hom.app (op U)
  let ηh := ((inverseImageUnit X B h).app H).hom.app (op U)
  have hq : ηg ≫ q.hom.app (op ((sitePullback g).obj U)) =
      (forget (ModuleCat.{u + 1} Λ)).map ηm := by
    have hh := (adj.homEquiv H
      ((sheafCompose A.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj M)).apply_symm_apply
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F))
    exact NatTrans.congr_app (congrArg (fun a ↦ a.hom) hh) (op U)
  have hcoeff : (forget (ModuleCat.{u + 1} Λ)).map ηm ≫
      (forget (ModuleCat.{u + 1} Λ)).map (M.obj.map dA.op) ≫ eq.inv =
      ηg ≫ ((setPullback g).obj H).obj.map dA.op := by
    erw [← hq]
    erw [Category.assoc, ← reassoc_of% q.hom.naturality dA.op]
    change ηg ≫ ((setPullback g).obj H).obj.map dA.op ≫ eq.hom ≫ eq.inv = _
    erw [eq.hom_inv_id, Category.comp_id]
  have hsym := symmetry_unit_transport (pullbackSymmetry f ρ) h g hσ H U v hv
  dsimp only at hsym
  have htransport : (forget (ModuleCat.{u + 1} Λ)).map ηm ≫
      (forget (ModuleCat.{u + 1} Λ)).map (M.obj.map dA.op) ≫
      eq.inv ≫ ec.inv ≫ er.hom ≫ ed.inv =
    ηh ≫ ((setPullback h).obj H).obj.map (Scheme.strictHenselizationSectionMap f s j).op := by
    erw [reassoc_of% hcoeff]
    exact hsym
  have hc0 : (forget (ModuleCat.{u + 1} Λ)).map eΓ.inv ≫ e0.hom = 𝟙 _ :=
    e0.inv_hom_id
  have hall : (forget (ModuleCat.{u + 1} Λ)).map
      (ηm ≫ M.obj.map dA.op ≫ eΓ.inv) ≫ e1.hom =
      ηh ≫ ((setPullback h).obj H).obj.map
        (Scheme.strictHenselizationSectionMap f s j).op := by
    erw [(forget (ModuleCat.{u + 1} Λ)).map_comp ηm (M.obj.map dA.op ≫ eΓ.inv),
      (forget (ModuleCat.{u + 1} Λ)).map_comp (M.obj.map dA.op) eΓ.inv]
    simp only [Category.assoc]
    simp only [e1, Iso.trans_hom, Iso.symm_hom]
    erw [reassoc_of% hc0]
    exact htransport
  unfold strictLocalModuleSectionsSetEquiv
  change e1.toEquiv (ConcreteCategory.hom
    (ηm ≫ M.obj.map dA.op ≫ eΓ.inv) z) = _
  have hf := ConcreteCategory.congr_hom hall z
  simp only [types_comp_apply] at hf
  exact hf

end AlgebraicGeometry.Etale
