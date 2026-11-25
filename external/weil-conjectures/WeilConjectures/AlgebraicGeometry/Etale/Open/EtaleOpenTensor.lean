/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenKFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaAssoc
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleFlat

/-! # Canonical étale open tensor and coefficient comparisons

Source: Stacks Tags 0GL1, 0E8I, 06YY, 03EL, 03DI and 0E8J
(blueprint: lem-coef-etale-open-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem canonicalGammaZero_isIso
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : Sheaf U.smallEtaleTopology C) (T : Sheaf X.smallEtaleTopology C) :
    IsIso (canonicalGammaZero C j P T) := by
  let adj := openImmersionLowerShriekUpperStarAdjunction C j
  have : (j)_!open[C].Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : (j)_!open[C].Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (adj.counit.app ((j)_!open[C].obj P ⊗ T)) :=
    adj.isIso_counit_app_of_iso (etaleLowerShriekTensorIso C inferInstance P T).symm
  unfold canonicalGammaZero
  rw [Adjunction.homEquiv_counit]
  infer_instance

private theorem open_flat_preserved
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (hP : etaleFlat U A P) :
    etaleFlat X A ((j)_!open[ModuleCat.{u + 1} A].obj P) := by
  apply (Scheme.etaleConstantModule_flat_iff X A _).mp
  exact Functor.PreservesFlat.flat_obj
    (F := etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance)
    ((Scheme.etaleConstantModule_flat_iff U A P).mpr hP)

private theorem projection_transport_assoc
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G S : D ⥤ C} (a : F ⊣ G) [S.Monoidal] (e : S ≅ G)
    (δ : (((Functor.whiskeringLeft₂ C).obj G).obj S).obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj G).obj (curriedTensor D))
    (hδ : ∀ X Y, (δ.app X).app Y = e.inv.app X ▷ S.obj Y ≫
      Functor.LaxMonoidal.μ S X Y ≫ e.hom.app (X ⊗ Y))
    (P : C) (T₁ T₂ : D) :
    let γ : ∀ (K : C) (M : D), F.obj (K ⊗ G.obj M) ⟶ F.obj K ⊗ M :=
      fun K M ↦ F.map (K ◁ e.inv.app M) ≫
      ((a.projectionMap S (curriedTensor C) (curriedTensor D) δ).app K).app M
    F.map ((α_ P (G.obj T₁) (G.obj T₂)).hom ≫
      P ◁ (G.obj T₁ ◁ e.inv.app T₂ ≫ (δ.app T₁).app T₂)) ≫ γ P (T₁ ⊗ T₂) =
      γ (P ⊗ G.obj T₁) T₂ ≫ γ P T₁ ▷ T₂ ≫ (α_ (F.obj P) T₁ T₂).hom := by
  let := Functor.Monoidal.transport e
  let γ : ∀ (K : C) (M : D), F.obj (K ⊗ G.obj M) ⟶ F.obj K ⊗ M :=
    fun K M ↦ F.map (K ◁ e.inv.app M) ≫
    ((a.projectionMap S (curriedTensor C) (curriedTensor D) δ).app K).app M
  have hm (X Y : D) : Functor.LaxMonoidal.μ G X Y =
      G.obj X ◁ e.inv.app Y ≫ (δ.app X).app Y := by
    rw [Functor.Monoidal.transport_μ, hδ, tensorHom_def']
    simp only [Category.assoc]
  have hg (K : C) (M : D) : γ K M =
      ((a.projectionMap G (curriedTensor C) (curriedTensor D)
        (Functor.LaxMonoidal.μNatTrans G)).app K).app M := by
    dsimp only [γ]
    rw [Adjunction.projectionMap_app_app, Adjunction.projectionMap_app_app,
      Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    change F.map (K ◁ _) ≫ (F.map ((a.unit.app K ▷ _) ≫ _) ≫ a.counit.app _) =
      F.map ((a.unit.app K ▷ _) ≫ Functor.LaxMonoidal.μ G _ M) ≫ a.counit.app _
    rw [← Functor.map_comp_assoc, hm]
    congr 2
    change K ◁ e.inv.app M ≫ a.unit.app K ▷ S.obj M ≫ (δ.app (F.obj K)).app M =
      a.unit.app K ▷ G.obj M ≫ G.obj (F.obj K) ◁ e.inv.app M ≫ _
    rw [whisker_exchange_assoc]
    rfl
  have ha (X M M' : D) :
      (α_ (G.obj X) (G.obj M) (G.obj M')).hom ≫
        G.obj X ◁ Functor.LaxMonoidal.μ G M M' ≫
        Functor.LaxMonoidal.μ G X (M ⊗ M') ≫ G.map (α_ X M M').inv =
      Functor.LaxMonoidal.μ G X M ▷ G.obj M' ≫
        Functor.LaxMonoidal.μ G (X ⊗ M) M' := by
    rw [Functor.LaxMonoidal.associativity_inv, Iso.hom_inv_id_assoc]
  have h := a.projectionMap_assoc G (Functor.LaxMonoidal.μNatTrans G) ha P T₁ T₂
  simp only [← hg, hm] at h
  change F.map _ ≫ γ P _ = γ _ _ ≫ γ _ _ ▷ _ ≫ _
  rw [Functor.map_comp]
  apply (cancel_mono (α_ (F.obj P) T₁ T₂).inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    curriedTensor_obj_obj] using h

section ExactTensorCoherence

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
  {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) [AlgebraicGeometry.IsOpenImmersion j]

private theorem canonicalGammaExact_assoc
    (P : DerivedCategory (Sheaf U.smallEtaleTopology C))
    (T₁ T₂ : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (D((j)_!open[C])).map
        ((derivedTensorAssociator (C) U P
            ((D((j)^*[C])).obj T₁) ((D((j)^*[C])).obj T₂)).hom ≫
          ((derivedTensor (C) U).obj P).map
            (openExactRestrictionTensor (C) j T₁ T₂).hom) ≫
        canonicalGammaExact (C) j P
          (((derivedTensor (C) X).obj T₁).obj T₂) =
      canonicalGammaExact (C) j
          (((derivedTensor (C) U).obj P).obj
            ((D((j)^*[C])).obj T₁)) T₂ ≫
        ((derivedTensor (C) X).map
          (canonicalGammaExact (C) j P T₁)).app T₂ ≫
        (derivedTensorAssociator (C) X
          ((D((j)_!open[C])).obj P) T₁ T₂).hom := by
  let := leftDerivedUpperStarMonoidal C j
  have hμ (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
      ((leftDerivedUpperStarTensorNatIso C j).inv.app K).app M =
        Functor.LaxMonoidal.μ L((j)^*[C]) K M := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ L((j)^*[C]) K M),
      Functor.Monoidal.μ_δ]
    exact congr_app (congr_app (leftDerivedUpperStarTensorNatIso C j).inv_hom_id K) M
  have hδ (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
      ((mapDerivedCategoryUpperStarDerivedTensorIso C j).hom.app K).app M =
        (leftDerivedUpperStarIsoMapDerivedCategory C j).inv.app K ▷ L((j)^*[C]).obj M ≫
          Functor.LaxMonoidal.μ L((j)^*[C]) K M ≫
            (leftDerivedUpperStarIsoMapDerivedCategory C j).hom.app (K ⊗ M) := by
    rw [← hμ]
    rfl
  have h := projection_transport_assoc
    (derivedOpenImmersionLowerShriekUpperStarAdjunction C j)
    (leftDerivedUpperStarIsoMapDerivedCategory C j)
    (mapDerivedCategoryUpperStarDerivedTensorIso C j).hom hδ P T₁ T₂
  simpa only [canonicalGammaExact, derivedOpenImmersionLowerShriekProjectionMap,
    openExactRestrictionTensor, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, derivedTensor, derivedTensorAssociator_eq, derivedTensor_obj_map,
    derivedTensor_map_app, curriedTensor_obj_obj, curriedTensor_obj_map,
    curriedTensor_map_app] using h

end ExactTensorCoherence

private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem scalarOpenInverseMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))) =
      ((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv := by
  rw [uniq_eq_conjugate]
  exact
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

private theorem scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : DerivedCategoryModule A X) :
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj T) ≫
        (derivedExtension (A := B) j).map ((openScalarRestriction φ j).hom.app T) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj T) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)
  have h := mateEquiv_counit_symm a b α T
  have hm : ((mateEquiv a b).symm α) = (openScalarExtension φ j).inv :=
    scalarOpenInverseMate a b x u (openDerivedRestrictScalarsIso φ j)
  change _ = ((mateEquiv a b).symm α).app _ ≫ _ at h
  rw [hm] at h
  change (derivedExtension (A := B) j).map ((openScalarRestriction φ j).hom.app T) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).counit.app
        ((scalarExtension φ X).obj T) =
    (openScalarExtension φ j).inv.app ((derivedRestriction (A := A) j).obj T) ≫
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) at h
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ (openScalarExtension φ j).hom.app
      ((derivedRestriction (A := A) j).obj T) ≫ t) h

private theorem scalar_restricts
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : DerivedCategoryModule A U) :
    (derivedRestriction (A := B) j).map ((openScalarExtension φ j).hom.app P) ≫
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).unit.app _)).inv =
      (openScalarRestriction φ j).inv.app ((derivedExtension (A := A) j).obj P) ≫
        (scalarExtension φ U).map
          (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app P)).inv := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)
  have h := unit_mateEquiv_symm a b α P
  have hm : ((mateEquiv a b).symm α) = (openScalarExtension φ j).inv :=
    scalarOpenInverseMate a b x u (openDerivedRestrictScalarsIso φ j)
  change _ = b.unit.app _ ≫ (derivedRestriction (A := B) j).map
    (((mateEquiv a b).symm α).app P) at h
  rw [hm] at h
  let l := asIso (b.unit.app ((scalarExtension φ U).obj P)) ≪≫
    (derivedRestriction (A := B) j).mapIso ((openScalarExtension φ j).symm.app P)
  let r := (scalarExtension φ U).mapIso (asIso (a.unit.app P)) ≪≫
    (openScalarRestriction φ j).app ((derivedExtension (A := A) j).obj P)
  have hh : l.hom = r.hom := by
    change r.hom = l.hom at h
    exact h.symm
  have hi := congrArg Iso.inv (Iso.ext hh)
  simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.symm_inv, a, b] using hi

/-- The full open tensor/coefficient assertion. Every comparison in these laws is
fixed above, or is a published canonical scalar tensor/composition comparison.
Source: Stacks 0GL1, 0E8I, 06YY, 03EL, 03DI, 0E8J
(blueprint: lem-coef-etale-open-tensor). -/
structure EtaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop where
  gamma_isIso : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    IsIso (canonicalGamma j P T)
  ordinary_tensor : ∀ (P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
    IsIso (canonicalGammaZero (ModuleCat.{u + 1} A) j P T)
  flat_preserved : ∀ P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
    etaleFlat U A P → etaleFlat X A ((j)_!open[ModuleCat.{u + 1} A].obj P)
  kflat_preserved : ∀ P : CochainComplex
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat U A P → etaleKFlat X A
      (((j)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj P)
  q_normalized : OpenScalarExtensionNormalization φ j (openScalarExtension φ j)
  q_unique : ∀ q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j,
    OpenScalarExtensionNormalization φ j q → q = openScalarExtension φ j
  r_normalized : OpenScalarRestrictionNormalization φ j (openScalarRestriction φ j)
  r_unique : ∀ r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j,
    OpenScalarRestrictionNormalization φ j r → r = openScalarRestriction φ j
  q_restricts : ∀ P : DerivedCategoryModule A U,
    (derivedRestriction (A := B) j).map ((openScalarExtension φ j).hom.app P) ≫
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).unit.app _)).inv =
      (openScalarRestriction φ j).inv.app ((derivedExtension (A := A) j).obj P) ≫
        (scalarExtension φ U).map
          (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app P)).inv
  counit : ∀ T : DerivedCategoryModule A X,
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj T) ≫
        (derivedExtension (A := B) j).map ((openScalarRestriction φ j).hom.app T) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj T) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T)
  tensor_associative : ∀ (P : DerivedCategoryModule A U)
      (T₁ T₂ : DerivedCategoryModule A X),
    (derivedExtension (A := A) j).map
        ((derivedTensorAssociator (ModuleCat.{u + 1} A) U P
            ((derivedRestriction j).obj T₁) ((derivedRestriction j).obj T₂)).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) U).obj P).map
            (openExactRestrictionTensor (ModuleCat.{u + 1} A) j T₁ T₂).hom) ≫
        canonicalGammaExact (ModuleCat.{u + 1} A) j P
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj T₁).obj T₂) =
      canonicalGammaExact (ModuleCat.{u + 1} A) j
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj
            ((derivedRestriction j).obj T₁)) T₂ ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          (canonicalGammaExact (ModuleCat.{u + 1} A) j P T₁)).app T₂ ≫
        (derivedTensorAssociator (ModuleCat.{u + 1} A) X
          ((derivedExtension j).obj P) T₁ T₂).hom
  successive_scalar : ∀ {C : Type (u + 1)} [CommRing C] (ψ : B →+* C)
      (P : DerivedCategoryModule A U),
    (scalarExtension ψ X).map ((openScalarExtension φ j).hom.app P) ≫
        (openScalarExtension ψ j).hom.app ((scalarExtension φ U).obj P) ≫
        (derivedExtension (A := C) j).map
          ((ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app P) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((derivedExtension (A := A) j).obj P) ≫
        (openScalarExtension (ψ.comp φ) j).hom.app P
  mixed_tensor_scalar : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) ≫
        (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison U φ P ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T)

/-- The canonical open comparisons obey the projection, K-flat normalization,
open counit, associativity, scalar-tower and mixed tensor/scalar laws.
Source: Stacks 0GL1, 0E8I, 06YY, 03EL, 03DI, 0E8J
(blueprint: lem-coef-etale-open-tensor).

Proof: (1) Localize the small étale site at the open object. The ordinary
adjunction has sectionwise identity unit on U and the specified counit summand
formula. (2) Transpose the unit tensored with restriction. This gives `γ⁰`,
whose restriction is the identity; both sides have open support, so it is an
isomorphism. (3) Tensoring a short exact sequence, restricting, and applying
exact extension by zero proves preservation of flat sheaves. Applying the same
isomorphism to every bidegree of direct-sum total tensor proves preservation of
K-flat complexes. Restriction also preserves K-flatness: test with an acyclic
complex on U, extend by zero, and restrict back using the invertible unit.
(4) The exact open adjunction descends degreewise; its units and counits are
those of the published derived adjunction. A K-flat resolution computes the
published `canonicalGamma`, proving invertibility without boundedness.
(5) Specialize inverse ordinary projection to the coefficient sheaf B; its
pure-tensor formula is j_!p tensor b maps to j_!(p tensor b). The scalar
adjunction shows it is precisely `openScalarExtensionZero`. Restriction of
ordinary balancing is `openScalarRestrictionZero`. Apply both degreewise to
K-flat models. The exact localization factors and published scalar counits give
the two normalization equations. Every derived object has a K-flat resolution;
naturality on that resolution determines each component, proving uniqueness.
(6) On the same models the restriction identity and counit equation send every
extension-presheaf tensor generator to the same section. Sheafification and
localization give the displayed equalities. (7) Rebracket triple total tensors:
the differential signs on both sides are 1, (-1)^p and (-1)^(p+q). Both paths
of `tensor_associative` send the same local tensor generator to the same tensor.
(8) In a tower A to B to C the canonical composition comparison multiplies
coefficients, ((p tensor b) tensor c) maps to p tensor bc. Applying q directly
or successively gives the same result. (9) The mixed square uses the published
uniquely normalized strong scalar tensor comparison, sending
(p tensor b₁) tensor (t tensor b₂) to (p tensor t) tensor b₁b₂.
Either path commutes with the open projection on these generators. Descend all
three equalities using the K-flat model comparisons. The argument applies to
arbitrary coefficient maps and unbounded complexes. -/
theorem etaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenTensorComparisons φ j := by
  have hscalar := etaleOpenScalarComparisons φ j
  refine
    { gamma_isIso := ?_
      ordinary_tensor := canonicalGammaZero_isIso _ j
      flat_preserved := open_flat_preserved j
      kflat_preserved := etaleOpenKFlat j
      q_normalized := hscalar.q_normalized
      q_unique := hscalar.q_unique
      r_normalized := hscalar.r_normalized
      r_unique := hscalar.r_unique
      q_restricts := scalar_restricts φ j
      counit := scalar_counit φ j
      tensor_associative := canonicalGammaExact_assoc _ j
      successive_scalar := hscalar.successive_scalar
      mixed_tensor_scalar := hscalar.mixed_tensor_scalar }
  intro P T
  dsimp only [canonicalGamma]
  infer_instance

end AlgebraicGeometry.Etale
