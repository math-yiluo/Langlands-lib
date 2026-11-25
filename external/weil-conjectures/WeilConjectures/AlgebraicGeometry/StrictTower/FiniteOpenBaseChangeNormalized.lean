/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Normalized finite constant-coefficient open base change

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint:
proposition-extension-zero-restriction-closed-subscheme--11).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The square compositor is uniquely determined by its explicit composition formula.
Source: Stacks, Tag 09AE
(blueprint: lem-fix-constant-square-compositor-specification).
Proof: the displayed composite witnesses existence, and the required equality gives uniqueness. -/
theorem moduleSquareG_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ∃! e : modulePullback B i ⋙ modulePullback B r ≅
        modulePullback B p ⋙ modulePullback B k,
      e = (moduleGComp B r i).symm ≪≫ eqToIso (congrArg (modulePullback B) h.symm) ≪≫
        moduleGComp B k p := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

/-- The canonical single-level pullback-square identification.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11). -/
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    modulePullback B i ⋙ modulePullback B r ≅ modulePullback B p ⋙ modulePullback B k :=
  (moduleSquareG_existsUnique B k r p i h).choose

/-- The specified square compositor equals the original explicit composite.
Source: Stacks, Tag 09AE
(blueprint: lem-fix-constant-square-compositor-specification).
Proof: this is the equality clause of the unique specification. -/
theorem moduleSquareG_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG B k r p i h =
      (moduleGComp B r i).symm ≪≫ eqToIso (congrArg (modulePullback B) h.symm) ≪≫
        moduleGComp B k p :=
  (moduleSquareG_existsUnique B k r p i h).choose_spec.1

/-- The inverse open-base-change component, specified by the original open-unit transpose.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11). -/
noncomputable def singleBetaInvApp {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) (M : Modules B U) :
    (moduleJ B j').obj ((modulePullback B a).obj M) ⟶
      (modulePullback B g).obj ((moduleJ B j).obj M) :=
  ((moduleJAdj B j').homEquiv _ _).symm
    ((modulePullback B a).map ((moduleJAdj B j).unit.app M) ≫
      (moduleSquareG B a j' j g h).inv.app ((moduleJ B j).obj M))

/-- Naturality follows from the same open-unit transpose.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11).
Proof: transpose each naturality square under the open adjunction. Naturality of
the open unit and of the pullback-square comparison makes their transposes equal. -/
theorem singleBetaInvApp_naturality {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (M N : Modules B U) (f : M ⟶ N) :
    (moduleJ B j').map ((modulePullback B a).map f) ≫ singleBetaInvApp B a j' j g h N =
      singleBetaInvApp B a j' j g h M ≫
        (modulePullback B g).map ((moduleJ B j).map f) := by
  unfold singleBetaInvApp
  apply (moduleJAdj B j').homEquiv_naturality_right_square
  have hu := (moduleJAdj B j).unit.naturality f
  change f ≫ (moduleJAdj B j).unit.app N =
    (moduleJAdj B j).unit.app M ≫
      (modulePullback B j).map ((moduleJ B j).map f) at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  have hn := (moduleSquareG B a j' j g h).inv.naturality ((moduleJ B j).map f)
  simp only [Functor.comp_map] at hn ⊢
  rw [hn]

/-- The specified inverse comparison, as a natural transformation.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11). -/
noncomputable def singleBetaInv {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    modulePullback B a ⋙ moduleJ B j' ⟶ moduleJ B j ⋙ modulePullback B g where
  app := singleBetaInvApp B a j' j g h
  naturality := singleBetaInvApp_naturality B a j' j g h

-- Transfer the ordinary sheaf comparisons to constant-ring module coordinates.
-- These comparisons are used only to establish membership in the open essential image;
-- the public comparison remains the original open-unit transpose.
section

variable [Finite B] [TopologicalSpace B] [DiscreteTopology B]

set_option backward.isDefEq.respectTransparency false in
private theorem scalarIdentity_isIso (X : Scheme.{u}) :
    IsIso (finiteScalarMap B X B (RingHom.id B)) := by
  let J := Scheme.ProEt.topology X
  let t := scalarUnit B X
  have htI : Presheaf.IsLocallyInjective J t := by
    rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
    infer_instance
  have htS : Presheaf.IsLocallySurjective J t := scalarUnit_surjective B X
  have he : t ≫ (finiteScalarMap B X B (RingHom.id B)).hom =
      finiteCoefficientScalarMap X B := by
    have hi : RingCat.ofHom (RingHom.id B) = 𝟙 (RingCat.of B) := rfl
    have hh := finiteScalarMap_unit B X B (RingHom.id B)
    rw [hi] at hh
    change t ≫ (finiteScalarMap B X B (RingHom.id B)).hom =
      𝟙 _ ≫ finiteCoefficientScalarMap X B at hh
    simpa only [Category.id_comp] using hh
  have hi := (finiteCoefficientScalarMap_locallyBijective X B).1
  have hs := (finiteCoefficientScalarMap_locallyBijective X B).2
  have : Presheaf.IsLocallyInjective J (finiteScalarMap B X B (RingHom.id B)).hom := by
    apply (Presheaf.comp_isLocallyInjective_iff J t _).mp
    rw [he]
    exact hi
  have : Presheaf.IsLocallySurjective J (finiteScalarMap B X B (RingHom.id B)).hom := by
    apply (Presheaf.comp_isLocallySurjective_iff J t _).mp
    rw [he]
    exact hs
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem realization_equivalence (X : Scheme.{u}) :
    (C B X B (RingHom.id B)).IsEquivalence := by
  have := scalarIdentity_isIso B X
  let rc := asIso (finiteScalarMap B X B (RingHom.id B))
  let e := Scheme.proEtaleScalarEquivalence X rc
  let z : finiteRestriction B X B (RingHom.id B) ≅ e.functor := Iso.refl _
  have : (finiteRestriction B X B (RingHom.id B)).IsEquivalence :=
    Functor.isEquivalence_of_iso z.symm
  dsimp only [C]
  infer_instance

attribute [local instance] realization_equivalence

private noncomputable def inverseSquare
    {A₁ A₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    (eA : A₁ ≌ A₂) (eC : C₁ ≌ C₂) (F : A₁ ⥤ C₁) (G : A₂ ⥤ C₂)
    (s : eA.functor ⋙ G ≅ F ⋙ eC.functor) : G ⋙ eC.inverse ≅ eA.inverse ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight eA.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eA.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s eC.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ eC.unitIso.symm ≪≫ Functor.rightUnitor _)

private noncomputable def pullModel {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C B Y B (RingHom.id B) ⋙ modulePullback B f ≅
      upperStar (ModuleCat.{u + 1} B) f ⋙ C B X B (RingHom.id B) :=
  ((C B Y B (RingHom.id B)).asEquivalence.toAdjunction.comp
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))).leftAdjointUniq
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
      (C B X B (RingHom.id B)).asEquivalence.toAdjunction).ofNatIsoRight
        (inverseSquare (C B X B (RingHom.id B)).asEquivalence
          (C B Y B (RingHom.id B)).asEquivalence _ _
          (cDirect B f B (RingHom.id B)).symm).symm)

private noncomputable def restrictionModel {U X : Scheme.{u}} (j : U ⟶ X) :
    modulePullback B j ⋙ (C B U B (RingHom.id B)).asEquivalence.inverse ≅
      (C B X B (RingHom.id B)).asEquivalence.inverse ⋙
        upperStar (ModuleCat.{u + 1} B) j :=
  inverseSquare (C B X B (RingHom.id B)).asEquivalence
    (C B U B (RingHom.id B)).asEquivalence _ _ (pullModel B j)

private noncomputable def openModel {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    C B U B (RingHom.id B) ⋙ moduleJ B j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙ C B X B (RingHom.id B) :=
  ((C B U B (RingHom.id B)).asEquivalence.toAdjunction.comp (moduleJAdj B j)).leftAdjointUniq
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).comp
      (C B X B (RingHom.id B)).asEquivalence.toAdjunction).ofNatIsoRight
        (restrictionModel B j).symm)

private theorem openUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let eX := (C B X B (RingHom.id B)).asEquivalence
  let r := inverseSquare (C B U B (RingHom.id B)).asEquivalence eX
    (openImmersionLowerShriek A j) (moduleJ B j) (openModel B j)
  have : (moduleJ B j ⋙ eX.inverse).Full := Functor.Full.of_iso r.symm
  have : (moduleJ B j ⋙ eX.inverse).Faithful := Functor.Faithful.of_iso r.symm
  have : (moduleJ B j).Full := Functor.Full.of_comp_faithful _ eX.inverse
  have : (moduleJ B j).Faithful := Functor.Faithful.of_comp _ eX.inverse
  infer_instance

private noncomputable def ordinaryOpenSquare {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback a j' j g) :
    openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        upperStar (ModuleCat.{u + 1} B) g ≅
      upperStar (ModuleCat.{u + 1} B) a ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} B) j' :=
  ((conjugateIsoEquiv
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) a).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j'))).symm
    (@asIso _ _ _ _ (baseChangeMap (ModuleCat.{u + 1} B) hsq.toCommSq)
      (isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} B) hsq))).symm

private noncomputable def realizedOpenSquare {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback a j' j g) :
    C B U B (RingHom.id B) ⋙ (moduleJ B j ⋙ modulePullback B g) ≅
      C B U B (RingHom.id B) ⋙ (modulePullback B a ⋙ moduleJ B j') :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openModel B j) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullModel B g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ordinaryOpenSquare B a j' j g hsq) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openModel B j').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullModel B a).symm _ ≪≫
    Functor.associator _ _ _

private theorem openSquare_image {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback a j' j g)
    (M : Modules B U) :
    Nonempty ((modulePullback B g).obj ((moduleJ B j).obj M) ≅
      (moduleJ B j').obj ((modulePullback B a).obj M)) := by
  let e := (C B U B (RingHom.id B)).asEquivalence
  exact ⟨(moduleJ B j ⋙ modulePullback B g).mapIso (e.counitIso.app M).symm ≪≫
    (realizedOpenSquare B a j' j g hsq).app (e.inverse.obj M) ≪≫
    (modulePullback B a ⋙ moduleJ B j').mapIso (e.counitIso.app M)⟩

end

/-- The finite-coefficient canonical comparison is invertible for a cartesian square.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11).
Proof: open localization identifies the right adjoints by restriction on the same
pulled-back test objects. Their left adjoints have the unique unit-preserving
isomorphism. Its inverse has exactly the displayed open-unit transpose, hence is
singleBetaInv. Exactness passes this isomorphism degreewise and through localization. -/
theorem singleBetaInv_isIso [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g h) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have := openUnit_isIso B j
  have := openUnit_isIso B j'
  let ff := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  -- In the open essential image the counit is invertible. The transpose is the
  -- extension of the pulled-back unit and square isomorphism, followed by that counit.
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g h).app M) := by
    obtain ⟨e⟩ := openSquare_image B a j' j g hsq M
    have := (moduleJAdj B j').isIso_counit_app_of_iso e
    change IsIso (singleBetaInvApp B a j' j g h M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The existing finite open-base-change comparison, in constant-ring module coordinates.
Its inverse has the prescribed open-unit transpose; no new map is chosen.
Source: Stacks, Tag 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--11). -/
noncomputable def singleBeta [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) :
    (moduleJ B j).mapDerivedCategory ⋙ (modulePullback B g).mapDerivedCategory ≅
      (modulePullback B a).mapDerivedCategory ⋙ (moduleJ B j').mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (singleBetaInv B a j' j g h)
        (singleBetaInv_isIso B a j' j g h hsq)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale.StrictTower
