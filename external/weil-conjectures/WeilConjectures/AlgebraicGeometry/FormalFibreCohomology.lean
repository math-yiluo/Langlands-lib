/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties

/-! # Infinitesimal fibre cohomology and its canonical stalk maps

Source: Stacks Project, Cohomology of Schemes, Lemma 02OD; Cohomology, Tags 01FB, 01E4
(blueprint: def-weil-pbc-formal-fibre-cohomology).

Natural index n denotes the positive infinitesimal level n+1. The cohomology modules
retain the action of the quotient of the base local ring, and of its completion.
The canonical stalk maps are characterized by the predicate `IsFormalFunctionsTheta`.
-/

@[expose] public section

universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- The positive power defining an infinitesimal fibre.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
abbrev formalFibreIdeal (Y : Scheme.{uF}) (y : Y) (n : ℕ) :=
  maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)

/-- The canonical map Spec(O_y/m_y^(n+1)) → Spec O_y → Y.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreBaseMap (Y : Scheme.{uF}) (y : Y) (n : ℕ) :
    Spec (CommRingCat.of ((Y.presheaf.stalk y) ⧸ formalFibreIdeal Y y n)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n))) ≫
    Y.fromSpecStalk y

/-- The infinitesimal fibre Spec(O_y/m_y^(n+1)) ×_Y X, the chosen fibre product.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibre {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) : Scheme.{uF} :=
  pullback (formalFibreBaseMap Y y n) f

/-- The projection i_n to X, used for tensor pullback of F.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreι {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibre f y n ⟶ X :=
  pullback.snd (formalFibreBaseMap Y y n) f

/-- Base quotient scalars act via the first projection and the Gamma-Spec isomorphism.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreScalarMap {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    ((Y.presheaf.stalk y) ⧸ formalFibreIdeal Y y n) →+* Γ(formalFibre f y n, ⊤) :=
  ((Scheme.ΓSpecIso
    (CommRingCat.of ((Y.presheaf.stalk y) ⧸ formalFibreIdeal Y y n))).inv ≫
      (pullback.fst (formalFibreBaseMap Y y n) f).appTop).hom

/-- The reduction Spec(O_y/m_y^(n+1)) → Spec(O_y/m_y^(n+2)) lies over Y.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology).
Proof: the factor map composed with the quotient map is the smaller quotient map, and
Spec reverses composition. -/
theorem formalFibreBaseMap_transition (Y : Scheme.{uF}) (y : Y) (n : ℕ) :
    formalFibreBaseMap Y y n =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factorPow (maximalIdeal (Y.presheaf.stalk y))
          (Nat.le_succ (n + 1)))) ≫ formalFibreBaseMap Y y (n + 1) := by
  rw [formalFibreBaseMap, formalFibreBaseMap]
  rw [← Category.assoc, ← Spec.map_comp]
  congr

/-- The closed immersion j_n : X_n → X_(n+1), the base change of the reduction map.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreTransition {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibre f y n ⟶ formalFibre f y (n + 1) :=
  pullback.map (formalFibreBaseMap Y y n) f (formalFibreBaseMap Y y (n + 1)) f
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factorPow (maximalIdeal (Y.presheaf.stalk y)) (Nat.le_succ (n + 1)))))
    (𝟙 X) (𝟙 Y)
    (by rw [Category.comp_id, ← formalFibreBaseMap_transition])
    (by rw [Category.comp_id, Category.id_comp])

/-- The transition followed by the projection to X is the earlier projection.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology).
Proof: the second projection of pullback.map is the second projection followed by 𝟙. -/
theorem formalFibreTransition_ι {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreι f y n = formalFibreTransition f y n ≫ formalFibreι f y (n + 1) := by
  simp [formalFibreTransition, formalFibreι]

private theorem eval_factorPow {R : Type uF} [CommRing R] (I : Ideal R)
    (n : ℕ) (a : AdicCompletion I R) :
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
      (AdicCompletion.evalₐ I (n + 2) a) = AdicCompletion.evalₐ I (n + 1) a := by
  induction a using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow]
    simpa using AdicCompletion.Ideal.mk_eq_mk I (Nat.le_succ (n + 1)) a

private theorem scalarMap_transition {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (n : ℕ) (a : (Y.presheaf.stalk y) ⧸ formalFibreIdeal Y y (n + 1)) :
    (formalFibreTransition f y n).appTop.hom (formalFibreScalarMap f y (n + 1) a) =
      formalFibreScalarMap f y n
        (Ideal.Quotient.factorPow (maximalIdeal (Y.presheaf.stalk y))
          (Nat.le_succ (n + 1)) a) := by
  let q := CommRingCat.ofHom
    (Ideal.Quotient.factorPow (maximalIdeal (Y.presheaf.stalk y))
      (Nat.le_succ (n + 1)))
  have h : formalFibreTransition f y n ≫
      pullback.fst (formalFibreBaseMap Y y (n + 1)) f =
      pullback.fst (formalFibreBaseMap Y y n) f ≫ Spec.map q := by
    simp [formalFibreTransition, q]
  have hΓ := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at hΓ
  have hs := Scheme.ΓSpecIso_inv_naturality q
  have hc : (Scheme.ΓSpecIso _).inv ≫
      (pullback.fst (formalFibreBaseMap Y y (n + 1)) f).appTop ≫
        (formalFibreTransition f y n).appTop =
      q ≫ (Scheme.ΓSpecIso _).inv ≫
        (pullback.fst (formalFibreBaseMap Y y n) f).appTop := by
    rw [hΓ, ← Category.assoc, ← hs, Category.assoc]
  exact congrArg (fun k ↦ k.hom a) hc

private theorem completedScalarMap_transition {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (n : ℕ)
    (a : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    (formalFibreTransition f y n).appTop.hom
      (formalFibreScalarMap f y (n + 1)
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2) a)) =
      formalFibreScalarMap f y n
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) a) := by
  rw [scalarMap_transition, eval_factorPow]

/-- The transition h-map F_(n+1) → j_n* F_n: the adjoint, for the canonical
tensor-pullback adjunction of i_(n+1), of the unit of i_n followed by the composition
identification of direct images. It is the adjoint of the canonical identification
j_n^* F_(n+1) ≅ F_n fixed by the adjunction units.
Source: Stacks, Tags 02OD, 01F7, 0096 (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreTransitionFMap {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (n : ℕ) :
    (Scheme.Modules.tensorPullback (formalFibreι f y (n + 1))).obj F ⟶
      (Scheme.Modules.pushforward (formalFibreTransition f y n)).obj
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (formalFibreι f y (n + 1)))).homEquiv F _).symm
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (formalFibreι f y n))).unit.app F ≫
      (Scheme.Modules.pushforwardCongr (formalFibreTransition_ι f y n)).hom.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) ≫
      (Scheme.Modules.pushforwardComp (formalFibreTransition f y n)
        (formalFibreι f y (n + 1))).inv.app
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))

/-- H^p(X_n, F_n) as a module over the completed base local ring; its action factors
through the quotient by m_y^(n+1).
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreCohomology {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p n : ℕ) :
    ModuleCat.{uF} (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :=
  (ModuleCat.restrictScalars ((formalFibreScalarMap f y n).comp
    (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom)).obj
      ((RingedSpace.moduleCohomology (formalFibre f y n).toRingedSpace p).obj
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))

/-- H^p(X_n, F_n) as a module over the uncompleted local ring O_(Y,y).
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreCohomologyLocal {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace))
    (p n : ℕ) : ModuleCat.{uF} (Y.presheaf.stalk y) :=
  (ModuleCat.restrictScalars ((formalFibreScalarMap f y n).comp
    (Ideal.Quotient.mk (formalFibreIdeal Y y n)))).obj
      ((RingedSpace.moduleCohomology (formalFibre f y n).toRingedSpace p).obj
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))

/-- The cohomology j_n-map H^p(X_(n+1), F_(n+1)) → H^p(X_n, F_n) on the underlying groups.
Source: Stacks, Tags 02OD, 01FB (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreCohomologyTransitionAddHom {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p n : ℕ) :
    formalFibreCohomology f y F p (n + 1) →+ formalFibreCohomology f y F p n :=
  (Scheme.Modules.moduleCohomologyFMap (formalFibreTransition f y n)
    (formalFibreTransitionFMap f y F n) p).hom

private theorem cohomologyFMap_smul {X Y : Scheme.{uF}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (Scheme.Modules.pushforward h).obj F)
    (p : ℕ) (a : Γ(Y, ⊤)) (x : (Y.toRingedSpace.moduleCohomology p).obj G) :
    (Scheme.Modules.moduleCohomologyFMap h φ p).hom (a • x) =
      h.appTop.hom a •
        (show (X.toRingedSpace.moduleCohomology p).obj F from
          (Scheme.Modules.moduleCohomologyFMap h φ p).hom x) := by
  obtain ⟨L, hL⟩ :=
    (Scheme.Modules.moduleCohomologyFMap_basic_properties h (G := G) (F := F) φ p).1
  have he : L.hom.toAddMonoidHom = (Scheme.Modules.moduleCohomologyFMap h φ p).hom :=
    congrArg (fun k ↦ k.hom) hL
  have hs := L.hom.map_smul a x
  change L.hom (a • x) = h.appTop.hom a • L.hom x at hs
  rw [← he]
  exact hs

/-- The cohomology j_n-map is linear over the completed local ring.
Source: Stacks, Tags 02OD, 01FB (blueprint: def-weil-pbc-formal-fibre-cohomology).
Proof: maps on cohomology induced by h-maps are linear over global sections of the
target (module-cohomology-fmap-basic-properties); the scalars of A/m^(n+2) act on X_(n+1)
and on X_n through j_n, compatibly with reduction to A/m^(n+1), and the completed ring
acts through these quotients. -/
theorem formalFibreCohomologyTransition_smul {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p n : ℕ)
    (a : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    (x : formalFibreCohomology f y F p (n + 1)) :
    formalFibreCohomologyTransitionAddHom f y F p n (a • x) =
      a • formalFibreCohomologyTransitionAddHom f y F p n x := by
  have h := cohomologyFMap_smul (formalFibreTransition f y n)
    (G := (Scheme.Modules.tensorPullback (formalFibreι f y (n + 1))).obj F)
    (F := (Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)
    (formalFibreTransitionFMap f y F n) p
    (formalFibreScalarMap f y (n + 1)
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2) a)) x
  rw [completedScalarMap_transition] at h
  exact h

/-- The transition H^p(X_(n+1), F_(n+1)) → H^p(X_n, F_n): the cohomology j_n-map,
as a map of modules over the completed local ring.
Source: Stacks, Tags 02OD, 01FB (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreCohomologyTransition {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p n : ℕ) :
    formalFibreCohomology f y F p (n + 1) ⟶ formalFibreCohomology f y F p n :=
  ModuleCat.ofHom (X := formalFibreCohomology f y F p (n + 1))
    (Y := formalFibreCohomology f y F p n)
    { toFun := formalFibreCohomologyTransitionAddHom f y F p n
      map_add' := map_add (formalFibreCohomologyTransitionAddHom f y F p n)
      map_smul' := formalFibreCohomologyTransition_smul f y F p n }

/-- The inverse system of fibre cohomology, in modules over the completed local ring.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreCohomologySystem {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{uF}
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :=
  Functor.ofOpSequence (formalFibreCohomologyTransition f y F p)

/-- The stalk M = (R^p f_* F)_y, with its O_(Y,y)-module structure.
Source: Stacks, Tag 02OD (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
abbrev formalFunctionsStalk {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : SheafOfModules.{uF} (moduleRings X.toRingedSpace)) (p : ℕ) :=
  (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
    (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F)

/-- theta_n : M → H^p(X_n, F_n) is the canonical stalk map: for every open V ∋ y, the
germ of the canonical class (Stacks 01E4) of a cohomology class xi on f⁻¹V goes to the
class whose restriction to the inverse image W of f⁻¹V in X_n (all of X_n) is the
cohomology pullback of xi along W → f⁻¹V. Restriction to W = X_n is injective and these
germs exhaust M, so the predicate determines theta_n.
Source: Stacks, Tags 02OD, 01E4, 01FB (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def IsFormalFunctionsTheta {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p n : ℕ)
    (θ : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n) : Prop :=
  ∀ (I : InjectiveResolution F)
    (J : InjectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))
    (V : Y.Opens) (hy : y ∈ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (formalFibreBaseMap Y y n) F I J V)
    (xi : (forget₂ _ AddCommGrpCat.{uF}).obj
      ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
    Scheme.Modules.moduleCohomologyFMap ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((Scheme.Modules.restrictAdjunction ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)) p
      (θ (TopCat.Presheaf.germ
        (((Scheme.Modules.pushforward f).rightDerived p).obj F).presheaf V y hy
        ((Scheme.Modules.resolutionSectionClass D.source.resolution
          (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex) V D.source.sections p ≫
          Scheme.Modules.Hom.app
            (I.isoRightDerivedObj (Scheme.Modules.pushforward f) p).inv V) xi))) =
    Scheme.Modules.moduleCohomologyFMap ((formalFibreι f y n).resLE (f ⁻¹ᵁ V)
      ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi

/-- Global sections Γ(X_n, O) as a module over the completed local ring.
Source: Stacks, Tag 02OD, p=0 (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreSections {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    ModuleCat.{uF} (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :=
  (ModuleCat.restrictScalars ((formalFibreScalarMap f y n).comp
    (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom)).obj
      (ModuleCat.of Γ(formalFibre f y n, ⊤) Γ(formalFibre f y n, ⊤))

/-- Section pullback Γ(X_(n+1), O) → Γ(X_n, O) along j_n on the underlying groups.
Source: Stacks, Tag 02OD, p=0 (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreSectionsTransitionAddHom {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreSections f y (n + 1) →+ formalFibreSections f y n :=
  (formalFibreTransition f y n).appTop.hom.toAddMonoidHom

/-- Section pullback along j_n is linear over the completed local ring.
Source: Stacks, Tag 02OD, p=0 (blueprint: def-weil-pbc-formal-fibre-cohomology).
Proof: j_n lies over the reduction A/m^(n+2) → A/m^(n+1); the maps from the completed
ring to the two quotients commute with reduction, and appTop is a ring map. -/
theorem formalFibreSectionsTransition_smul {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    (x : formalFibreSections f y (n + 1)) :
    formalFibreSectionsTransitionAddHom f y n (a • x) =
      a • formalFibreSectionsTransitionAddHom f y n x := by
  change Γ(formalFibre f y (n + 1), ⊤) at x
  change (formalFibreTransition f y n).appTop.hom
      (formalFibreScalarMap f y (n + 1)
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2) a) * x) =
    formalFibreScalarMap f y n
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) a) *
        (formalFibreTransition f y n).appTop.hom x
  rw [map_mul, completedScalarMap_transition]

/-- Section pullback Γ(X_(n+1), O) → Γ(X_n, O) along j_n, a completed-ring-linear map.
Source: Stacks, Tag 02OD, p=0 (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreSectionsTransition {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreSections f y (n + 1) ⟶ formalFibreSections f y n :=
  ModuleCat.ofHom (X := formalFibreSections f y (n + 1)) (Y := formalFibreSections f y n)
    { toFun := formalFibreSectionsTransitionAddHom f y n
      map_add' := map_add (formalFibreSectionsTransitionAddHom f y n)
      map_smul' := formalFibreSectionsTransition_smul f y n }

/-- The inverse system of actual global sections Γ(X_n, O_(X_n)).
Source: Stacks, Tag 02OD, p=0 (blueprint: def-weil-pbc-formal-fibre-cohomology). -/
def formalFibreSectionsSystem {X Y : Scheme.{uF}} (f : X ⟶ Y) (y : Y) :
    ℕᵒᵖ ⥤ ModuleCat.{uF}
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :=
  Functor.ofOpSequence (formalFibreSectionsTransition f y)

end AlgebraicGeometry
