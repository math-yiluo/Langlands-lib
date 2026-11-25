/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly

/-! # Proper/open coordinates before compactification coherence

The ordinary section comparisons identify the supplied operations with the
canonical semilinear model. Derived transport uses exact localization and the
canonical right-derived comparisons, before any finite evaluation.
Source: blueprint gluing proof, Local pairs and Levels.
(blueprint: lem-sp-geometric-proper-open-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual lifted quotient rings for the graph construction, with index n meaning n+1.
Source: Local pairs, coefficient convention
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))

/-- The adjacent quotient maps, lifted without changing coefficients.
Source: Local pairs, coefficient convention
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphTransitions (n : ℕ) : graphRings l E (n + 1) ⟶ graphRings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))

/-- Section-preserving ordinary presentations and direct-image comparisons for the
existing graph model. Units and counits are pinned as functions on sections.
The push square agrees levelwise with the given ordinaryPushEvaluation isomorphism,
allowing arbitrary carrier presentations without an independent scalar twist.
Source: Local pairs, section-model and graph construction
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
structure GraphCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) where
  presentation : ∀ T : Scheme.{u}, SpTowerShriek.S l E T ≌
    SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T
  [additive : ∀ T : Scheme.{u}, (presentation T).functor.Additive]
  [inverseAdditive : ∀ T : Scheme.{u}, (presentation T).inverse.Additive]
  sections : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.obj M).val.obj V) (M.val.obj V)
  restrictions : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T)
    {V W : (ℕ × T.ProEt)ᵒᵖ} (a : V ⟶ W),
    HEq (((presentation T).functor.obj M).val.map a) (M.val.map a)
  morphisms : ∀ (T : Scheme.{u}) {M N : SpTowerShriek.S l E T} (a : M ⟶ N)
    (V : (ℕ × T.ProEt)ᵒᵖ), HEq (((presentation T).functor.map a).val.app V) (a.val.app V)
  unit_sections : ∀ (T : Scheme.{u}) (M : SpTowerShriek.S l E T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).unitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  counit_sections : ∀ (T : Scheme.{u})
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).counitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  push : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (presentation X).inverse ⋙ (o.geometry f).push ⋙ (presentation Y).functor ≅
      SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f
  /-- Compatibility with the supplied ordinary evaluation iso, on all component sections.
  Both sides are functions; no equality with the input section's carrier is required. -/
  push_evaluation : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X)
    (n : ℕ) (V : Y.ProEtᵒᵖ),
    HEq (fun x ↦ ((push f).hom.app M).val.app (op (n, V.unop)) x)
      (fun x ↦ (((o.geometry f).ordinaryPushEvaluation n).hom.app
        ((presentation X).inverse.obj M)).val.app V x)

attribute [instance] GraphCoordinates.additive GraphCoordinates.inverseAdditive

/-- Remove an ordinary conjugation using only the presentation's fixed unit.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphForward (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o) {X Y : Scheme.{u}}
    (F : SpTowerShriek.S l E X ⥤ SpTowerShriek.S l E Y)
    (G : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X ⥤
      SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) Y)
    (a : (g.presentation X).inverse ⋙ F ⋙ (g.presentation Y).functor ≅ G) :
    F ⋙ (g.presentation Y).functor ≅ (g.presentation X).functor ⋙ G :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (g.presentation X).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ a

/-- Pullback comparison uniquely preserving the section-normalized geometric adjunction.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphPullCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (g.presentation Y).inverse ⋙ (o.geometry f).pull ⋙ (g.presentation X).functor ≅
      SemilinearProperOpen.pull (graphRings l E) (graphTransitions l E) f :=
  ((((g.presentation Y).symm.toAdjunction.comp (o.geometry f).ordinaryAdjunction).comp
    (g.presentation X).toAdjunction).ofNatIsoRight (g.push f)).leftAdjointUniq
      (SemilinearProperOpen.ordinaryAdj (graphRings l E) (graphTransitions l E) f)

/-- Open extension comparison obtained from the specified ordinary adjunctions.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphOpenCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    (g.presentation U).inverse ⋙ (o.openOp j).extension ⋙ (g.presentation T).functor ≅
      SemilinearProperOpen.extension (graphRings l E) (graphTransitions l E) j :=
  ((((g.presentation U).symm.toAdjunction.comp (o.openOp j).ordinaryAdjunction).comp
    (g.presentation T).toAdjunction).ofNatIsoRight
      (graphPullCoordinates l E b o g j)).leftAdjointUniq
        (SemilinearProperOpen.ordinaryOpenAdj (graphRings l E) (graphTransitions l E) j)

attribute [local implicit_reducible] VaryingRing.coefficientTransition

private abbrev SS (T : Scheme.{u})
    (σ : ∀ n, SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) :=
  SemilinearSections.Systems.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T) σ

private noncomputable abbrev EE (T : Scheme.{u})
    (σ : ∀ n, SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T) σ

private noncomputable abbrev σgraph (T : Scheme.{u}) :=
  SemilinearProperOpen.transition (graphRings l E) (graphTransitions l E) T

private noncomputable def graphPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f ≅
      VaryingRing.push (graphRings l E) (graphTransitions l E) f :=
  SheafOfModules.pushforwardCongr
    (SemilinearProperOpen.coefficientMap_forget_eq (graphRings l E) (graphTransitions l E) f)

-- Keep the adjacent maps abstract until the equality transport is performed once.
set_option maxHeartbeats 900000 in
-- The section pins compare functors on large coefficient-system categories.
private structure OrdinaryModel
    (σ : ∀ T : Scheme.{u}, ∀ n,
      SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) where
  presentation : ∀ T : Scheme.{u}, SS l E T (σ T) ≌
    SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T
  [additive : ∀ T, (presentation T).functor.Additive]
  [inverseAdditive : ∀ T, (presentation T).inverse.Additive]
  sections : ∀ T (M : SS l E T (σ T)) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.obj M).val.obj V) (M.val.obj V)
  restrictions : ∀ T (M : SS l E T (σ T)) {V W : (ℕ × T.ProEt)ᵒᵖ} (a : V ⟶ W),
    HEq (((presentation T).functor.obj M).val.map a) (M.val.map a)
  morphisms : ∀ T {M N : SS l E T (σ T)} (a : M ⟶ N) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.map a).val.app V) (a.val.app V)
  unit_sections : ∀ T (M : SS l E T (σ T)) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).unitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  counit_sections : ∀ T
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).counitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  push : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (SS l E X (σ X) ⥤ SS l E Y (σ Y))
  evalP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    push f ⋙ EE l E Y (σ Y) n ≅
      EE l E X (σ X) n ⋙ proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  horizontal : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : SS l E X (σ X))
    {m n : ℕ} (h : n ≤ m) (V : Y.ProEtᵒᵖ)
    (x : ((EE l E Y (σ Y) m).obj ((push f).obj M)).val.obj V),
    ((evalP f n).hom.app M).val.app V
        (SpTowerShriek.HS l E Y (σ Y) h ((push f).obj M) V x) =
      SpTowerShriek.HS l E X (σ X) h M (SpTowerShriek.chart f V)
        (((evalP f m).hom.app M).val.app V x)
  comparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : SS l E X (σ X) ⥤ SS l E Y (σ Y)) (_d : G ≅ push f),
    (presentation X).inverse ⋙ G ⋙ (presentation Y).functor ≅
      SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f
  comparison_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : SS l E X (σ X) ⥤ SS l E Y (σ Y)) (d : G ≅ push f)
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X)
    (n : ℕ) (V : Y.ProEtᵒᵖ),
    HEq (fun x ↦ ((comparison f G d).hom.app M).val.app (op (n, V.unop)) x)
      (fun x ↦ (((EE l E Y (σ Y) n).map
        (d.hom.app ((presentation X).inverse.obj M)) ≫
        (evalP f n).hom.app ((presentation X).inverse.obj M)).val.app V x))

attribute [local instance] OrdinaryModel.additive OrdinaryModel.inverseAdditive

set_option maxHeartbeats 900000 in
-- Equality transport identifies the full coefficient-system presentation.
private noncomputable def ordinaryModel
    (σ : ∀ T : Scheme.{u}, ∀ n,
      SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n)
    (hσ : σ = σgraph l E) : OrdinaryModel l E σ := by
  subst σ
  refine {
    presentation := fun _ ↦ CategoryTheory.Equivalence.refl
    additive := fun _ ↦ { map_add := by intros; rfl }
    inverseAdditive := fun _ ↦ { map_add := by intros; rfl }
    sections := fun _ _ _ ↦ HEq.rfl
    restrictions := fun _ _ _ _ _ ↦ HEq.rfl
    morphisms := fun _ _ _ _ _ ↦ HEq.rfl
    unit_sections := fun _ _ _ ↦ HEq.rfl
    counit_sections := fun _ _ _ ↦ HEq.rfl
    push := fun f ↦ VaryingRing.push (graphRings l E) (graphTransitions l E) f
    evalP := fun f n ↦ VaryingRing.moduleEvalP (graphRings l E) (graphTransitions l E) f n
    horizontal := fun {X Y} f M {m n} h V x ↦
      SpTowerShriek.canonicalPushHorizontal (graphRings l E) (graphTransitions l E) f M h V x
    comparison := fun f G d ↦
      Functor.leftUnitor _ ≪≫ Functor.rightUnitor _ ≪≫ d ≪≫ (graphPushIso l E f).symm
    comparison_sections := ?_ }
  intro X Y f G d M n V
  apply heq_of_eq
  funext x
  change ((d.hom.app M).val.app (op (n, V.unop)) x) =
    ((VaryingRing.moduleEvalP (graphRings l E) (graphTransitions l E) f n).hom.app M).val.app V
      ((d.hom.app M).val.app (op (n, V.unop)) x)
  exact ((VaryingRing.moduleEvalP_existsUnique
    (graphRings l E) (graphTransitions l E) f n).choose_spec.1 M V.unop _).symm

-- Cancellation compares horizontal morphisms on large module-sheaf categories.
-- Assemble the level isomorphisms and check their naturality on every section.
/-- Derived proper/open transport uses the ordinary section square and the canonical
right-derived composition maps. No arbitrary derived comparison is selected.
Source: Local pairs, graph comparison (blueprint: lem-sp-geometric-proper-open-coordinates). -/
def graphSupportCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U T : Scheme.{u}} {e : U ⟶ T} (c : Compactification e) :
    SpTowerShriek.F l E b o c ⋙ (g.presentation T).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        SemilinearProperOpen.J (graphRings l E) (graphTransitions l E) c.i ⋙
        SemilinearProperOpen.R (graphRings l E) (graphTransitions l E) c.g :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
      Functor.rightDerivedFunctorNatIso (graphForward l E b o g _ _ (g.push c.g)) ≪≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (graphForward l E b o g _ _ (graphOpenCoordinates l E b o g c.i)) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
