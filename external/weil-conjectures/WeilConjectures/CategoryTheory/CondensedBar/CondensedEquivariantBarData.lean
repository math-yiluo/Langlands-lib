/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Condensed.Equivalence
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-! # Internal profinite actions and compatible bar models

Source: the formal internal-bar expansion of paragraph (3) of the main-20261015
six-functors direct-image proof (blueprint: def-sfb-condensed-equivariant-bar-data).
The action is on all continuous generalized elements and is compatible with restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- Commutative ring objects on the profinite site, with the recorded coefficient size.
Source: blueprint condensed rings (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev Ring := CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})

/-- The recorded internal module category, without a copied module structure.
Source: blueprint module objects (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev Modules (A : Ring.{u}) :=
  Profinite.CondensedAction.Modules A.toMon

/-- The existing section-module equivalence, used to express generalized-element formulas.
Source: Stacks 00YV (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev sectionsFunctor (A : Ring.{u}) :=
  InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) A.X

/-- The section ring of an internal condensed ring.
Source: Stacks 00YV (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev sectionRing (A : Ring.{u}) (S : Profinite.{u}) :=
  (InternalAbelianSheafModule.sectionRingSheaf
    (coherentTopology Profinite.{u}) A.X).obj.obj (op S)

/-- Sections of the actual module sheaf associated to an internal module.
Source: Stacks 00YV (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev sections (A : Ring.{u}) (M : Modules A) (S : Profinite.{u}) :=
  M.X.obj.obj (op S)

/-- The section-module structure transported by the recorded equivalence.
Source: Stacks 00YV (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance sectionModule (A : Ring.{u}) (M : Modules A) (S : Profinite.{u}) :
    Module (sectionRing A S) (sections A M S) :=
  (((sectionsFunctor A).obj M).val.obj (op S)).isModule

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The bundled commutativity proof on the underlying condensed ring.
Source: commutative monoid objects (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance ringComm (A : Ring.{u}) : IsCommMonObj A.toMon.X := A.comm

/-- The landed internal-action category, specialized to the bundled commutative ring.
Source: internal-action definitions (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev Equivariant (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] := Profinite.CondensedAction.ActionModule A.toMon G

variable {A G}

/-- The existing internal-action forgetful functor.
Source: internal-action definitions (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev forgetAction {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Equivariant A G ⥤ Modules A :=
  Profinite.CondensedAction.forgetAction (R := A.toMon) (P := G)

/-- Forgetting an action retains addition of the underlying maps.
Source: internal-action definitions (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance forgetAction_additive : (forgetAction (A := A) (G := G)).Additive where
  map_add := by intros; rfl

/-- Generalized functions on a profinite parameter, over every base change of S.
Source: the free/internal-Hom adjunction (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev FunctionFamily (M : Modules A) (P S : Profinite.{u}) :=
  ∀ (T : Profinite.{u}), (T ⟶ S) → C(T, P) → sections A M T

/-- A generalized function commutes with every profinite base change.
Source: the free/internal-Hom adjunction (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def FunctionFamily.IsNatural {M : Modules A} {P S : Profinite.{u}}
    (c : FunctionFamily M P S) : Prop :=
  ∀ (T V : Profinite.{u}) (f : T ⟶ S) (k : V ⟶ T) (g : C(T, P)),
    M.X.obj.map k.op (c T f g) = c V (k ≫ f) (g.comp k.hom.hom)

/-- A profinite power, including the terminal power in degree zero.
Source: the internal bar formula (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev power (G : Type u) [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (n : ℕ) : Profinite.{u} := Profinite.of (Fin n → G)

/-- A tuple of continuous maps is the corresponding continuous map to a profinite power.
Source: the internal bar formula (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def tupleMap [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {n : ℕ} {T : Profinite.{u}} (g : Fin n → C(T, G)) : C(T, power G n) :=
  ⟨fun t i ↦ g i t, continuous_pi fun i ↦ (g i).continuous⟩

/-- The tuple entering an interior inhomogeneous face, with adjacent entries multiplied.
Source: the internal bar formula (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def mergeTuple {n : ℕ} {T : Profinite.{u}} (i : Fin (n + 2))
    (g : Fin (n + 1) → C(T, G)) : Fin n → C(T, G) :=
  fun j ↦ if j.val + 1 < i.val then g j.castSucc
    else if j.val + 1 = i.val then g j.castSucc * g j.succ else g j.succ

/-- The landed invariant-submodule functor and its normalized inclusion adjunction.
Source: internal-action definitions (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev Invariants (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] := Profinite.CondensedAction.Invariants A.toMon G

attribute [instance] Profinite.CondensedAction.Invariants.additive

/-- The actual free internal module on a representable condensed set: apply the free
abelian sheaf functor (sheafified free abelian group, left adjoint of forgetting to
condensed sets) and then the free internal A-module functor `A ⊗ -`. This is the same
composite as the free functor of the internal bar resolution module, written out here so
that the definition rests on definitions only.
Source: the composed free adjunction (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def freeParameter (A : Ring.{u}) (P : Profinite.{u}) : Modules A :=
  (Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free A.toMon.X).obj
    ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).obj P)

/-- Internal functions from a profinite parameter, characterized on every generalized section.
By the free-module adjunction this is precisely internal Hom from A[P]. Linearity and
restriction formulas uniquely specify the functor, and include empty profinite parameters.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure InternalFunctions (A : Ring.{u}) where
  functor : Profinite.{u} → (Modules A ⥤ Modules A)
  additive : ∀ P, (functor P).Additive
  internalHom : ∀ P, functor P ≅ Mod.ihom (freeParameter A P)
  evaluate : ∀ (P S : Profinite.{u}) (M : Modules A),
    sections A ((functor P).obj M) S ≃
      {c : FunctionFamily M P S // c.IsNatural}
  add : ∀ (P S : Profinite.{u}) (M : Modules A) (x y)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
    (evaluate P S M (x + y)).val T f g =
      (evaluate P S M x).val T f g + (evaluate P S M y).val T f g
  smul : ∀ (P S : Profinite.{u}) (M : Modules A) (r : sectionRing A S) (x)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
    (evaluate P S M (r • x)).val T f g =
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj.map f.op r •
          (evaluate P S M x).val T f g
  map : ∀ (P S : Profinite.{u}) {M N : Modules A} (h : M ⟶ N) (x)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
    (evaluate P S N (((functor P).map h).hom.hom.app (op S) x)).val T f g =
      h.hom.hom.app (op T) ((evaluate P S M x).val T f g)
  restriction : ∀ (P S V : Profinite.{u}) (k : V ⟶ S) (M : Modules A) (x)
    (T : Profinite.{u}) (f : T ⟶ V) (g : C(T, P)),
    (evaluate P V M (((functor P).obj M).X.obj.map k.op x)).val T f g =
      (evaluate P S M x).val T (f ≫ k) g

attribute [instance] InternalFunctions.additive

/-- The equivariant bar diagram, specified by the inhomogeneous face and degeneracy
formulas on every generalized element. A model is unique up to its displayed evaluations.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure BarDiagram (F : InternalFunctions A) [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] where
  diagram : Equivariant A G ⥤ CosimplicialObject (Modules A)
  maps_additive : ∀ {N P : Equivariant A G} (f h : N ⟶ P) (n : ℕ),
    (diagram.map (f + h)).app (SimplexCategory.mk n) =
      (diagram.map f).app (SimplexCategory.mk n) +
        (diagram.map h).app (SimplexCategory.mk n)
  term : ∀ (N : Equivariant A G) (n : ℕ),
    (diagram.obj N).obj (SimplexCategory.mk n) ≅ (F.functor (power G n)).obj N.module
  face : ∀ (N : Equivariant A G) (n : ℕ) (i : Fin (n + 2)) (S : Profinite.{u})
    (x : sections A ((F.functor (power G n)).obj N.module) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, G)),
    (F.evaluate (power G (n + 1)) S N.module
      (((term N n).inv ≫ (diagram.obj N).δ i ≫ (term N (n + 1)).hom).hom.hom.app
        (op S) x)).val T f (tupleMap g) =
      if i.val = 0 then N.act T (g 0)
        ((F.evaluate (power G n) S N.module x).val T f (tupleMap (fun j ↦ g j.succ)))
      else if i.val = n + 1 then
        (F.evaluate (power G n) S N.module x).val T f (tupleMap (fun j ↦ g j.castSucc))
      else (F.evaluate (power G n) S N.module x).val T f (tupleMap (mergeTuple i g))
  degeneracy : ∀ (N : Equivariant A G) (n : ℕ) (i : Fin (n + 1)) (S : Profinite.{u})
    (x : sections A ((F.functor (power G (n + 1))).obj N.module) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, G)),
    (F.evaluate (power G n) S N.module
      (((term N (n + 1)).inv ≫ (diagram.obj N).σ i ≫ (term N n).hom).hom.hom.app
        (op S) x)).val T f (tupleMap g) =
      (F.evaluate (power G (n + 1)) S N.module x).val T f
        (tupleMap (Fin.insertNth i 1 g))
  maps : ∀ {N P : Equivariant A G} (h : N ⟶ P) (n : ℕ),
    (diagram.map h).app (SimplexCategory.mk n) ≫ (term P n).hom =
      (term N n).hom ≫ (F.functor (power G n)).map h.val

/-- The alternating inhomogeneous cochains, constructed from the specified nerve diagram.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def cochains [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {F : InternalFunctions A} (B : BarDiagram (G := G) F) :
    Equivariant A G ⥤ CochainComplex (Modules A) ℕ :=
  B.diagram ⋙ AlgebraicTopology.alternatingCofaceMapComplex (Modules A)

/-- Alternating cochains inherit the additive structure from their termwise formula.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance cochains_additive [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {F : InternalFunctions A} (B : BarDiagram (G := G) F) : (cochains B).Additive where
  map_add := by
    intros N P f h
    apply HomologicalComplex.hom_ext
    intro n
    exact B.maps_additive f h n

/-- The invariant inclusion as an actual cochain augmentation, normalized by constant functions.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure Augmentation [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Invariants A G) {F : InternalFunctions A} (B : BarDiagram (G := G) F) where
  map : V.functor ⋙ CochainComplex.single₀ (Modules A) ⟶ cochains B
  degreeZero : ∀ (N : Equivariant A G) (S : Profinite.{u})
    (x : sections A (V.functor.obj N) S) (T : Profinite.{u}) (f : T ⟶ S)
    (g : C(T, power G 0)),
    (F.evaluate (power G 0) S N.module
      (((map.app N).f 0 ≫ (B.term N 0).hom).hom.hom.app (op S) x)).val T f g =
      N.module.X.obj.map f.op ((V.inclusion.app N).hom.hom.app (op S) x)

/-- The compatible first-quadrant bar double complex on a single resolution.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def doubleComplex [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : CochainComplex (Equivariant A G) ℕ) :
    HomologicalComplex₂ (Modules A) (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip (((cochains B).mapHomologicalComplex (.up ℕ)).obj I)

/-- Finite-diagonal totalization of the compatible bar double complex.
The outer degree is the bar degree; the differential is d_bar + (-1)^p d_resolution.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def totalCochains [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {F : InternalFunctions A} (B : BarDiagram (G := G) F) :
    CochainComplex (Equivariant A G) ℕ ⥤ CochainComplex (Modules A) ℕ :=
  (cochains B).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor (Modules A) (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor (Modules A) (.up ℕ) (.up ℕ) (.up ℕ)

/-- The total invariant augmentation is fixed on every degree by the bar-zero coprojection.
Its naturality is for actual chain maps, so includes comparison maps of resolutions.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure TotalAugmentation [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Invariants A G) {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (a : Augmentation V B) where
  map : V.functor.mapHomologicalComplex (.up ℕ) ⟶ totalCochains B
  components : ∀ (I : CochainComplex (Equivariant A G) ℕ) (n : ℕ),
    (map.app I).f n = (a.map.app (I.X n)).f 0 ≫
      (doubleComplex B I).ιTotal (.up ℕ) 0 n n (by simp)

/-- Extension of a nonnegative complex by zero to the ordinary integer-indexed category.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
abbrev extend (K : CochainComplex (Modules A) ℕ) : CochainComplex (Modules A) ℤ :=
  K.extend ComplexShape.embeddingUpNat

/-- Abelian-category properties for the fixed additive action category; only the existence
of limits and normality is supplied, while addition remains the actual addition of maps.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
class ActionAbelian (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  normalMono : IsNormalMonoCategory (Equivariant A G)
  normalEpi : IsNormalEpiCategory (Equivariant A G)
  products : HasFiniteProducts (Equivariant A G)
  kernels : HasKernels (Equivariant A G)
  cokernels : HasCokernels (Equivariant A G)

/-- The abelian structure uses the fixed addition of equivariant internal module maps.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance actionAbelian [h : ActionAbelian A G] : Abelian (Equivariant A G) where
  toPreadditive := Profinite.CondensedAction.actionPreadditive
  toIsNormalMonoCategory := h.normalMono
  toIsNormalEpiCategory := h.normalEpi
  has_finite_products := h.products
  has_kernels := h.kernels
  has_cokernels := h.cokernels

/-- Expose the multiplicative law of a bundled condensed-ring map to scalar restriction.
Source: bundled monoid morphisms (blueprint: def-sfb-condensed-equivariant-bar-data). -/
instance scalarMap_isMonHom {A A' : Ring.{u}} (a : A ⟶ A') : IsMonHom a.hom.hom :=
  a.hom.isMonHom_hom

/-- Restriction of an internal action along the specified ring morphism. The displayed
underlying isomorphism intertwines every generalized group element, fixing the functor.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure ScalarAction {A A' : Ring.{u}} (a : A ⟶ A') (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] where
  functor : Equivariant A' G ⥤ Equivariant A G
  additive : functor.Additive
  underlying : functor ⋙ forgetAction ≅ forgetAction ⋙ Mod.comap a.hom.hom
  action : ∀ (N : Equivariant A' G) (S : Profinite.{u}) (g : C(S, G))
    (x : sections A (functor.obj N).module S),
    (underlying.hom.app N).hom.hom.app (op S) ((functor.obj N).act S g x) =
      N.act S g ((underlying.hom.app N).hom.hom.app (op S) x)

attribute [instance] ScalarAction.additive

section Derived
variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized ordinary right-derived-invariant comparison on a specified injective
resolution: map its augmentation and then invert the right-derived unit on injectives.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def resolutionComparison (V : Invariants A G) {N : Equivariant A G}
    (I : InjectiveResolution N) :
    V.functor.rightDerivedFunctor.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2}.obj ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N) ≅
      DerivedCategory.Q.{u + 2}.obj (extend ((V.functor.mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex)) := by
  letI : QuasiIso I.ι' := by infer_instance
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact V.functor.rightDerivedFunctor.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2}.mapIso (asIso (DerivedCategory.Q.{u + 2}.map I.ι')) ≪≫
    V.functor.rightDerivedFunctorObjQIso.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2} I.cochainComplex ≪≫
      DerivedCategory.Q.{u + 2}.mapIso
        (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat V.functor)

/-- An actual derived-object comparison for every compatible nonnegative resolution.
The normalization makes it the localization of the invariant inclusion, not an arbitrary
isomorphism. All chain lifts obey naturality through the total augmentation.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure Computation [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Invariants A G) {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (a : Augmentation V B) (t : TotalAugmentation V B a) where
  forgetInjectives : (forgetAction (A := A) (G := G)).PreservesInjectiveObjects
  forgetLimits : PreservesFiniteLimits (forgetAction (A := A) (G := G))
  forgetColimits : PreservesFiniteColimits (forgetAction (A := A) (G := G))
  columns : ∀ (P : Profinite.{u}) {N : Equivariant A G} (I : InjectiveResolution N),
    IsIso ((F.functor P).rightDerivedFunctorUnit.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (extend (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex))))
  augmentation_quasiIso : ∀ {N : Equivariant A G} (I : InjectiveResolution N),
    QuasiIso (t.map.app I.cocomplex)
  iso : ∀ {N : Equivariant A G} (I : InjectiveResolution N),
    V.functor.rightDerivedFunctor.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2}.obj ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N) ≅
      DerivedCategory.Q.{u + 2}.obj (extend ((totalCochains B).obj I.cocomplex))
  normalization : ∀ {N : Equivariant A G} (I : InjectiveResolution N),
    (iso I).hom = (resolutionComparison V I).hom ≫
      DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap (t.map.app I.cocomplex)
        ComplexShape.embeddingUpNat)
  naturality : ∀ {N P : Equivariant A G} (h : N ⟶ P)
    (I : InjectiveResolution N) (J : InjectiveResolution P)
    (f : I.cocomplex ⟶ J.cocomplex) (_hf : I.ι ≫ f = (CochainComplex.single₀ _).map h ≫ J.ι),
    V.functor.rightDerivedFunctor.{u + 2, u + 2,
      u + 1, u + 1, u + 2, u + 2}.map ((DerivedCategory.singleFunctor.{u + 2} _ 0).map h) ≫
        (iso J).hom = (iso I).hom ≫
      DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap ((totalCochains B).map f)
        ComplexShape.embeddingUpNat)
end Derived

/-- All ordinary and derived bar data for one coefficient ring. No existence assertion
is hidden in this definition: the theorem supplies this data with its computation laws.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure Model (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
    [HasDerivedCategory.{u + 2} (Equivariant A G)]
    [HasDerivedCategory.{u + 2} (Modules A)] where
  invariants : Invariants A G
  functions : InternalFunctions A
  bar : BarDiagram (G := G) functions
  augmentation : Augmentation invariants bar
  totalAugmentation : TotalAugmentation invariants bar augmentation
  computation : Computation invariants bar augmentation totalAugmentation

section Scalar
variable {A A' : Ring.{u}} (a : A ⟶ A')
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [ActionAbelian A' G]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Modules A)] [HasDerivedCategory.{u + 2} (Modules A')]

/-- Scalar compatibility before resolving, including the formulas fixing the maps on each
internal-Hom term and each total summand. These formulas exclude an arbitrary comparison.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure ScalarModel (M : Model A G) (M' : Model A' G) where
  restriction : ScalarAction a G
  invariants : restriction.functor ⋙ M.invariants.functor ≅
    M'.invariants.functor ⋙ Mod.comap a.hom.hom
  inclusion : ∀ N, M.invariants.inclusion.app (restriction.functor.obj N) ≫
      restriction.underlying.hom.app N =
    invariants.hom.app N ≫ (Mod.comap a.hom.hom).map (M'.invariants.inclusion.app N)
  bar : restriction.functor ⋙ cochains M.bar ≅
    cochains M'.bar ⋙ (Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)
  evaluation : ∀ (N : Equivariant A' G) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains M.bar).obj (restriction.functor.obj N)).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, power G n)),
    (restriction.underlying.hom.app N).hom.hom.app (op T)
      ((M.functions.evaluate (power G n) S (restriction.functor.obj N).module
        ((M.bar.term (restriction.functor.obj N) n).hom.hom.hom.app (op S) x)).val
          T f g) =
    (M'.functions.evaluate (power G n) S N.module
      ((M'.bar.term N n).hom.hom.hom.app (op S)
        (((bar.hom.app N).f n).hom.hom.app (op S) x))).val T f g
  total : restriction.functor.mapHomologicalComplex (.up ℕ) ⋙ totalCochains M.bar ≅
    totalCochains M'.bar ⋙ (Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)
  summands : ∀ (J : CochainComplex (Equivariant A' G) ℕ) (p q n : ℕ)
    (h : p + q = n),
    (doubleComplex M.bar
      ((restriction.functor.mapHomologicalComplex (.up ℕ)).obj J)).ιTotal
        (.up ℕ) p q n h ≫ (total.hom.app J).f n =
    (bar.hom.app (J.X q)).f p ≫ (Mod.comap a.hom.hom).map
      ((doubleComplex M'.bar J).ιTotal (.up ℕ) p q n h)

/-- The normalized map on invariant-resolution complexes, directed from restricted
A'-resolutions to A-resolutions. Its inverse in the derived category is scalar restriction.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def scalarInvariantChain {M : Model A G} {M' : Model A' G} (s : ScalarModel a M M')
    (J : CochainComplex (Equivariant A' G) ℕ)
    (I : CochainComplex (Equivariant A G) ℕ)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J ⟶ I) :
    ((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).obj
        ((M'.invariants.functor.mapHomologicalComplex (.up ℕ)).obj J) ⟶
      (M.invariants.functor.mapHomologicalComplex (.up ℕ)).obj I :=
  (NatIso.mapHomologicalComplex s.invariants (.up ℕ)).inv.app J ≫
    (M.invariants.functor.mapHomologicalComplex (.up ℕ)).map β

/-- The corresponding total-bar map, built from the same comparison β in every term.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def scalarTotalChain {M : Model A G} {M' : Model A' G} (s : ScalarModel a M M')
    (J : CochainComplex (Equivariant A' G) ℕ)
    (I : CochainComplex (Equivariant A G) ℕ)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J ⟶ I) :
    ((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).obj
        ((totalCochains M'.bar).obj J) ⟶ (totalCochains M.bar).obj I :=
  s.total.inv.app J ≫ (totalCochains M.bar).map β

/-- Localizing a specified nonnegative quasi-isomorphism, with no choice of its inverse.
Source: derived localization (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def localizedIso {K L : CochainComplex (Modules A) ℕ} (f : K ⟶ L) (hf : QuasiIso f) :
    DerivedCategory.Q.{u + 2}.obj (extend K) ≅ DerivedCategory.Q.{u + 2}.obj (extend L) := by
  letI := hf
  exact asIso (DerivedCategory.Q.{u + 2}.map
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat))

/-- Scalar restriction on the derived bar calculation. All lifts β are quantified, and
all columns and both sides of the augmentation square are normalized by actual chain maps.
Inverting these vertical quasi-isomorphisms gives the canonical scalar maps in the theorem.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
structure ScalarComputation {M : Model A G} {M' : Model A' G} (s : ScalarModel a M M') where
  lifts : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N),
    ∃ β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
        I.cocomplex,
      s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0
  columns : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (_hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0)
    (p : ℕ),
    QuasiIso (((M.functions.functor (power G p)).mapHomologicalComplex (.up ℕ)).map
      (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).map β))
  invariantQI : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (_hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0),
    QuasiIso (scalarInvariantChain a s J.cocomplex I.cocomplex β)
  totalQI : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (_hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0),
    QuasiIso (scalarTotalChain a s J.cocomplex I.cocomplex β)
  square : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0),
    DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
        (M.totalAugmentation.map.app I.cocomplex) ComplexShape.embeddingUpNat) ≫
      (localizedIso (scalarTotalChain a s J.cocomplex I.cocomplex β)
        (totalQI N I J β hβ)).inv =
    (localizedIso (scalarInvariantChain a s J.cocomplex I.cocomplex β)
      (invariantQI N I J β hβ)).inv ≫
        DerivedCategory.Q.{u + 2}.map (HomologicalComplex.extendMap
          (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).map
            (M'.totalAugmentation.map.app J.cocomplex)) ComplexShape.embeddingUpNat)
end Scalar

/-- The whole bar assertion, including the existence of the action-category structures,
so no Grothendieck or existence hypotheses have been added to the theorem. Standard
localizations are used uniformly; each model includes the ordinary total right derived functor.
Source: formal internal-bar expansion (blueprint: def-sfb-condensed-equivariant-bar-data). -/
def Assertion (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop := by
  refine ∃ h : ∀ A : Ring.{u}, ActionAbelian A G, ?_
  letI (A : Ring.{u}) : ActionAbelian A G := h A
  refine ∃ g : ∀ A : Ring.{u}, IsGrothendieckAbelian.{u + 1} (Equivariant A G), ?_
  letI (A : Ring.{u}) : IsGrothendieckAbelian.{u + 1} (Equivariant A G) := g A
  letI (A : Ring.{u}) : HasDerivedCategory.{u + 2} (Equivariant A G) :=
    HasDerivedCategory.standard (Equivariant A G)
  letI (A : Ring.{u}) : HasDerivedCategory.{u + 2} (Modules A) :=
    HasDerivedCategory.standard (Modules A)
  exact ∃ models : ∀ A : Ring.{u}, Model A G,
    ∀ (A A' : Ring.{u}) (a : A ⟶ A'),
      ∃ s : ScalarModel a (models A) (models A'), Nonempty (ScalarComputation a s)

end CategoryTheory.CondensedBar
