/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Topology.Algebra.Ring.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# Geometric operation packages with specified exceptional adjunction domains

Source: literature/blueprint/latest/blueprint/sec-trace-formula/sk-d-six/_section.md,
all five data bullets and coherence/invertibility clauses (blueprint: sk-d-six).

The operations are supplied inputs. Exceptional adjunctions have explicitly supplied
full subcategory domains; no ambient right-adjoint existence is asserted. All tensor,
Hom, evaluation and biduality constructions use the recorded relative derived structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.TraceOperations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ordinary uncompleted derived category of modules over `ρ_X^*Λ`.
Source: sk-d-six, opening (blueprint: sk-d-six). -/
abbrev D (X : Scheme.{u}) := DerivedCategory
  (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The recorded derived pullback; it is an input to the operation package, not a new
pullback construction. Source: sk-d-six, opening (blueprint: sk-d-six). -/
abbrev star {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ Y ⥤ D Λ X :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- The recorded derived ordinary pushforward.
Source: sk-d-six, opening (blueprint: sk-d-six). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ X ⥤ D Λ Y :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

/-- The specified domain of an exceptional adjunction. The Hom equivalence is required
only for the supplied source and target full subcategories. Naturality in each variable
is the adjunction condition; the output functor is valued in the ordinary derived category.
Source: sk-d-six, opening and its explicit adjunction-domain convention
(blueprint: sk-d-six). -/
structure ExceptionalDomain {X Y : Scheme.{u}} (F : D Λ X ⥤ D Λ Y) where
  source : ObjectProperty (D Λ X)
  target : ObjectProperty (D Λ Y)
  right : target.FullSubcategory ⥤ D Λ X
  right_mem_source : ∀ L, source (right.obj L)
  left_mem_target : ∀ K : source.FullSubcategory, target (F.obj K.obj)
  homEquiv : ∀ (K : source.FullSubcategory) (L : target.FullSubcategory),
    (F.obj K.obj ⟶ L.obj) ≃ (K.obj ⟶ right.obj L)
  natural_left : ∀ (K K' : source.FullSubcategory) (L : target.FullSubcategory)
    (a : K ⟶ K') (b : F.obj K'.obj ⟶ L.obj),
    homEquiv K L (F.map a.hom ≫ b) = a.hom ≫ homEquiv K' L b
  natural_right : ∀ (K : source.FullSubcategory) (L L' : target.FullSubcategory)
    (a : F.obj K.obj ⟶ L.obj) (b : L ⟶ L'),
    homEquiv K L' (a ≫ b.hom) = homEquiv K L a ≫ right.map b

/-- Given compact-support operations and their given exceptional adjunction domains.
The type `exceptional f` indexes the supplied domains, and may be empty when no exceptional
adjunction is supplied. No existence statement is part of this input record.
Source: sk-d-six, opening (blueprint: sk-d-six). -/
structure Given (s : Scheme.{u}) where
  shriek : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left],
    D Λ X.left ⥤ D Λ Y.left
  exceptional : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left], Type (u + 2)
  domain : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left],
    exceptional f → ExceptionalDomain Λ (shriek f)

/-- The canonical derived Koszul braiding, descended from complexes.
Source: sk-d-six, sign convention (blueprint: sk-d-six). -/
local instance derivedBraiding (X : Scheme.{u}) : BraidedCategory (D Λ X) :=
  DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The canonical pullback identity, obtained from the exact underived identity.
Source: sk-d-six, identity comparison (blueprint: sk-d-six). -/
def starIdentity (X : Scheme.{u}) : star Λ (𝟙 X) ≅ 𝟭 (D Λ X) :=
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical direct-image identity, the mate of inverse pullback identity.
Source: sk-d-six, identity comparison (blueprint: sk-d-six). -/
def pushIdentity (X : Scheme.{u}) : push Λ (𝟙 X) ≅ 𝟭 (D Λ X) :=
  conjugateIsoEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (𝟙 X))
    Adjunction.id (starIdentity Λ X).symm

/-- The ordinary derived direct-image compositor, the mate of pullback composition.
Source: sk-d-six, composition comparison (blueprint: sk-d-six). -/
def pushComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push Λ f ⋙ push Λ g ≅ push Λ (f ≫ g) :=
  (conjugateIsoEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f))
    (CondensedRing.leftDerivedUpperStarComp Λ f g).symm).symm

variable {Λ}

/-- The base object in the over category. Source: sk-d-six (blueprint: sk-d-six). -/
abbrev base (s : Scheme.{u}) : Over s := Over.mk (𝟙 s)

/-- A structure map as a morphism over the base.
Source: sk-d-six (blueprint: sk-d-six). -/
abbrev structureMap {s : Scheme.{u}} (X : Over s) : X ⟶ base s := Over.homMk X.hom

/-- The structure map has exactly its given compactifiability instance.
Source: sk-d-six, structure-map convention (blueprint: sk-d-six). -/
instance structureMapCompactifiable {s : Scheme.{u}} (X : Over s)
    [HasCompactification X.hom] : HasCompactification (structureMap X).left :=
  inferInstanceAs (HasCompactification X.hom)

/-- The base structure morphism is the proper identity.
Source: sk-d-six, normalization at s (blueprint: sk-d-six). -/
instance baseCompactifiable (s : Scheme.{u}) : HasCompactification (base s).hom :=
  inferInstanceAs (HasCompactification (𝟙 s))

/-- Proper composition in the bundled over category is ordinary proper composition.
Source: sk-d-six, proper composition coherence (blueprint: sk-d-six). -/
local instance overCompProper {s : Scheme.{u}} {X Y Z : Over s}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left] [IsProper g.left] :
    IsProper (f ≫ g).left := inferInstanceAs (IsProper (f.left ≫ g.left))

/-- The product over the specified base, with the actual chosen scheme pullback.
Source: sk-d-six, external product (blueprint: sk-d-six). -/
abbrev product {s : Scheme.{u}} (X Y : Over s) : Over s :=
  Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)

/-- First product projection. Source: sk-d-six (blueprint: sk-d-six). -/
abbrev first {s : Scheme.{u}} (X Y : Over s) : product X Y ⟶ X :=
  Over.homMk (pullback.fst X.hom Y.hom)

/-- Second product projection. Source: sk-d-six (blueprint: sk-d-six). -/
abbrev second {s : Scheme.{u}} (X Y : Over s) : product X Y ⟶ Y :=
  Over.homMk (pullback.snd X.hom Y.hom) (pullback.condition (f := X.hom) (g := Y.hom)).symm

/-- Verdier duality on objects, using the existing relative internal Hom.
Source: sk-d-six, displayed definitions (blueprint: sk-d-six). -/
def dual {X : Scheme.{u}} (ω K : D Λ X) : D Λ X := (ihom K).obj ω

/-- Evaluation is the tensor--Hom adjunct of the identity, with the braiding for the
specified tensor slot. Source: sk-d-six, evaluation paragraph (blueprint: sk-d-six). -/
def evaluation {X : Scheme.{u}} (ω K : D Λ X) : dual ω K ⊗ K ⟶ ω :=
  (β_ (dual ω K) K).hom ≫ (ihom.ev K).app ω

/-- The specified evaluation-adjoint biduality map; the two braidings exhibit precisely
which tensor slot the given closed adjunction uses.
Source: sk-d-six, biduality paragraph (blueprint: sk-d-six). -/
def biduality {X : Scheme.{u}} (ω K : D Λ X) : K ⟶ dual ω (dual ω K) :=
  (ihom.adjunction (dual ω K)).homEquiv K ω
    ((β_ (dual ω K) K).hom ≫ (β_ K (dual ω K)).hom ≫ evaluation ω K)

/-- External product using actual product projections and the relative derived tensor.
Source: sk-d-six, displayed definitions (blueprint: sk-d-six). -/
def externalProduct {s : Scheme.{u}} {X Y : Over s}
    (M : D Λ X.left) (N : D Λ Y.left) : D Λ (product X Y).left :=
  (star Λ (first X Y).left).obj M ⊗ (star Λ (second X Y).left).obj N

/-- The counit on the supplied exceptional domain, obtained from its Hom equivalence.
Source: sk-d-six, trace construction (blueprint: sk-d-six). -/
def ExceptionalDomain.counit {X Y : Scheme.{u}} {F : D Λ X ⥤ D Λ Y}
    (e : ExceptionalDomain Λ F) (L : e.target.FullSubcategory) :
    F.obj (e.right.obj L) ⟶ L.obj :=
  (e.homEquiv ⟨e.right.obj L, e.right_mem_source L⟩ L).symm (𝟙 _)

variable {s : Scheme.{u}} (O : Given Λ s)

/-- The five specified kinds of package data, on the supplied operation domains.
Here `omega` is ambient, not assumed constructible; tensor and internal Hom are the
existing derived ones, not freely chosen operations.
Source: sk-d-six, five data bullets (blueprint: sk-d-six). -/
structure Comparisons where
  omega : ∀ X : Over s, D Λ X.left
  normalization : omega (base s) ≅ 𝟙_ (D Λ s)
  dualizing : ∀ (X : Over s) [HasCompactification X.hom]
    (e : O.exceptional (structureMap X))
    (h : (O.domain (structureMap X) e).target (𝟙_ (D Λ s))),
    omega X ≅ (O.domain (structureMap X) e).right.obj ⟨𝟙_ (D Λ s), h⟩
  dualizingComp : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (e : O.exceptional f) (h : (O.domain f e).target (omega Y)),
    (O.domain f e).right.obj ⟨omega Y, h⟩ ≅ omega X
  proper : ∀ {X Y : Over s} (f : X ⟶ Y) [IsProper f.left],
    O.shriek f ≅ push Λ f.left
  composition : ∀ {X Y Z : Over s} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f.left] [HasCompactification g.left]
    [HasCompactification (f ≫ g).left], O.shriek f ⋙ O.shriek g ≅ O.shriek (f ≫ g)
  identity : ∀ X : Over s, O.shriek (𝟙 X) ≅ 𝟭 (D Λ X.left)
  baseChange : ∀ {X' X Y' Y : Over s}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [HasCompactification f.left] [HasCompactification f'.left],
    ChosenCartesianSquare g'.left f'.left f.left g.left →
      (O.shriek f ⋙ star Λ g.left ≅ star Λ g'.left ⋙ O.shriek f')
  projection : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (K : D Λ X.left) (L : D Λ Y.left),
    (O.shriek f).obj K ⊗ L ≅ (O.shriek f).obj (K ⊗ (star Λ f.left).obj L)
  projection_natural : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (K K' : D Λ X.left) (L L' : D Λ Y.left) (a : K ⟶ K') (b : L ⟶ L'),
    ((O.shriek f).map a ⊗ₘ b) ≫ (projection f K' L').hom =
      (projection f K L).hom ≫ (O.shriek f).map (a ⊗ₘ (star Λ f.left).map b)
  monoidal : ∀ {X Y : Over s} (f : X ⟶ Y), (star Λ f.left).CoreMonoidal
  braided : ∀ {X Y : Over s} (f : X ⟶ Y) (K L : D Λ Y.left),
    (β_ ((star Λ f.left).obj K) ((star Λ f.left).obj L)).hom ≫
      ((monoidal f).μIso L K).hom =
      ((monoidal f).μIso K L).hom ≫ (star Λ f.left).map (β_ K L).hom

namespace Comparisons

variable (P : Comparisons O)

/-- The compact-support functor of the structure morphism.
Source: sk-d-six, displayed definitions (blueprint: sk-d-six). -/
def compactlySupported (X : Over s) [HasCompactification X.hom] :
    D Λ X.left ⥤ D Λ s := O.shriek (structureMap X)

/-- The canonical product trace: inverse base change, the dualizing identification,
the exceptional counit at the coefficient unit, and inverse monoidal unit.
Source: sk-d-six, displayed formula for `t` (blueprint: sk-d-six). -/
def trace (X Y Z : Over s) (px : Z ⟶ X) (py : Z ⟶ Y)
    [HasCompactification Y.hom] [HasCompactification px.left]
    (sq : ChosenCartesianSquare py.left px.left Y.hom X.hom)
    (eY : O.exceptional (structureMap Y))
    (hY : (O.domain (structureMap Y) eY).target (𝟙_ (D Λ s))) :
    (O.shriek px).obj ((star Λ py.left).obj (P.omega Y)) ⟶ 𝟙_ (D Λ X.left) :=
  (P.baseChange py px (structureMap Y) (structureMap X) sq).inv.app (P.omega Y) ≫
    (star Λ X.hom).map ((O.shriek (structureMap Y)).map (P.dualizing Y eY hY).hom) ≫
    (star Λ X.hom).map ((O.domain (structureMap Y) eY).counit ⟨_, hY⟩) ≫
    (P.monoidal (structureMap X)).εIso.inv

/-- The exceptional adjunct `alpha_M`. Its two domain proofs are supplied, rather
than deduced from a general-base constructibility-preservation assertion.
Source: sk-d-six, displayed formula for `alpha_M` (blueprint: sk-d-six). -/
def alpha (X Y Z : Over s) (px : Z ⟶ X) (py : Z ⟶ Y)
    [HasCompactification Y.hom] [HasCompactification px.left]
    (sq : ChosenCartesianSquare py.left px.left Y.hom X.hom)
    (eY : O.exceptional (structureMap Y))
    (hY : (O.domain (structureMap Y) eY).target (𝟙_ (D Λ s)))
    (eP : O.exceptional px) (M : D Λ X.left)
    (hM : (O.domain px eP).target M)
    (hJ : (O.domain px eP).source
      ((star Λ px.left).obj M ⊗ (star Λ py.left).obj (P.omega Y))) :
    (star Λ px.left).obj M ⊗ (star Λ py.left).obj (P.omega Y) ⟶
      (O.domain px eP).right.obj ⟨M, hM⟩ :=
  (O.domain px eP).homEquiv ⟨_, hJ⟩ ⟨M, hM⟩
    ((O.shriek px).map
      (β_ ((star Λ px.left).obj M) ((star Λ py.left).obj (P.omega Y))).hom ≫
    (P.projection px ((star Λ py.left).obj (P.omega Y)) M).inv ≫
    (P.trace O X Y Z px py sq eY hY ⊗ₘ 𝟙 M) ≫ (λ_ M).hom)

/-- The specified Künneth--Verdier arrow, constructed from the supplied comparisons.
It is not an arbitrary morphism or a bare existence of an isomorphism.
Source: sk-d-six, final displayed composite and tensor--Hom adjunct
(blueprint: sk-d-six). -/
def kunnethVerdier (X Y Z : Over s) (px : Z ⟶ X) (py : Z ⟶ Y)
    [HasCompactification Y.hom] [HasCompactification px.left]
    (sq : ChosenCartesianSquare py.left px.left Y.hom X.hom)
    (eY : O.exceptional (structureMap Y))
    (hY : (O.domain (structureMap Y) eY).target (𝟙_ (D Λ s)))
    (eP : O.exceptional px) (M : D Λ X.left) (N : D Λ Y.left)
    (hM : (O.domain px eP).target M)
    (hJ : (O.domain px eP).source
      ((star Λ px.left).obj M ⊗ (star Λ py.left).obj (P.omega Y))) :
    (star Λ px.left).obj M ⊗ (star Λ py.left).obj (dual (P.omega Y) N) ⟶
      (ihom ((star Λ py.left).obj N)).obj ((O.domain px eP).right.obj ⟨M, hM⟩) :=
  (ihom.adjunction ((star Λ py.left).obj N)).homEquiv _ _
    ((β_ ((star Λ py.left).obj N)
      ((star Λ px.left).obj M ⊗ (star Λ py.left).obj (dual (P.omega Y) N))).hom ≫
    (α_ ((star Λ px.left).obj M) ((star Λ py.left).obj (dual (P.omega Y) N))
      ((star Λ py.left).obj N)).hom ≫
    ((star Λ px.left).obj M ◁
      ((P.monoidal py).μIso (dual (P.omega Y) N) N).hom) ≫
    ((star Λ px.left).obj M ◁ (star Λ py.left).map (evaluation (P.omega Y) N)) ≫
    P.alpha O X Y Z px py sq eY hY eP M hM hJ)

/-- The trace mate of the dualizing composition isomorphism. Compatibility of these
traces is precisely compatibility of the dualizing isomorphisms with the adjoint
composition comparison. Source: sk-d-six, coherence paragraph (blueprint: sk-d-six). -/
def dualizingTrace {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (e : O.exceptional f) (hX : (O.domain f e).source (P.omega X))
    (hY : (O.domain f e).target (P.omega Y)) :
    (O.shriek f).obj (P.omega X) ⟶ P.omega Y :=
  ((O.domain f e).homEquiv ⟨_, hX⟩ ⟨_, hY⟩).symm (P.dualizingComp f e hY).inv

/-- Componentwise identity, normalization, composition, and vertical-pasting equations.
The dualizing composition equation is stated after the given adjunction bijections;
it therefore uses exactly the adjoint composition comparison.
Source: sk-d-six, coherence paragraph (blueprint: sk-d-six). -/
structure Coherence : Prop where
  leftUnit : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (K : D Λ X.left),
    letI : HasCompactification ((𝟙 X) ≫ f).left :=
      HasCompactification.of_eq (f := f.left)
        (congrArg Over.Hom.left (Category.id_comp f)).symm
    (P.composition (𝟙 X) f).hom.app K ≫
      (eqToIso (by simp only [Category.id_comp] :
        O.shriek ((𝟙 X) ≫ f) = O.shriek f)).hom.app K =
      (O.shriek f).map ((P.identity X).hom.app K)
  rightUnit : ∀ {X Y : Over s} (f : X ⟶ Y) [HasCompactification f.left]
    (K : D Λ X.left),
    letI : HasCompactification (f ≫ (𝟙 Y)).left :=
      HasCompactification.of_eq (f := f.left)
        (congrArg Over.Hom.left (Category.comp_id f)).symm
    (P.composition f (𝟙 Y)).hom.app K ≫
      (eqToIso (by simp only [Category.comp_id] :
        O.shriek (f ≫ (𝟙 Y)) = O.shriek f)).hom.app K =
      (P.identity Y).hom.app ((O.shriek f).obj K)
  properIdentity : ∀ (X : Over s) (K : D Λ X.left),
    (P.proper (𝟙 X)).hom.app K =
      (P.identity X).hom.app K ≫ (pushIdentity Λ X.left).inv.app K
  baseNormalization : ∀ (e : O.exceptional (structureMap (base s)))
    (hS : (O.domain (structureMap (base s)) e).source (𝟙_ (D Λ s)))
    (hT : (O.domain (structureMap (base s)) e).target (𝟙_ (D Λ s))),
    (P.dualizing (base s) e hT).hom = P.normalization.hom ≫
      (O.domain (structureMap (base s)) e).homEquiv ⟨_, hS⟩ ⟨_, hT⟩
        ((P.identity (base s)).hom.app (𝟙_ (D Λ s)))
  dualizingIdentity : ∀ (X : Over s) (e : O.exceptional (𝟙 X))
    (hS : (O.domain (𝟙 X) e).source (P.omega X))
    (hT : (O.domain (𝟙 X) e).target (P.omega X)),
    (P.dualizingComp (𝟙 X) e hT).inv =
      (O.domain (𝟙 X) e).homEquiv ⟨_, hS⟩ ⟨_, hT⟩
        ((P.identity X).hom.app (P.omega X))
  monoidalIdentity : ∀ X : Over s,
    (P.monoidal (𝟙 X)).εIso.hom ≫
      (starIdentity Λ X.left).hom.app (𝟙_ (D Λ X.left)) = 𝟙 _
  properComposition : ∀ {X Y Z : Over s} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (K : D Λ X.left),
    (P.composition f g).hom.app K ≫ (P.proper (f ≫ g)).hom.app K =
      (O.shriek g).map ((P.proper f).hom.app K) ≫
        (P.proper g).hom.app ((push Λ f.left).obj K) ≫
        (pushComposition Λ f.left g.left).hom.app K
  dualizingComposition : ∀ {X Y Z : Over s} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f.left] [HasCompactification g.left]
    [HasCompactification (f ≫ g).left]
    (ef : O.exceptional f) (eg : O.exceptional g) (efg : O.exceptional (f ≫ g))
    (hX : (O.domain f ef).source (P.omega X))
    (hY : (O.domain f ef).target (P.omega Y))
    (hY' : (O.domain g eg).source (P.omega Y))
    (hZ : (O.domain g eg).target (P.omega Z))
    (hX' : (O.domain (f ≫ g) efg).source (P.omega X))
    (hZ' : (O.domain (f ≫ g) efg).target (P.omega Z)),
    (P.composition f g).hom.app (P.omega X) ≫
      P.dualizingTrace O (f ≫ g) efg hX' hZ' =
      (O.shriek g).map (P.dualizingTrace O f ef hX hY) ≫
        P.dualizingTrace O g eg hY' hZ
  baseChangeVertical : ∀ (X Y Z X' Y' Z' : Over s)
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z)
    [HasCompactification f.left] [HasCompactification g.left]
    [HasCompactification (f ≫ g).left]
    [HasCompactification f'.left] [HasCompactification g'.left]
    [HasCompactification (f' ≫ g').left]
    (h₁ : ChosenCartesianSquare x.left f'.left f.left y.left)
    (h₂ : ChosenCartesianSquare y.left g'.left g.left z.left)
    (h₃ : ChosenCartesianSquare x.left (f' ≫ g').left (f ≫ g).left z.left)
    (K : D Λ X.left),
    (P.baseChange x (f' ≫ g') (f ≫ g) z h₃).hom.app K ≫
      (P.composition f' g').inv.app ((star Λ x.left).obj K) =
      (star Λ z.left).map ((P.composition f g).inv.app K) ≫
        (P.baseChange y g' g z h₂).hom.app ((O.shriek f).obj K) ≫
        (O.shriek g').map ((P.baseChange x f' f y h₁).hom.app K)

end Comparisons

/-- A geometric operation package on the actual ordinary derived categories.
The specified comparisons satisfy the component equations, biduality is required for
all bounded constructible finite-Tor inputs, and the canonical Künneth--Verdier arrow is
invertible over a field for quasi-compact compactifiable schemes, in the supplied
adjunction domains. The Künneth--Verdier arrow is required on the fibre product
`product X Y = X ×_s Y` with its projections `first`, `second`, whose source is
`externalProduct M (dual ω_Y N)`; the square datum `sq` for this product is unique,
since its identification with the pullback is fixed by the two projection equations.
No preservation or right-adjoint existence theorem is asserted.
Source: sk-d-six, entire definition (blueprint: sk-d-six). -/
structure GeometricOperations where
  comparisons : Comparisons O
  coherence : comparisons.Coherence O
  biduality : ∀ (X : Over s) (K : ConstantModelConstructibleFiniteTor Λ X.left),
    IsIso (TraceOperations.biduality (comparisons.omega X) K.obj)
  kunnethVerdier : ∀ (k : Type u) [Field k] (_hs : s ≅ Spec (.of k))
    (X Y : Over s) [CompactSpace X.left] [CompactSpace Y.left]
    [HasCompactification X.hom] [HasCompactification Y.hom]
    [HasCompactification (first X Y).left]
    (sq : ChosenCartesianSquare (second X Y).left (first X Y).left Y.hom X.hom)
    (eY : O.exceptional (structureMap Y))
    (hY : (O.domain (structureMap Y) eY).target (𝟙_ (D Λ s)))
    (eP : O.exceptional (first X Y))
    (M : ConstantModelConstructibleFiniteTor Λ X.left)
    (N : ConstantModelConstructibleFiniteTor Λ Y.left)
    (hM : (O.domain (first X Y) eP).target M.obj)
    (hJ : (O.domain (first X Y) eP).source
      ((star Λ (first X Y).left).obj M.obj ⊗
        (star Λ (second X Y).left).obj (comparisons.omega Y))),
    IsIso (comparisons.kunnethVerdier O X Y (product X Y) (first X Y) (second X Y) sq
      eY hY eP M.obj N.obj hM hJ)

/-- The finite commutative primary-coefficient specialization, with no restriction on
base scheme, coefficient characteristic, or finite ring beyond those in the source.
The discrete topology is unique and the resulting coefficient is exactly C(-,A).
Source: sk-d-six, opening (blueprint: sk-d-six). -/
def finiteGeometricOperationPackage (ell : ℕ) [Fact ell.Prime]
    (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0) (s : Scheme.{u})
    (O : letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := ⟨rfl⟩
      let Λ := Profinite.continuousMapRingObjOfUniverse.{u, u} A
      letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
      letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
      Given Λ s) : Type _ :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let Λ := Profinite.continuousMapRingObjOfUniverse.{u, u} A
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
  GeometricOperations (Λ := Λ) O

end AlgebraicGeometry.ProEtale.TraceOperations
