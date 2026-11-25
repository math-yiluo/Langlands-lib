/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence

/-! # Projective-line presentation and adjunction data

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-p1.md` (blueprint: def-sp-tower-p1-adjunction-data).
The domain is bounded below with etale-origin levels. No normalization is imposed.
All natural-number indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The full bounded-below etale-origin domain in the ordinary system localization.
Source: the opening paragraph (blueprint: proposition-sp-tower-geometric). -/
def domain (b : SpTowerShriek.Base l E) (T : Scheme.{u}) :
    ObjectProperty (SpTowerShriek.D l E T) :=
  fun K ↦ (∃ a : ℤ, DerivedCategory.IsGE K a) ∧
    ∀ n : ℕ, Nonempty (SpTowerShriek.Origin l E b T n K)

/-- The actual full subcategory, retaining all ambient derived morphisms.
Source: the opening paragraph (blueprint: proposition-sp-tower-geometric). -/
abbrev C (b : SpTowerShriek.Base l E) (T : Scheme.{u}) := (domain l E b T).FullSubcategory

/-- Unit and signed symmetry of the existing tensor, with its representative normalization.
The model's closed structure is required to be the already recorded system tensor.
Source: the projection identifications (blueprint: proposition-sp-tower-geometric). -/
structure TensorData (b : SpTowerShriek.Base l E) (T : Scheme.{u}) where
  model : RingedSiteDualityModel.{u + 1, u, u + 1, u + 2}
    (coefficientSequenceTopology (ProEt.topology T)) (systemRing l E T)
  closed_eq : model.closed = (b.calculus T).closed
  unitIso : (b.calculus T).closed.monoidal.tensorUnit ≅ unit T (Arings l E T)
  unit_normalization : HEq unitIso model.unitIso

/-- Transport only the structure equality; the signed symmetry remains the recorded one.
Source: projection reordering (blueprint: proposition-sp-tower-geometric). -/
@[instance_reducible]
def TensorData.symmetry {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) :
    @SymmetricCategory (SpTowerShriek.D l E T) _ (b.calculus T).closed.monoidal :=
  Eq.mp (congrArg (fun z ↦ @SymmetricCategory (SpTowerShriek.D l E T) _ z.monoidal)
    t.closed_eq) t.model.symmetric

/-- Tensor with the coefficient object contracts by actual scalar multiplication.
Source: projection identifications (blueprint: proposition-sp-tower-geometric). -/
def TensorData.rightUnit {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) (K : SpTowerShriek.D l E T) :
    (SpTowerShriek.tensor l E b T).obj (K, unit T (Arings l E T)) ≅ K :=
  (SpTowerShriek.tensor l E b T).mapIso (Iso.prod (Iso.refl K) t.unitIso.symm) ≪≫
    (b.calculus T).closed.monoidal.rightUnitor K

/-- The other coefficient constraint uses the same unit normalization.
Source: the diagonal projection (blueprint: proposition-sp-tower-geometric). -/
def TensorData.leftUnit {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) (K : SpTowerShriek.D l E T) :
    (SpTowerShriek.tensor l E b T).obj (unit T (Arings l E T), K) ≅ K :=
  (SpTowerShriek.tensor l E b T).mapIso (Iso.prod t.unitIso.symm (Iso.refl K)) ≪≫
    (b.calculus T).closed.monoidal.leftUnitor K

/-- The projection arrow is the counit transpose, before any invertibility assertion.
Source: the displayed projection formula (blueprint: proposition-sp-tower-geometric). -/
def projection {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    (N : SpTowerShriek.D l E X) (K : SpTowerShriek.D l E Y) :
    (SpTowerShriek.tensor l E b Y).obj ((SpTowerShriek.push l E b g).obj N, K) ⟶
      (SpTowerShriek.push l E b g).obj
        ((SpTowerShriek.tensor l E b X).obj (N, (SpTowerShriek.pull l E b g).obj K)) :=
  (SpTowerShriek.adjunction l E b g).homEquiv _ _
    (g.tensorPullback.hom.app ((SpTowerShriek.push l E b g).obj N, K) ≫
      (SpTowerShriek.tensor l E b X).map
        (Prod.mkHom ((SpTowerShriek.adjunction l E b g).counit.app N) (𝟙 _)))

/-- The canonical geometric comparisons used in the displayed formulas. Composition
comes from the recorded ordinary system operations. The identity comparison is fixed
at the ordinary sheaf level, where evaluation is faithful; no equality of general
ordinary-derived morphisms is inferred from their levels.
Source: construction paragraphs (blueprint: proposition-sp-tower-geometric). -/
structure Presentation (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) where
  classes : TowerClasses l E S hS
  operations : SpTowerShriek.Operations l E classes.base
  q_geometry : operations.geometry (ProjectiveLine S ↘ S) = classes.projective.geometry
  diagonal_geometry : operations.geometry (diagonalImmersion S) = classes.diagonal.geometry
  tensorS : TensorData l E classes.base S
  tensorP : TensorData l E classes.base (ProjectiveLine S)
  tensorW : TensorData l E classes.base (diagonalSurface S)
  identity : (operations.geometry (𝟙 (ProjectiveLine S))).pull ≅
    𝟭 (SpTowerShriek.S l E (ProjectiveLine S))
  identity_normalization : ∀ (n : ℕ) (M : SpTowerShriek.S l E (ProjectiveLine S)),
    (SpTowerShriek.ev l E (ProjectiveLine S) n).map (identity.hom.app M) =
      ((operations.geometry (𝟙 (ProjectiveLine S))).ordinaryPullEvaluation n).hom.app M ≫
        (proEtaleStalkIdentityPullback (SpTowerShriek.R l E n)
          (ProjectiveLine S)).hom.app ((SpTowerShriek.ev l E (ProjectiveLine S) n).obj M)
  line2 : LinePullback l E
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
    (operations.geometry (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    classes.chernP classes.chernW

variable {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Rq_* in the same recorded system coordinates as the classes.
Source: displayed adjunction (blueprint: proposition-sp-tower-geometric). -/
abbrev Presentation.F (p : Presentation l E S hS) :=
  SpTowerShriek.push l E p.classes.base (p.operations.geometry (ProjectiveLine S ↘ S))

/-- q^*(-)(1)[2], as the existing derived tensor with the shifted line.
Source: displayed adjunction (blueprint: proposition-sp-tower-geometric). -/
def Presentation.G (p : Presentation l E S hS) :=
  SpTowerShriek.pull l E p.classes.base (p.operations.geometry (ProjectiveLine S ↘ S)) ⋙
    Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ⋙
        SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)

/-- Transport of the actual splitting trace along the equality of geometric presentations.
Source: displayed counit (blueprint: proposition-sp-tower-geometric). -/
def Presentation.trace (p : Presentation l E S hS) :
    (p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ⟶
      unit S (Arings l E S) :=
  letI := p.classes.splitting
  (eqToIso (congrArg (SpTowerShriek.push l E p.classes.base) p.q_geometry)).hom.app _ ≫
    p.classes.projective.trace l E

/-- Transport of the actual supported diagonal class, with its Kummer sign.
Source: displayed unit (blueprint: proposition-sp-tower-geometric). -/
def Presentation.delta (p : Presentation l E S hS) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (diagonalImmersion S))).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ⟶
      (line l E p.classes.chernW)⟦(2 : ℤ)⟧ :=
  (eqToIso (congrArg (SpTowerShriek.push l E p.classes.base)
    p.diagonal_geometry)).hom.app _ ≫
      diagonalArrow l E p.classes.chernW p.classes.diagonal.sourceIso

/-- The canonical pullback of the shifted Tate line along p2.
Source: displayed unit, final identification (blueprint: proposition-sp-tower-geometric). -/
def Presentation.line2Iso (p : Presentation l E S hS) :
    (SpTowerShriek.pull l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≅
          (line l E p.classes.chernW)⟦(2 : ℤ)⟧ :=
  ((SpTowerShriek.pull l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).commShiftIso
        (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (p.line2.derivedIso l E)

/-- The restriction of p1 or p2 to the diagonal, localized from ordinary composition.
Source: source identification in the unit (blueprint: proposition-sp-tower-geometric). -/
def Presentation.diagonalPull (p : Presentation l E S hS)
    (r : diagonalSurface S ⟶ ProjectiveLine S)
    (hr : diagonalImmersion S ≫ r = 𝟙 (ProjectiveLine S)) :
    SpTowerShriek.pull l E p.classes.base (p.operations.geometry r) ⋙
      SpTowerShriek.pull l E p.classes.base (p.operations.geometry (diagonalImmersion S)) ≅
        𝟭 (SpTowerShriek.D l E (ProjectiveLine S)) :=
  p.operations.comp (diagonalImmersion S) r ≪≫
    eqToIso (congrArg (fun f ↦ SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry f)) hr) ≪≫
    Functor.mapDerivedCategoryNatIso p.identity ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical composition unit M -> Rp2_* RDelta_* M.
Source: first identification in the displayed unit (blueprint: proposition-sp-tower-geometric). -/
def Presentation.sourceUnit (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    M ⟶ (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((SpTowerShriek.push l E p.classes.base
          (p.operations.geometry (diagonalImmersion S))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base (p.operations.geometry
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).unit.app M ≫
      (SpTowerShriek.push l E p.classes.base (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
          ((SpTowerShriek.adjunction l E p.classes.base
            (p.operations.geometry (diagonalImmersion S))).unit.app _ ≫
              (SpTowerShriek.push l E p.classes.base
                (p.operations.geometry (diagonalImmersion S))).map
                  ((p.diagonalPull l E _ (pullback.diagonal_snd _)).hom.app M))

/-- The proper exchange arrow for the projective-line square: the unit of p2,
the specified pullback square, and the counit of q, in that order.
Source: last identification in the displayed unit (blueprint: proposition-sp-tower-geometric). -/
def Presentation.exchange (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj ((p.F l E).obj M) ⟶
        (SpTowerShriek.push l E p.classes.base (p.operations.geometry
          (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
            ((SpTowerShriek.pull l E p.classes.base (p.operations.geometry
              (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base (p.operations.geometry
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).unit.app _ ≫
      (SpTowerShriek.push l E p.classes.base (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
          ((SpTowerShriek.square l E p.classes.base p.operations
            (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
            (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
              (ProjectiveLine S ↘ S)
              (ProjectiveLine S ↘ S) pullback.condition).hom.app ((p.F l E).obj M) ≫
            (SpTowerShriek.pull l E p.classes.base
              (p.operations.geometry
                (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
                ((SpTowerShriek.adjunction l E p.classes.base
                  (p.operations.geometry (ProjectiveLine S ↘ S))).counit.app M))

/-- Projection across Delta followed by Delta^*p1^*=1 and scalar multiplication.
Its inverse is the source identification before delta tensor identity.
Source: displayed unit, middle arrow (blueprint: proposition-sp-tower-geometric). -/
def Presentation.diagonalProjection (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).obj
      ((SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (diagonalImmersion S))).obj
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
        (SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (pullback.fst (ProjectiveLine S ↘ S)
            (ProjectiveLine S ↘ S)))).obj M) ⟶
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (diagonalImmersion S))).obj M :=
  projection l E (p.operations.geometry (diagonalImmersion S)) _ _ ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (diagonalImmersion S))).map
        ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
          (Prod.mkHom (𝟙 _) ((p.diagonalPull l E _
            (pullback.diagonal_fst _)).hom.app M)) ≫
              (p.tensorP.leftUnit l E M).hom)

/-- The domain-preservation and invertible *specified* projection and exchange maps.
All isomorphisms are constrained by equality with the already defined mate arrows.
Source: construction on C^+ (blueprint: proposition-sp-tower-geometric). -/
structure Maps (p : Presentation l E S hS) where
  push_closed : ∀ M : C l E p.classes.base (ProjectiveLine S),
    domain l E p.classes.base S ((p.F l E).obj M.obj)
  pull_closed : ∀ K : C l E p.classes.base S,
    domain l E p.classes.base (ProjectiveLine S) ((p.G l E).obj K.obj)
  projectionQ : ∀ K : C l E p.classes.base S,
    (SpTowerShriek.tensor l E p.classes.base S).obj
      ((p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧), K.obj) ≅
        (p.F l E).obj ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).obj
          ((line l E p.classes.chernP)⟦(2 : ℤ)⟧,
            (SpTowerShriek.pull l E p.classes.base
              (p.operations.geometry (ProjectiveLine S ↘ S))).obj K.obj))
  projectionQ_eq : ∀ K : C l E p.classes.base S,
    (projectionQ K).hom = projection l E (p.operations.geometry (ProjectiveLine S ↘ S))
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) K.obj
  diagonalProjection : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (p.diagonalProjection l E M.obj)
  exchange : ∀ M : C l E p.classes.base (ProjectiveLine S), IsIso (p.exchange l E M.obj)
  projection2 : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (projection l E (p.operations.geometry (pullback.snd
      (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      ((SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (pullback.fst (ProjectiveLine S ↘ S)
          (ProjectiveLine S ↘ S)))).obj M.obj)
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧))

/-- Restrict Rq_* to the full domain; its morphisms are unchanged.
Source: displayed adjunction (blueprint: proposition-sp-tower-geometric). -/
def left {p : Presentation l E S hS} (d : Maps l E p) :
    C l E p.classes.base (ProjectiveLine S) ⥤ C l E p.classes.base S :=
  ObjectProperty.lift _ ((domain l E p.classes.base (ProjectiveLine S)).ι ⋙ p.F l E)
    d.push_closed

/-- Restrict q^*(-)(1)[2] to the full domain.
Source: displayed adjunction (blueprint: proposition-sp-tower-geometric). -/
def rightRestricted {p : Presentation l E S hS} (d : Maps l E p) :
    C l E p.classes.base S ⥤ C l E p.classes.base (ProjectiveLine S) :=
  ObjectProperty.lift _ ((domain l E p.classes.base S).ι ⋙ p.G l E) d.pull_closed

/-- The exact displayed counit: inverse projection, symmetry, identity tensor trace,
and the scalar-multiplication unitor. No arbitrary counit is selected.
Source: displayed epsilon (blueprint: proposition-sp-tower-geometric). -/
def epsilon {p : Presentation l E S hS} (d : Maps l E p)
    (K : C l E p.classes.base S) : (p.F l E).obj ((p.G l E).obj K.obj) ⟶ K.obj :=
  (p.F l E).map
    (((p.tensorP.symmetry l E).braiding _ _).hom) ≫
      (d.projectionQ K).inv ≫ ((p.tensorS.symmetry l E).braiding _ _).hom ≫
        (SpTowerShriek.tensor l E p.classes.base S).map
          (Prod.mkHom (𝟙 K.obj) (p.trace l E)) ≫ (p.tensorS.rightUnit l E K.obj).hom

/-- The exact displayed unit: composition unit, inverse diagonal projection,
delta tensor identity, the twist-line projection, and inverse proper exchange.
Source: displayed eta (blueprint: proposition-sp-tower-geometric). -/
def eta {p : Presentation l E S hS} (d : Maps l E p)
    (M : C l E p.classes.base (ProjectiveLine S)) : M.obj ⟶
      (p.G l E).obj ((p.F l E).obj M.obj) :=
  letI := d.diagonalProjection M
  letI := d.exchange M
  letI := d.projection2 M
  p.sourceUnit l E M.obj ≫
    (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
        (inv (p.diagonalProjection l E M.obj) ≫
          (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
            (Prod.mkHom (p.delta l E) (𝟙 _)) ≫
              ((p.tensorW.symmetry l E).braiding _ _).hom ≫
                (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
                  (Prod.mkHom (𝟙 _) (p.line2Iso l E).inv)) ≫
      inv (projection l E (p.operations.geometry (pullback.snd
        (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) _ _) ≫
        (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
          (Prod.mkHom (inv (p.exchange l E M.obj)) (𝟙 _))

/-- The bounded-below finite etale-origin domain, using the retained witness interface.
Source: finite evaluations of C^+ (blueprint: proposition-sp-tower-geometric). -/
def finiteDomain (T : Scheme.{u}) (n : ℕ) :
    ObjectProperty (proEtaleDerivedCategory T (SpTowerShriek.R l E n)) :=
  fun K ↦ ∃ V : DerivedCategory.Plus (Sheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))),
      Nonempty (FixedEtaleOriginWitness T (ULift.{u + 1} (SpTowerShriek.R l E n)) V) ∧
        Nonempty
          (((sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory).obj
            V.obj ≅ K)

/-- Finite direct image is the recorded total derived direct image.
Source: evaluation clause (blueprint: proposition-sp-tower-geometric). -/
abbrev finiteF (S : Scheme.{u}) (n : ℕ) :=
  (proEtaleConstantRingPushforward (SpTowerShriek.R l E n)
    (ProjectiveLine S ↘ S)).rightDerivedFunctor

/-- The finite inverse image tensored with the evaluated shifted Tate line.
The line evaluation of TowerClasses identifies this with the usual finite twist.
Source: evaluation clause (blueprint: proposition-sp-tower-geometric). -/
def finiteG (p : Presentation l E S hS) (n : ℕ) :=
  proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) (ProjectiveLine S ↘ S) ⋙
    Prod.sectL (proEtaleDerivedCategory (ProjectiveLine S) (SpTowerShriek.R l E n))
      ((SpTowerShriek.Ev l E (ProjectiveLine S) n).obj
        ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ⋙
      ((p.classes.base.calculus (ProjectiveLine S)).levelClosed n).tensor

/-- Exact evaluation into the finite full domain, retaining its actual level object.
Source: level evaluations (blueprint: proposition-sp-tower-geometric). -/
def evaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (n : ℕ) :
    C l E b T ⥤ (finiteDomain l E T n).FullSubcategory :=
  ObjectProperty.lift _ ((domain l E b T).ι ⋙ SpTowerShriek.Ev l E T n)
    (fun K ↦ ⟨(Classical.choice (K.property.2 n)).level,
      ⟨(Classical.choice (K.property.2 n)).witness⟩,
      ⟨(Classical.choice (K.property.2 n)).realization⟩⟩)

/-- Preservation of the finite domains, with the tensor/pullback evaluation specified
componentwise by the recorded canonical comparisons. No free comparison map is used.
Source: finite-level assertion (blueprint: proposition-sp-tower-geometric). -/
structure FiniteMaps (p : Presentation l E S hS) (n : ℕ) where
  push_closed : ∀ M : (finiteDomain l E (ProjectiveLine S) n).FullSubcategory,
    finiteDomain l E S n ((finiteF l E S n).obj M.obj)
  pull_closed : ∀ K : (finiteDomain l E S n).FullSubcategory,
    finiteDomain l E (ProjectiveLine S) n ((finiteG l E p n).obj K.obj)
  comparison : p.G l E ⋙ SpTowerShriek.Ev l E (ProjectiveLine S) n ≅
    SpTowerShriek.Ev l E S n ⋙ finiteG l E p n
  comparison_eq : ∀ K : SpTowerShriek.D l E S,
    comparison.hom.app K =
      ((p.classes.base.calculus (ProjectiveLine S)).tensorEvaluation n).hom.app
        ((SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (ProjectiveLine S ↘ S))).obj K,
            (line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
        ((p.classes.base.calculus (ProjectiveLine S)).levelClosed n).tensor.map
          (Prod.mkHom
            (((p.operations.geometry (ProjectiveLine S ↘ S)).pullEvaluation n).hom.app K) (𝟙 _))

/-- The finite left functor restricted without changing morphisms.
Source: finite adjunction (blueprint: proposition-sp-tower-geometric). -/
def finiteLeft {p : Presentation l E S hS} {n : ℕ} (d : FiniteMaps l E p n) :=
  ObjectProperty.lift _ ((finiteDomain l E (ProjectiveLine S) n).ι ⋙ finiteF l E S n)
    d.push_closed

/-- The finite right functor restricted without changing morphisms.
Source: finite adjunction (blueprint: proposition-sp-tower-geometric). -/
def finiteRight {p : Presentation l E S hS} {n : ℕ} (d : FiniteMaps l E p n) :=
  ObjectProperty.lift _ ((finiteDomain l E S n).ι ⋙ finiteG l E p n) d.pull_closed

/-- Uniformly bounded constructible finite-Tor towers in the system coordinates.
This is only transport of the recorded predicate, not a second definition of Dctf.
Source: final restriction clause (blueprint: proposition-sp-tower-geometric). -/
def uniform (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) : ObjectProperty (SpTowerShriek.D l E T) :=
  fun K ↦ spConstructibleTorTowers l E T a
    ((spTowerShriekRealization l E b T a).inverse.obj K)

/-- Adjunction with exactly the displayed maps, finite adjunctions with exactly their
evaluations, and preservation of the full uniformly bounded constructible finite-Tor
subcategories in the standing scheme setting. The last preservation statements, together
with fullness, are precisely the restriction of this same adjunction.
Source: all clauses of the statement (blueprint: proposition-sp-tower-geometric). -/
structure AdjunctionData {p : Presentation l E S hS} (d : Maps l E p) where
  adjunction : left l E d ⊣ rightRestricted l E d
  unit_eq : ∀ M : C l E p.classes.base (ProjectiveLine S),
    (domain l E p.classes.base (ProjectiveLine S)).ι.map (adjunction.unit.app M) = eta l E d M
  counit_eq : ∀ K : C l E p.classes.base S,
    (domain l E p.classes.base S).ι.map (adjunction.counit.app K) = epsilon l E d K
  finiteMaps : ∀ n : ℕ, FiniteMaps l E p n
  finiteAdjunction : ∀ n : ℕ, finiteLeft l E (finiteMaps n) ⊣ finiteRight l E (finiteMaps n)
  finite_unit : ∀ (n : ℕ) (M : C l E p.classes.base (ProjectiveLine S)),
    (SpTowerShriek.Ev l E (ProjectiveLine S) n).map (eta l E d M) ≫
      (finiteMaps n).comparison.hom.app ((p.F l E).obj M.obj) ≫
        (finiteG l E p n).map
          (((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).hom.app M.obj) =
      (finiteDomain l E (ProjectiveLine S) n).ι.map
        ((finiteAdjunction n).unit.app
          ((evaluation l E p.classes.base (ProjectiveLine S) n).obj M))
  finite_counit : ∀ (n : ℕ) (K : C l E p.classes.base S),
    (finiteF l E S n).map ((finiteMaps n).comparison.inv.app K.obj) ≫
      ((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).inv.app
        ((p.G l E).obj K.obj) ≫ (SpTowerShriek.Ev l E S n).map (epsilon l E d K) =
      (finiteDomain l E S n).ι.map
        ((finiteAdjunction n).counit.app ((evaluation l E p.classes.base S n).obj K))
  constructible_restriction : ∀ (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar], l ≠ pchar →
    ∀ [S.Over (Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
      (aS : SpCoefficientTowersAbelian l E S)
      (aP : SpCoefficientTowersAbelian l E (ProjectiveLine S)),
      (∀ M : SpTowerShriek.D l E (ProjectiveLine S),
        uniform l E p.classes.base (ProjectiveLine S) aP M →
          domain l E p.classes.base (ProjectiveLine S) M ∧
            uniform l E p.classes.base S aS ((p.F l E).obj M)) ∧
      (∀ K : SpTowerShriek.D l E S, uniform l E p.classes.base S aS K →
        domain l E p.classes.base S K ∧ uniform l E p.classes.base (ProjectiveLine S) aP
          ((p.G l E).obj K))

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
