/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Exchange and projection transformations

Source: Weil blueprint, chap-Smooth-purity, sk-def-sf-operations,
node def-exchange-projection, order 1487 (blueprint: def-exchange-projection).

The finite maps are the existing pro-etale derived exchange, compactification exchange,
and compactification projection maps. The other definitions give the same composites on
supplied domains of operations at a higher coefficient stage. They neither construct those
domains nor assert preservation, invertibility, or independence of the compactification.
Integral operations mean completed operations. Rationalization and the common-field inclusion
apply their functors to these maps; rational coefficients have no finite-reduction functor.

## Main definitions

* `AlgebraicGeometry.ProEtale.coefficientExtensionExchangeProjection`: the finite-level maps.
* `CategoryTheory.ExchangeProjectionStage`: the supplied higher-stage operation data.
* `CategoryTheory.ExchangeProjectionStage.exchange`, `.compactExchange`, `.projection`:
  the three composites on those supplied domains.
* `CategoryTheory.ExchangeProjectionAdjunctionComparison` and
  `CategoryTheory.ExchangeProjectionScalarCocycle`: the required coefficient compatibilities.
-/

@[expose] public section

set_option autoImplicit false

universe u vX vB vY vX' vB' vY' uX uB uY uX' uB' uY'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace CategoryTheory

section SuppliedDomains

variable {DX : Type uX} {DB : Type uB} {DY : Type uY}
  {DX' : Type uX'} {DB' : Type uB'} {DY' : Type uY'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY]
  [Category.{vX'} DX'] [Category.{vB'} DB'] [Category.{vY'} DY']

/-- Compactification exchange from the supplied operation data on closed full domains.
Here `J,J'` are the open extensions, `P,P'` the proper pullbacks, `R,R'` their
right adjoints, and `G,H,B` the three horizontal pullbacks. `theta` is the specified
composition comparison for the proper square; `beta` is the specified open base change.
This is `Ex_{*,p}(j_! K)` followed by `Rp'_*(beta_K)`, with functor associators inserted.
At the integral, rational, and algebraically closed stages these are respectively the
completed, rationalized, and common-finite-field operations supplied by the node.
Source: blueprint, node def-exchange-projection, chosen compactification and other stages
(blueprint: def-exchange-projection). -/
noncomputable def compactificationExchangeFromData
    (J : DX ⥤ DB) (J' : DX' ⥤ DB')
    (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (P' : DY' ⥤ DB') (R' : DB' ⥤ DY') (adj' : P' ⊣ R')
    (G : DY ⥤ DY') (H : DX ⥤ DX') (B : DB ⥤ DB')
    (theta : G ⋙ P' ≅ P ⋙ B) (beta : J ⋙ B ≅ H ⋙ J') :
    (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R') :=
  (Functor.associator J R G).hom ≫
    Functor.whiskerLeft J
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ theta.hom)) ≫
    (Functor.associator J B R').inv ≫
    Functor.whiskerRight beta.hom R' ≫
    (Functor.associator H J' R').hom

/-- Compactification projection from the supplied tensor, adjunction, and comparison data.
`mu` is the tensor-pullback isomorphism for the proper factor. `gamma` is the open
projection isomorphism followed by `Lj^* Lp^* ≅ Lf^*`, with exactly that order.
The first arrow is the existing counit-defined right-adjoint projection mate, so its
transpose is `mu` followed by `epsilon ⊗ 1`. The second arrow is `Rp_*(gamma)`.
No assertion that the resulting natural transformation is invertible is made.
Source: blueprint, node def-exchange-projection, projection and other coefficient stages
(blueprint: def-exchange-projection). -/
noncomputable def compactificationProjectionFromData
    (J : DX ⥤ DB) (F : DY ⥤ DX) (P : DY ⥤ DB) (R : DB ⥤ DY) (adj : P ⊣ R)
    (TX : DX ⥤ DX ⥤ DX) (TB : DB ⥤ DB ⥤ DB) (TY : DY ⥤ DY ⥤ DY)
    (mu : (Functor.postcompose₂.obj P).obj TY ≅
      (((Functor.whiskeringLeft₂ DB).obj P).obj P).obj TB)
    (gamma : (((Functor.whiskeringLeft₂ DB).obj J).obj P).obj TB ≅
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj F).obj TX)) :
    J ⋙ (R ⋙ TY) ⟶
      (Functor.postcompose₂.obj (J ⋙ R)).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj F).obj TX) :=
  Functor.whiskerLeft J (adj.rightAdjointProjectionMap mu.hom) ≫
    (Functor.postcompose₂.obj R).map gamma.hom

/-- The supplied operation and comparison data for one coefficient stage on its closed domains.
The categories are the prescribed full domains, rather than assumed ambient categories on
which higher-coefficient operations need not exist. The fields retain the square pullback
comparison, both adjunctions, the chosen-compactification identifications, and the actual
natural isomorphisms beta, mu, and gamma. These are data, not existence assertions.
Source: blueprint, node def-exchange-projection, other coefficient stages and domains
(blueprint: def-exchange-projection). -/
structure ExchangeProjectionStage where
  pull : DY ⥤ DX
  push : DX ⥤ DY
  adjunction : pull ⊣ push
  pull' : DY' ⥤ DX'
  push' : DX' ⥤ DY'
  adjunction' : pull' ⊣ push'
  horizontal : DY ⥤ DY'
  horizontal' : DX ⥤ DX'
  pullbackComparison : horizontal ⋙ pull' ≅ pull ⋙ horizontal'
  openExtension : DX ⥤ DB
  openExtension' : DX' ⥤ DB'
  properPull : DY ⥤ DB
  properPush : DB ⥤ DY
  properAdjunction : properPull ⊣ properPush
  properPull' : DY' ⥤ DB'
  properPush' : DB' ⥤ DY'
  properAdjunction' : properPull' ⊣ properPush'
  compactifyingHorizontal : DB ⥤ DB'
  properPullbackComparison :
    horizontal ⋙ properPull' ≅ properPull ⋙ compactifyingHorizontal
  openBaseChange : openExtension ⋙ compactifyingHorizontal ≅ horizontal' ⋙ openExtension'
  tensorX : DX ⥤ DX ⥤ DX
  tensorBar : DB ⥤ DB ⥤ DB
  tensorY : DY ⥤ DY ⥤ DY
  tensorPullback : (Functor.postcompose₂.obj properPull).obj tensorY ≅
    (((Functor.whiskeringLeft₂ DB).obj properPull).obj properPull).obj tensorBar
  openProjection :
    (((Functor.whiskeringLeft₂ DB).obj openExtension).obj properPull).obj tensorBar ≅
      (Functor.postcompose₂.obj openExtension).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj pull).obj tensorX)
  compactSupport : DX ⥤ DY
  compactSupport' : DX' ⥤ DY'
  compactSupportIdentification : compactSupport ≅ openExtension ⋙ properPush
  compactSupportIdentification' : compactSupport' ≅ openExtension' ⋙ properPush'

namespace ExchangeProjectionStage

variable (d : ExchangeProjectionStage (DX := DX) (DB := DB) (DY := DY)
  (DX' := DX') (DB' := DB') (DY' := DY'))

/-- Direct-image exchange at a supplied coefficient stage: the specified square mate.
Source: blueprint, node def-exchange-projection, direct-image formula
(blueprint: def-exchange-projection). -/
noncomputable def exchange : d.push ⋙ d.horizontal ⟶ d.horizontal' ⋙ d.push' :=
  (mateEquiv d.adjunction d.adjunction'
    (TwoSquare.mk _ _ _ _ d.pullbackComparison.hom))

/-- Chosen-compactification exchange, transported by the supplied identifications with
proper image after open extension. The formula retains the choice of compactification.
Source: blueprint, node def-exchange-projection, compactification-relative exchange
(blueprint: def-exchange-projection). -/
noncomputable def compactExchange :
    d.compactSupport ⋙ d.horizontal ⟶ d.horizontal' ⋙ d.compactSupport' :=
  Functor.whiskerRight d.compactSupportIdentification.hom d.horizontal ≫
    compactificationExchangeFromData d.openExtension d.openExtension'
      d.properPull d.properPush d.properAdjunction
      d.properPull' d.properPush' d.properAdjunction'
      d.horizontal d.horizontal' d.compactifyingHorizontal
      d.properPullbackComparison d.openBaseChange ≫
    Functor.whiskerLeft d.horizontal' d.compactSupportIdentification'.inv

/-- Chosen-compactification projection on the supplied coefficient domain. Its components
are the counit projection mate followed by the specified open projection comparison.
The endpoint identifications implement the supplied realization of the compact-support
functors as the composite of open extension and proper direct image.
Source: blueprint, node def-exchange-projection, projection formula definition
(blueprint: def-exchange-projection). -/
noncomputable def projection :
    d.compactSupport ⋙ d.tensorY ⟶
      (Functor.postcompose₂.obj d.compactSupport).obj
        ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj d.pull).obj d.tensorX) :=
  Functor.whiskerRight d.compactSupportIdentification.hom d.tensorY ≫
    compactificationProjectionFromData d.openExtension d.pull d.properPull d.properPush
      d.properAdjunction d.tensorX d.tensorBar d.tensorY d.tensorPullback d.openProjection ≫
    (Functor.postcompose₂.map d.compactSupportIdentification.inv).app
      ((((Functor.whiskeringLeft₂ DX).obj (𝟭 DX)).obj d.pull).obj d.tensorX)

end ExchangeProjectionStage

end SuppliedDomains

/-- A supplied change of coefficients carries a specified natural comparison to the
comparison at the new stage. Use this equation for theta, mu, beta, and gamma, inserting
the supplied source and target composite identifications as `source` and `target`.
It also describes finite reduction and rationalization; no rational-to-finite functor
is introduced. Source: blueprint, node def-exchange-projection, coefficient comparisons
(blueprint: def-exchange-projection). -/
def ExchangeProjectionComparisonPreserves
    {C : Type uX} {D : Type uY} {C' : Type uX'} {D' : Type uY'}
    [Category.{vX} C] [Category.{vY} D]
    [Category.{vX'} C'] [Category.{vY'} D']
    (c : C ⥤ C') (d : D ⥤ D')
    {F G : C ⥤ D} {F' G' : C' ⥤ D'}
    (source : F ⋙ d ≅ c ⋙ F') (target : G ⋙ d ≅ c ⋙ G')
    (comparison : F ⟶ G) (comparison' : F' ⟶ G') : Prop :=
  ∀ x : C, d.map (comparison.app x) ≫ target.hom.app x =
    source.hom.app x ≫ comparison'.app (c.obj x)

/-- The units and counits required of supplied operation comparisons under coefficient
change. This is used for each displayed pullback/direct-image adjunction. The same
interface applies to every positive finite reduction of an integral stage and to
scalar extension between finite coefficient fields.
Source: blueprint, node def-exchange-projection, other coefficient stages and domains
(blueprint: def-exchange-projection). -/
structure ExchangeProjectionAdjunctionComparison
    {C : Type uX} {D : Type uY} {C' : Type uX'} {D' : Type uY'}
    [Category.{vX} C] [Category.{vY} D]
    [Category.{vX'} C'] [Category.{vY'} D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (c : C ⥤ C') (d : D ⥤ D') where
  left : L ⋙ d ≅ c ⋙ L'
  right : R ⋙ c ≅ d ⋙ R'
  unit : ∀ x : C,
    c.map (adj.unit.app x) ≫ right.hom.app (L.obj x) ≫ R'.map (left.hom.app x) =
      adj'.unit.app (c.obj x)
  counit : ∀ x : D,
    L'.map (right.hom.app x) ≫ adj'.counit.app (d.obj x) =
      left.inv.app (R.obj x) ≫ d.map (adj.counit.app x)

/-- Identity and tower normalization for the supplied scalar-extension comparisons of
one operation. The transition functors and their identity/composition isomorphisms are
those of rationalization and the common-stage coefficient category, not new choices.
Use the property for every operation/comparison in an exchange-projection stage. For
integral reductions use the opposite ordering on positive exponents: the composition
clause is precisely compatibility with all successive finite transition maps.
The equations retain identity field extensions and arbitrary towers.
Source: blueprint, node def-exchange-projection, scalar-extension cocycle paragraph
(blueprint: def-exchange-projection). -/
structure ExchangeProjectionScalarCocycle
    {I : Type u} [Preorder I]
    (C : I → Type uX) (D : I → Type uY)
    [∀ i : I, Category.{vX} (C i)] [∀ i : I, Category.{vY} (D i)]
    (F : ∀ i : I, C i ⥤ D i)
    (c : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (d : ∀ (i j : I), i ≤ j → D i ⥤ D j)
    (cId : ∀ i : I, c i i le_rfl ≅ 𝟭 (C i))
    (dId : ∀ i : I, d i i le_rfl ≅ 𝟭 (D i))
    (cComp : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      c i j h ⋙ c j k h' ≅ c i k (h.trans h'))
    (dComp : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      d i j h ⋙ d j k h' ≅ d i k (h.trans h'))
    (comparison : ∀ (i j : I) (h : i ≤ j), F i ⋙ d i j h ≅ c i j h ⋙ F j) : Prop where
  identity : ∀ (i : I) (x : C i),
    (comparison i i le_rfl).hom.app x ≫ (F i).map ((cId i).hom.app x) =
      (dId i).hom.app ((F i).obj x)
  composition : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (x : C i),
    (d j k h').map ((comparison i j h).hom.app x) ≫
        (comparison j k h').hom.app ((c i j h).obj x) ≫
        (F k).map ((cComp i j k h h').hom.app x) =
      (dComp i j k h h').hom.app ((F i).obj x) ≫
        (comparison i k (h.trans h')).hom.app x

end CategoryTheory
