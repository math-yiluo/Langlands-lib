/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Picard.FiniteOpenProduct.FiniteOpenProductOperations
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-!
# Normalized open external tensor comparison

The auxiliary constructions use ordinary unbounded finite-coefficient categories.
All comparisons are the canonical adjunction, base-change and projection maps.

## References

* Stacks Project, Tags 0GL1, 03S6, 0B65
* Stacks 03DI
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.OpenExternalTensor

open WeilConjectures

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Transport open extension along equality of its geometric map. -/
def shriekCongr {U V : Scheme.{u}} {f g : U ⟶ V}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    finiteShriek A f ≅ finiteShriek A g :=
  eqToIso (by cases h; rfl)

/-- The two chosen intermediate products and all their canonical projection squares.
The outer product cones are specified separately by the final statement. These fields
only record choices of the two factorizations of the product open, with their equations. -/
structure Diagram {X Y Xb Yb : Scheme.{u}} (j : X ⟶ Xb) (k : Y ⟶ Yb)
    (T Tb : Scheme.{u}) [IsOpenImmersion j] [IsOpenImmersion k] where
  S : Scheme.{u}
  S' : Scheme.{u}
  pb : Tb ⟶ Xb
  qb : Tb ⟶ Yb
  p : T ⟶ X
  q : T ⟶ Y
  u : T ⟶ Tb
  r : S ⟶ X
  s : S ⟶ Yb
  j₁ : S ⟶ Tb
  k₁ : T ⟶ S
  r' : S' ⟶ Xb
  s' : S' ⟶ Y
  k₂ : S' ⟶ Tb
  j₂ : T ⟶ S'
  [open_j₁ : IsOpenImmersion j₁]
  [open_k₁ : IsOpenImmersion k₁]
  [open_k₂ : IsOpenImmersion k₂]
  [open_j₂ : IsOpenImmersion j₂]
  [open_u : IsOpenImmersion u]
  first : IsPullback r j₁ j pb
  second : IsPullback q k₁ k s
  first' : IsPullback s' k₂ k qb
  second' : IsPullback p j₂ j r'
  j₁_qb : j₁ ≫ qb = s
  k₁_r : k₁ ≫ r = p
  k₂_pb : k₂ ≫ pb = r'
  j₂_s' : j₂ ≫ s' = q
  factor : k₁ ≫ j₁ = u
  factor' : j₂ ≫ k₂ = u
  left : u ≫ pb = p ≫ j
  right : u ≫ qb = q ≫ k

attribute [instance] Diagram.open_j₁ Diagram.open_k₁
  Diagram.open_k₂ Diagram.open_j₂ Diagram.open_u

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- Swap the factors, on the same chosen fiber product. This means that the swapped
product has already been transported back along its canonical swap isomorphism. -/
def Diagram.swap (d : Diagram j k T Tb) : Diagram k j T Tb where
  S := d.S'
  S' := d.S
  pb := d.qb
  qb := d.pb
  p := d.q
  q := d.p
  u := d.u
  r := d.s'
  s := d.r'
  j₁ := d.k₂
  k₁ := d.j₂
  r' := d.s
  s' := d.r
  k₂ := d.j₁
  j₂ := d.k₁
  first := d.first'
  second := d.second'
  first' := d.first
  second' := d.second
  j₁_qb := d.k₂_pb
  k₁_r := d.j₂_s'
  k₂_pb := d.j₁_qb
  j₂_s' := d.k₁_r
  factor := d.factor'
  factor' := d.factor
  left := d.right
  right := d.left

/-- The ambient external product of the two extensions. -/
def ambient (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : FiniteD A Tb :=
  FiniteOpenProduct.tensor A Tb
    ((FiniteOpenProduct.pull A d.pb).obj ((finiteShriek A j).obj K))
    ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L))

/-- The external product on the open. -/
def inside (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : FiniteD A T :=
  FiniteOpenProduct.tensor A T
    ((FiniteOpenProduct.pull A d.p).obj K) ((FiniteOpenProduct.pull A d.q).obj L)

/-- The prescribed first-factor construction: beta for j, gamma for j₁, beta for k,
then signed symmetry, gamma for k₁, signed symmetry inside k₁!, and the normalized
composition comparison. All equalities are transported by pullback composition. -/
def comparison (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A Tb
      ((ProEtale.ordinaryOpenExtensionBaseChangeIso A
        d.r d.j₁ j d.pb d.first).hom.app K) (𝟙 _) ≫
    FiniteOpenProduct.gamma A d.j₁ ((FiniteOpenProduct.pull A d.r).obj K)
      ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L)) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.tensorMap A d.S (𝟙 _)
        (((FiniteOpenProduct.pullComp A d.j₁ d.qb).symm ≪≫
          eqToIso (congrArg (FiniteOpenProduct.pull A) d.j₁_qb)).hom.app
            ((finiteShriek A k).obj L))) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.tensorMap A d.S (𝟙 _)
        ((ProEtale.ordinaryOpenExtensionBaseChangeIso A
          d.q d.k₁ k d.s d.second).hom.app L)) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.rho A d.k₁
        ((FiniteOpenProduct.pull A d.r).obj K) ((FiniteOpenProduct.pull A d.q).obj L) ≫
        (finiteShriek A d.k₁).map
          (FiniteOpenProduct.tensorMap A T
            (((FiniteOpenProduct.pullComp A d.k₁ d.r).symm ≪≫
              eqToIso (congrArg (FiniteOpenProduct.pull A) d.k₁_r)).hom.app K) (𝟙 _))) ≫
    ((FiniteOpenProduct.comp A d.k₁ d.j₁) ≪≫
      shriekCongr A d.factor).hom.app (inside A d K L)

/-- Identify D with the restriction of H by the inverse tensor comparison, the two
projection squares and the section-normalized open units. -/
def restriction (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A T
    ((FiniteOpenProduct.pull A d.p).map ((FiniteOpenProduct.adj A j).unit.app K) ≫
      (FiniteOpenProduct.square A _ _ _ _ d.left).inv.app ((finiteShriek A j).obj K))
    ((FiniteOpenProduct.pull A d.q).map ((FiniteOpenProduct.adj A k).unit.app L) ≫
      (FiniteOpenProduct.square A _ _ _ _ d.right).inv.app ((finiteShriek A k).obj L)) ≫
    (FiniteOpenProduct.tensorPullIso A d.u _ _).inv

/-- The other factorization, with both signed interchanges in the specified places. -/
def oppositeComparison (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.sigma A Tb _ _ ≫ comparison A d.swap L K ≫
    (finiteShriek A d.u).map (FiniteOpenProduct.sigma A T _ _)

/-- The binary normalization, opposite-factorization and signed-symmetry equations.
The symmetry is written after transporting the swapped products to the same cones. -/
def BinaryAssertion (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : Prop :=
  IsIso (comparison A d K L) ∧ IsIso (oppositeComparison A d K L) ∧
    (restriction A d K L ≫ (FiniteOpenProduct.pull A d.u).map (comparison A d K L) =
      (FiniteOpenProduct.adj A d.u).unit.app (inside A d K L)) ∧
    (oppositeComparison A d K L = comparison A d K L) ∧
    (comparison A d K L ≫ (finiteShriek A d.u).map
        (FiniteOpenProduct.sigma A T
          ((FiniteOpenProduct.pull A d.p).obj K) ((FiniteOpenProduct.pull A d.q).obj L)) =
      FiniteOpenProduct.sigma A Tb
          ((FiniteOpenProduct.pull A d.pb).obj ((finiteShriek A j).obj K))
          ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L)) ≫
        comparison A d.swap L K)

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

open WeilConjectures

end AlgebraicGeometry.ProEtale.OpenExternalTensor
