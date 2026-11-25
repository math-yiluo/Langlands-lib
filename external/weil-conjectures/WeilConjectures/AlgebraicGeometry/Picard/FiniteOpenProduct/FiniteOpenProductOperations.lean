/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Canonical finite open product operations

We use the fixed-scalar presentation `FiniteD` of the ordinary constant-coefficient
module derived category, with its canonical intrinsic realization from the open
normalization dependency. Exact inverse image is localized termwise and identified
with its K-flat left derived functor. Tensor and symmetry are the K-flat ones.

## Main definitions and statement

- `comparison` and `comparisonOp`: the two specified factorization chains.
- `transportedReverse`: the reversed construction transported by the actual swaps.
- `restrictionSource`: the identification supplied by the two specified open units.
The theorem about these operations is in `FiniteOpenProductSwap`.

`product` names Mathlib's chosen pullback without unfolding its construction during
kernel checking. Its two projections and swap are the existing Mathlib morphisms.

## References

* Stacks 0GL1
* Stacks 06YS
* Stacks 07A4
* Stacks 03DI
* Stacks 03S6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace WeilConjectures.FiniteOpenProduct

/-- The chosen fibre-product object, kept named while deriving its operations. -/
@[irreducible]
def product {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : Scheme.{u} :=
  pullback a b

/-- First projection of the chosen product. -/
def first {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ⟶ T := by
  unfold product
  exact pullback.fst a b

/-- Second projection of the chosen product. -/
def second {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ⟶ U := by
  unfold product
  exact pullback.snd a b

/-- The actual swap of the two chosen fibre products. -/
def swap {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ≅ product b a := by
  unfold product
  exact pullbackSymmetry a b

/-- Evaluate the canonical K-flat Koszul braiding on a pro-etale coefficient category. -/
def proetSigma (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalClosed V]
    [MonoidalPreadditive V] [SymmetricCategory V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u}) (M N : DerivedCategory (Sheaf (ProEt.topology Y) V)) :
    ((ProEtale.derivedTensor V Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor V Y).obj N).obj M :=
  (DerivedCategory.braidedCategory' (Sheaf (ProEt.topology Y) V)).braiding M N |>.hom

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The derived tensor, with its coefficient specialization named. -/
abbrev tensor (Y : Scheme.{u}) (M N : FiniteD A Y) : FiniteD A Y :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj N

/-- Map both arguments of the derived tensor bifunctor. -/
def tensorMap (Y : Scheme.{u}) {M M' N N' : FiniteD A Y}
    (f : M ⟶ M') (g : N ⟶ N') : tensor A Y M N ⟶ tensor A Y M' N' :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).map f).app N ≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M').map g

/-- Map two isomorphisms under the same derived tensor bifunctor. -/
def tensorIsoMap (Y : Scheme.{u}) {M M' N N' : FiniteD A Y}
    (f : M ≅ M') (g : N ≅ N') : tensor A Y M N ≅ tensor A Y M' N' :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).mapIso f).app N ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M').mapIso g

/-- Exact inverse image on complexes, with its canonical K-flat derived identification. -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : FiniteD A Y ⥤ FiniteD A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- Tensor comparison for exact inverse image, with its canonical derived identification. -/
def tensorPullIso {T U : Scheme.{u}} (f : T ⟶ U) (M N : FiniteD A U) :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) f).symm.app (tensor A U M N) ≪≫
    ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f M N ≪≫
      tensorIsoMap A T
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).app M)
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).app N)

/-- The open adjunction, using the canonical exact/left-derived identification. -/
def adj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    finiteShriek A j ⊣ pull A j :=
  ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j

/-- Composition for exact pullback, induced termwise before localization. -/
def pullComp {T U X : Scheme.{u}} (i : T ⟶ U) (j : U ⟶ X) :
    pull A (i ≫ j) ≅ pull A j ⋙ pull A i :=
  Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp (ModuleCat.{u + 1} A) i j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Geometric equality induces equality of the exact pullback functors. -/
def pullCongr {T X : Scheme.{u}} {f g : T ⟶ X} (w : f = g) : pull A f ≅ pull A g :=
  w ▸ Iso.refl _

/-- Unit-compatible composition of exact open extensions, descended termwise. -/
def comp {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    finiteShriek A i ⋙ finiteShriek A j ≅ finiteShriek A (i ≫ j) :=
  (((adj A i).comp (adj A j)).ofNatIsoRight
    (pullComp A i j).symm).leftAdjointUniq
      (adj A (i ≫ j))

/-- Canonical pullback composition along an equality of geometric composites. -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (w : f ≫ g = h ≫ i) :
    pull A g ⋙ pull A f ≅ pull A i ⋙ pull A h :=
  (pullComp A f g).symm ≪≫
    pullCongr A w ≪≫
      pullComp A h i

/-- Compose the canonical pullback comparison with a geometric projection equality. -/
def composeEq {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : T ⟶ Y) (w : f ≫ g = h) : pull A g ⋙ pull A f ≅ pull A h :=
  (pullComp A f g).symm ≪≫
    pullCongr A w

/-- Open base change with the exact/left-derived comparisons made explicit.
Its inverse is the normalized open-unit mate, as in the normalization dependency. -/
def beta {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback gU j' j g) :
    finiteShriek A j ⋙ pull A g ≅ pull A gU ⋙ finiteShriek A j' :=
  ProEtale.ordinaryOpenExtensionBaseChangeIso A gU j' j g s

/-- The actual normalized open tensor comparison, in extension-first order. -/
def gamma {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A X) :=
  finiteGamma A j M N ≫
    (finiteShriek A j).map
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj M).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) j).hom.app N))

/-- The canonical Koszul braiding descended from the homotopy category. -/
def sigma (Y : Scheme.{u}) (M N : FiniteD A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj N).obj M :=
  proetSigma (ModuleCat.{u + 1} A) Y M N

/-- Right-extension order uses both signed symmetries, rather than an unsigned flip. -/
def rho {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A X) (N : FiniteD A U) :=
  sigma A _ M ((finiteShriek A j).obj N) ≫ gamma A j N M ≫
    (finiteShriek A j).map (sigma A _ N ((pull A j).obj M))

variable {Xb Zb B X Z : Scheme.{u}}

/-- The first open on a product, formed by the chosen fibre-product functor. -/
def leftOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) :
    product (j ≫ a) b ⟶ product a b := by
  unfold product
  exact pullback.map (j ≫ a) b a b j (𝟙 Zb) (𝟙 B) (by simp) (by simp)

/-- The second open on a product, formed by the same fibre-product functor. -/
def rightOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) :
    product a (k ≫ b) ⟶ product a b := by
  unfold product
  exact pullback.map a (k ≫ b) a b (𝟙 Xb) k (𝟙 B) (by simp) (by simp)

/-- The first open on a product is an open immersion, as a base change of `j`. -/
instance leftOpen_isOpenImmersion (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] : IsOpenImmersion (leftOpen a b j) := by
  unfold leftOpen product
  exact Scheme.pullback_map_isOpenImmersion (j ≫ a) b a b j (𝟙 Zb) (𝟙 B) (by simp) (by simp)

/-- The second open on a product is an open immersion, as a base change of `k`. -/
instance rightOpen_isOpenImmersion (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb)
    [IsOpenImmersion k] : IsOpenImmersion (rightOpen a b k) := by
  unfold rightOpen product
  exact Scheme.pullback_map_isOpenImmersion a (k ≫ b) a b (𝟙 Xb) k (𝟙 B) (by simp) (by simp)

set_option linter.defProp false in
/-- Product base change for the first open, with its two projection equations. -/
def leftSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) :
    IsPullback (first (j ≫ a) b) (leftOpen a b j) j (first a b) := by
  unfold first leftOpen product
  dsimp only [id_eq]
  have h : IsPullback
      (pullback.map (j ≫ a) b a b j (𝟙 Zb) (𝟙 B) (by simp) (by simp) ≫
        pullback.snd a b) (pullback.fst (j ≫ a) b) b (j ≫ a) := by
    simpa using (IsPullback.of_hasPullback (j ≫ a) b).flip
  exact (h.of_right (by simp) (IsPullback.of_hasPullback a b).flip).flip

/-- The first base-change step, tensored with the untouched second pullback. -/
def leftBeta (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] (M : FiniteD A X) (N : FiniteD A Zb) :=
  tensorMap A (product a b) ((beta A _ _ _ _ (leftSquare a b j)).hom.app M)
    (𝟙 ((pull A (second a b)).obj N))

/-- Tensor the projection-composition comparison at an abstract geometric corner. -/
def projectionTensor {V C T U : Scheme.{u}} (v : V ⟶ C) (t : C ⟶ T)
    (p : V ⟶ U) (q : V ⟶ T) (h : v ≫ t = q)
    (M : FiniteD A U) (N : FiniteD A T) :
    tensor A V ((pull A p).obj M) ((pull A v).obj ((pull A t).obj N)) ⟶
      tensor A V ((pull A p).obj M) ((pull A q).obj N) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj ((pull A p).obj M)).map
    ((composeEq A v t q h).hom.app N)

/-- Extend the projection-tensor comparison at the same abstract corner. -/
def extendedProjectionTensor {V C T U : Scheme.{u}} (v : V ⟶ C) [IsOpenImmersion v]
    (t : C ⟶ T) (p : V ⟶ U) (q : V ⟶ T) (h : v ≫ t = q)
    (M : FiniteD A U) (N : FiniteD A T) :
    (finiteShriek A v).obj
      (tensor A V ((pull A p).obj M) ((pull A v).obj ((pull A t).obj N))) ⟶
    (finiteShriek A v).obj (tensor A V ((pull A p).obj M) ((pull A q).obj N)) :=
  (finiteShriek A v).map (projectionTensor A v t p q h M N)

/-- The specified first-factor comparison, beta followed by gamma and projections. -/
def leftComparison (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] (M : FiniteD A X) (N : FiniteD A Zb) :=
  leftBeta A a b j M N ≫
    gamma A (leftOpen a b j) ((pull A (first (j ≫ a) b)).obj M)
      ((pull A (second a b)).obj N) ≫ extendedProjectionTensor A (leftOpen a b j) (second a b)
        (first (j ≫ a) b) (second (j ≫ a) b) (by
          unfold leftOpen second product
          dsimp only [id_eq]
          simp) M N

set_option linter.defProp false in
/-- Product base change for the second open. -/
def rightSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) :
    IsPullback (second a (k ≫ b)) (rightOpen a b k) k (second a b) := by
  unfold second rightOpen product
  dsimp only [id_eq]
  have h : IsPullback
      (pullback.map a (k ≫ b) a b (𝟙 Xb) k (𝟙 B) (by simp) (by simp) ≫
        pullback.fst a b) (pullback.snd a (k ≫ b)) a (k ≫ b) := by
    simpa using (IsPullback.of_hasPullback a (k ≫ b))
  exact (h.of_right (by simp) (IsPullback.of_hasPullback a b)).flip

/-- The one-factor comparison with the extension in the right factor.
The rho composite includes its two Koszul symmetries explicitly. -/
def rightComparison (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb)
    [IsOpenImmersion k] (M : FiniteD A Xb) (N : FiniteD A Z) :=
  tensorMap A (product a b) (𝟙 ((pull A (first a b)).obj M))
      ((beta A _ _ _ _ (rightSquare a b k)).hom.app N) ≫
    rho A (rightOpen a b k) ((pull A (first a b)).obj M)
      ((pull A (second a (k ≫ b))).obj N) ≫
      (finiteShriek A (rightOpen a b k)).map
        (tensorMap A _ ((composeEq A (rightOpen a b k) (first a b)
          (first a (k ≫ b)) (by
            unfold rightOpen first product
            dsimp only [id_eq]
            simp)).hom.app M)
          (𝟙 ((pull A (second a (k ≫ b))).obj N)))

/-- The actual product open immersion u=j times k, on the chosen fibre products. -/
def productOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb) :
    product (j ≫ a) (k ≫ b) ⟶ product a b := by
  unfold product
  exact pullback.map (j ≫ a) (k ≫ b) a b j k (𝟙 B) (by simp) (by simp)

/-- The product open is an open immersion when both factors are. -/
instance productOpen_isOpenImmersion (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] : IsOpenImmersion (productOpen a b j k) := by
  unfold productOpen product
  exact Scheme.pullback_map_isOpenImmersion (j ≫ a) (k ≫ b) a b j k (𝟙 B) (by simp) (by simp)

/-- The canonical compositor, followed only by a geometric equality of open maps. -/
def compTo {T U Y : Scheme.{u}} (i : T ⟶ U) (j : U ⟶ Y) (h : T ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion h] (w : i ≫ j = h) :
    finiteShriek A i ⋙ finiteShriek A j ≅ finiteShriek A h :=
  comp A i j ≪≫ (by
    subst h
    exact Iso.refl _)

/-- The specified first-factor-then-second-factor external product map e.
Every factor is the actual normalized beta, gamma, signed rho or open compositor. -/
def comparison (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :=
  leftComparison A a b j M ((finiteShriek A k).obj N) ≫
    (finiteShriek A (leftOpen a b j)).map (rightComparison A (j ≫ a) b k M N) ≫
      (compTo A (rightOpen (j ≫ a) b k) (leftOpen a b j) (productOpen a b j k)
        (by
          unfold rightOpen leftOpen productOpen product
          dsimp only [id_eq]
          apply pullback.hom_ext <;> simp)).hom.app _

end WeilConjectures.FiniteOpenProduct
