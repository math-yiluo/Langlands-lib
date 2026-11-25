/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift

/-! # Strict Roos cone calculus

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-lem-pe-derived-nakayama-first-reduction, Cones paragraph; Stacks Tags 08TC,
07KC, 014E and 011G (blueprint: lem-pe-roos-cone-calculus).

The construction is `CategoryTheory.roosF`, without a second Roos model.
The helper predicates specify its comparisons by their actual component maps.
Natural-number level n means the positive level n+1 of the blueprint.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex

universe a b t u w

namespace CategoryTheory.RoosConeCalculus

section Coordinates
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The product projection in a specified degree. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :=
  (Pi.π (fun n : ℕ => N.asFunctor.obj (op n)) n).f q

/-- The coordinate v of the existing Roos fibre. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :=
  (roosProj N).f q

/-- The coordinate u of the existing Roos fibre. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev ucoord (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) : (roosF.obj N).X q ⟶ (roosP N).X p :=
  (mappingCocone.snd (roosU N)).v q p (by omega)

/-- The target coordinate of a cone. Source: Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev coneTarget {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ) :=
  (mappingCone.snd f).v q q (add_zero q)

/-- The source coordinate of a cone. Source: Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev coneSource {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q p : ℤ) (h : q + 1 = p) :=
  (mappingCone.fst f).1.v q p h

/-- Four projection equations for (b,a,b',a') ↦ (b,b',a,-a').
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-roos-cone-calculus). -/
def ConeFormula {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (e : roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f)) : Prop :=
  ∀ (q : ℤ) (n : ℕ),
    (e.hom.f q ≫ coneTarget (roosF.map f) q ≫ v N' q ≫ π N' q n =
      v (mappingCone f) q ≫ π (mappingCone f) q n ≫ (coneTarget f q).app (op n)) ∧
    (e.hom.f q ≫ coneTarget (roosF.map f) q ≫ ucoord N' q (q - 1) rfl ≫
        π N' (q - 1) n =
      ucoord (mappingCone f) q (q - 1) rfl ≫ π (mappingCone f) (q - 1) n ≫
        (coneTarget f (q - 1)).app (op n)) ∧
    (e.hom.f q ≫ coneSource (roosF.map f) q (q + 1) rfl ≫
        v N (q + 1) ≫ π N (q + 1) n =
      v (mappingCone f) q ≫ π (mappingCone f) q n ≫
        (coneSource f q (q + 1) rfl).app (op n)) ∧
    (e.hom.f q ≫ coneSource (roosF.map f) q (q + 1) rfl ≫
        ucoord N (q + 1) q (by omega) ≫ π N q n =
      -(ucoord (mappingCone f) q (q - 1) rfl ≫ π (mappingCone f) (q - 1) n ≫
        (coneSource f (q - 1) q (by omega)).app (op n)))

/-- The component equations for the signed coherent shift comparison.
Source: Stacks 011G and blueprint Cones paragraph
(blueprint: lem-pe-roos-cone-calculus). -/
def ShiftFormula (cs : (roosF (A := A)).CommShift ℤ) : Prop :=
  ∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) (n : ℕ),
    (((Functor.commShiftIso roosF (self := cs) r).hom.app N).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        v N (q + r) ≫ π N (q + r) n =
      v (N⟦r⟧) q ≫ π (N⟦r⟧) q n ≫
        ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n)) ∧
    (((Functor.commShiftIso roosF (self := cs) r).hom.app N).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) ((q - 1) + r) (by omega) ≫ π N ((q - 1) + r) n =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫ π (N⟦r⟧) (q - 1) n ≫
        ((shiftFunctorObjXIso N r (q - 1) ((q - 1) + r) rfl).hom).app (op n)))

/-- A cone over the evaluated tower has its already defined strict augmentation.
Source: blueprint Cones paragraph; Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev augmentation {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (j : Cone N.asFunctor) : j.pt ⟶ roosF.obj N :=
  roosAugment (fun n => j.π.app (op n)) (fun n => by
    exact j.w (homOfLE (Nat.le_succ n)).op)

/-- Compatibility of maps between augmented towers, before taking fibres.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def AugmentedSquare {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt) : Prop :=
  ∀ n : ℕ, j.π.app (op n) ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) =
      g ≫ j'.π.app (op n)

/-- Naturality of zero-second-coordinate augmentations.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def AugmentationNaturality (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] : Prop :=
  ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt),
    AugmentedSquare f j j' g →
      augmentation j ≫ roosF.map f = g ≫ augmentation j'

/-- Naturality and preservation of inclusion and the signed cone boundary.
Source: blueprint Cones paragraph and Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
def ConeCompatibility (cs : (roosF (A := A)).CommShift ℤ)
    (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f)) : Prop :=
  (∀ {N N' M M' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (g : M ⟶ M') (α : N ⟶ M) (β : N' ⟶ M')
    (h : f ≫ β = α ≫ g),
    roosF.map (mappingCone.map f g α β h) ≫ (e g).hom =
      (e f).hom ≫ mappingCone.map (roosF.map f) (roosF.map g)
        (roosF.map α) (roosF.map β)
        (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ∧
  (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
    (roosF.map (mappingCone.inr f) ≫ (e f).hom = mappingCone.inr (roosF.map f)) ∧
    (roosF.map (mappingCone.triangle f).mor₃ ≫
        (Functor.commShiftIso roosF (self := cs) (1 : ℤ)).hom.app N =
      (e f).hom ≫ (mappingCone.triangle (roosF.map f)).mor₃))

/-- Cone augmentations are the induced cone maps of the two strict augmentations.
The hypotheses specify exactly the two levelwise cone coordinates.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def ConeAugmentation
    (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
    (hnat : AugmentationNaturality A) : Prop :=
  ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt)
    (h : AugmentedSquare f j j' g)
    (jc : Cone (mappingCone f).asFunctor) (c : mappingCone g ⟶ jc.pt),
    (∀ (q : ℤ) (n : ℕ),
      ((c ≫ jc.π.app (op n)).f q ≫ (coneTarget f q).app (op n) =
        coneTarget g q ≫ (j'.π.app (op n)).f q) ∧
      ((c ≫ jc.π.app (op n)).f q ≫ (coneSource f q (q + 1) rfl).app (op n) =
        coneSource g q (q + 1) rfl ≫ (j.π.app (op n)).f (q + 1))) →
    c ≫ augmentation jc ≫ (e f).hom =
      mappingCone.map g (roosF.map f) (augmentation j) (augmentation j')
        (hnat f j j' g h).symm

/-- Induced shifted augmentations commute with the coherent comparison.
Source: blueprint Cones paragraph and Stacks 011G
(blueprint: lem-pe-roos-cone-calculus). -/
def ShiftAugmentation (cs : (roosF (A := A)).CommShift ℤ) : Prop :=
  ∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : Cone N.asFunctor) (r : ℤ)
    (js : Cone (N⟦r⟧).asFunctor) (c : js.pt ⟶ j.pt⟦r⟧),
    (∀ (q : ℤ) (n : ℕ),
      (js.π.app (op n)).f q ≫
          ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n) =
        c.f q ≫ (shiftFunctorObjXIso j.pt r q (q + r) rfl).hom ≫
          (j.π.app (op n)).f (q + r)) →
    augmentation js ≫ (Functor.commShiftIso roosF (self := cs) r).hom.app N =
      c ≫ (augmentation j)⟦r⟧'

/-- The actual differential, diagonal maps and zero-second-coordinate augmentation.
Source: blueprint Cones paragraph; Stacks 014E, 011G and 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
def CoordinateCalculus (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] : Prop :=
  (∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ),
    ((roosF.obj N).d q (q + 1) ≫ v N (q + 1) =
      v N q ≫ (roosP N).d q (q + 1)) ∧
    ((roosF.obj N).d q (q + 1) ≫ ucoord N (q + 1) q (by omega) =
      -(ucoord N q (q - 1) rfl ≫ (roosP N).d (q - 1) q) -
        v N q ≫ (roosU N).f q)) ∧
  (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (q : ℤ),
    ((roosF.map f).f q ≫ v N' q = v N q ≫ (roosPmap f).f q) ∧
    ((roosF.map f).f q ≫ ucoord N' q (q - 1) rfl =
      ucoord N q (q - 1) rfl ≫ (roosPmap f).f (q - 1))) ∧
  (∀ {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (j : Cone N.asFunctor) (q : ℤ),
    ((augmentation j).f q ≫ v N q = (Pi.lift (fun n => j.π.app (op n))).f q) ∧
    ((augmentation j).f q ≫ ucoord N q (q - 1) rfl = 0))

/-- The localized triangle uses the actual localized termwise product projections.
It is a Roos triangle for the tower, with its product identified by those projections.
Source: Stacks 08TC and 07KC (blueprint: lem-pe-roos-cone-calculus). -/
def DerivedRoos [HasDerivedCategory.{w} A]
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Prop :=
  Nonempty (IsLimit (DerivedCategory.Q.mapCone
    (limit.cone (Discrete.functor (fun n : ℕ => N.asFunctor.obj (op n)))))) ∧
  DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (roosU N)) ∈
    distTriang (DerivedCategory A) ∧
  ∀ (_h : HasProduct (fun n : ℕ => DerivedCategory.Q.obj (N.asFunctor.obj (op n)))),
    IsDerivedLimit (K := fun n : ℕ => DerivedCategory.Q.obj (N.asFunctor.obj (op n)))
      (fun n : ℕ => DerivedCategory.Q.map
        (N.asFunctor.map (homOfLE (Nat.le_succ n)).op))
      (DerivedCategory.Q.obj (roosF.obj N))

private noncomputable def productLimit (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    IsLimit (Fan.mk ((roosP N).X q) (π N q)) :=
  isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    (fun n : ℕ ↦ N.asFunctor.obj (op n))

private theorem product_ext (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ)
    {T : A} {f g : T ⟶ (roosP N).X q}
    (h : ∀ n : ℕ, f ≫ π N q n = g ≫ π N q n) : f = g := by
  apply (productLimit N q).hom_ext
  rintro ⟨n⟩
  exact h n

private noncomputable def productLift (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ)
    {T : A} (f : ∀ n : ℕ, T ⟶ (N.asFunctor.obj (op n)).X q) : T ⟶ (roosP N).X q :=
  (productLimit N q).lift (Fan.mk T f)

@[reassoc (attr := simp)]
private theorem productLift_π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ)
    {T : A} (f : ∀ n : ℕ, T ⟶ (N.asFunctor.obj (op n)).X q) (n : ℕ) :
    productLift N q f ≫ π N q n = f n :=
  (productLimit N q).fac (Fan.mk T f) ⟨n⟩

-- Keep chosen product cones behind their projection API during later elaboration.
attribute [local irreducible] productLimit productLift

private noncomputable def fibrePair (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) {T : A}
    (a : T ⟶ (roosP N).X q) (b : T ⟶ (roosP N).X p) : T ⟶ (roosF.obj N).X q :=
  a ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
    b ≫ (mappingCocone.inr (roosU N)).1.v p q (by omega)

@[reassoc (attr := simp)]
private theorem fibrePair_v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) {T : A}
    (a : T ⟶ (roosP N).X q) (b : T ⟶ (roosP N).X p) :
    fibrePair N q p h a b ≫ v N q = a := by
  change (a ≫ _ + b ≫ _) ≫ (mappingCocone.fst (roosU N)).f q = a
  simp [Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
private theorem fibrePair_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) {T : A}
    (a : T ⟶ (roosP N).X q) (b : T ⟶ (roosP N).X p) :
    fibrePair N q p h a b ≫ ucoord N q p h = b := by
  simp [fibrePair, ucoord, Preadditive.add_comp, Category.assoc]

attribute [local irreducible] fibrePair

private noncomputable def conePair {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q p : ℤ) (h : q + 1 = p)
    {T : B} (a : T ⟶ K.X p) (b : T ⟶ L.X q) : T ⟶ (mappingCone f).X q :=
  a ≫ (mappingCone.inl f).v p q (by omega) + b ≫ (mappingCone.inr f).f q

@[reassoc (attr := simp)]
private theorem conePair_target {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q p : ℤ) (h : q + 1 = p)
    {T : B} (a : T ⟶ K.X p) (b : T ⟶ L.X q) :
    conePair f q p h a b ≫ coneTarget f q = b := by
  simp [conePair, coneTarget, Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
private theorem conePair_source {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q p : ℤ) (h : q + 1 = p)
    {T : B} (a : T ⟶ K.X p) (b : T ⟶ L.X q) :
    conePair f q p h a b ≫ coneSource f q p h = a := by
  simp [conePair, coneSource, Preadditive.add_comp, Category.assoc]

attribute [local irreducible] conePair

private noncomputable def productTarget {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) : (roosP (mappingCone f)).X q ⟶ (roosP N').X q :=
  productLift N' q (fun n ↦ π (mappingCone f) q n ≫ (coneTarget f q).app (op n))

private noncomputable def productSource {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (h : q + 1 = p) :
    (roosP (mappingCone f)).X q ⟶ (roosP N).X p :=
  productLift N p (fun n ↦ π (mappingCone f) q n ≫
    (coneSource f q p h).app (op n))

@[reassoc (attr := simp)]
private theorem productTarget_π {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) (n : ℕ) :
    productTarget f q ≫ π N' q n =
      π (mappingCone f) q n ≫ (coneTarget f q).app (op n) := by
  apply productLift_π

@[reassoc (attr := simp)]
private theorem productSource_π {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (h : q + 1 = p) (n : ℕ) :
    productSource f q p h ≫ π N p n =
      π (mappingCone f) q n ≫ (coneSource f q p h).app (op n) := by
  apply productLift_π

@[reassoc (attr := simp)]
private theorem π_d (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q p : ℤ) (n : ℕ) :
    (roosP N).d q p ≫ π N p n = π N q n ≫ (N.d q p).app (op n) :=
  ((Pi.π (fun n : ℕ ↦ N.asFunctor.obj (op n)) n).comm q p).symm

@[reassoc (attr := simp)]
private theorem π_map {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) (n : ℕ) :
    (roosPmap f).f q ≫ π N' q n = π N q n ≫ (f.f q).app (op n) :=
  congrArg (fun f ↦ f.f q) (Pi.map_π
    (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) n)

@[reassoc (attr := simp)]
private theorem π_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :
    (roosU N).f q ≫ π N q n = π N q n -
      π N q (n + 1) ≫ (N.asFunctor.map (homOfLE (Nat.le_succ n)).op).f q :=
  congrArg (fun f ↦ f.f q)
    ((towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ N.asFunctor.obj (op n))
      (fun n : ℕ ↦ N.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n)

private theorem productTarget_d {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    (roosP (mappingCone f)).d q (q + 1) ≫ productTarget f (q + 1) =
      productSource f q (q + 1) rfl ≫ (roosPmap f).f (q + 1) +
        productTarget f q ≫ (roosP N').d q (q + 1) := by
  apply product_ext N' (q + 1)
  intro n
  have h := congrArg (fun k ↦ k.app (op n)) (mappingCone.d_snd_v f q (q + 1) rfl)
  simp only [NatTrans.comp_app, NatTrans.app_add] at h
  simpa only [Category.assoc, productTarget_π, productSource_π, π_map,
    Preadditive.add_comp, π_d_assoc, π_d, productSource_π_assoc,
    productTarget_π_assoc, Preadditive.comp_add, coneTarget, coneSource] using
    congrArg (fun k ↦ π (mappingCone f) q n ≫ k) h

private theorem productTarget_d_at {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (h : q + 1 = p) :
    (roosP (mappingCone f)).d q p ≫ productTarget f p =
      productSource f q p h ≫ (roosPmap f).f p +
        productTarget f q ≫ (roosP N').d q p := by
  subst p
  exact productTarget_d f q

private theorem productSource_d {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p r : ℤ) (hqp : q + 1 = p) (hpr : p + 1 = r) :
    (roosP (mappingCone f)).d q p ≫ productSource f p r hpr =
      -(productSource f q p hqp ≫ (roosP N).d p r) := by
  apply product_ext N r
  intro n
  have h := congrArg (fun k ↦ k.app (op n)) (mappingCone.d_fst_v f q p r hqp hpr)
  simp only [NatTrans.comp_app, NatTrans.app_neg] at h
  simpa only [Category.assoc, productSource_π, Preadditive.neg_comp,
    π_d_assoc, π_d, productSource_π_assoc, Preadditive.comp_neg, coneSource] using
    congrArg (fun k ↦ π (mappingCone f) q n ≫ k) h

private theorem productTarget_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    (roosU (mappingCone f)).f q ≫ productTarget f q =
      productTarget f q ≫ (roosU N').f q := by
  apply product_ext N' q
  intro n
  simp only [Category.assoc, productTarget_π, π_u, π_u_assoc,
    Preadditive.comp_sub, Preadditive.sub_comp, productTarget_π_assoc]
  congr 1
  simpa only [Category.assoc, HomologicalComplex.asFunctor] using
    congrArg (fun k ↦ π (mappingCone f) q (n + 1) ≫ k)
      ((coneTarget f q).naturality (homOfLE (Nat.le_succ n)).op)

private theorem productSource_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (h : q + 1 = p) :
    (roosU (mappingCone f)).f q ≫ productSource f q p h =
      productSource f q p h ≫ (roosU N).f p := by
  apply product_ext N p
  intro n
  simp only [Category.assoc, productSource_π, π_u, π_u_assoc,
    Preadditive.comp_sub, Preadditive.sub_comp, productSource_π_assoc]
  congr 1
  simpa only [Category.assoc, HomologicalComplex.asFunctor] using
    congrArg (fun k ↦ π (mappingCone f) q (n + 1) ≫ k)
      ((coneSource f q p h).naturality (homOfLE (Nat.le_succ n)).op)

attribute [local irreducible] productTarget productSource

private noncomputable def productPair
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (q p : ℤ) (h : q + 1 = p) {T : A}
    (a : T ⟶ (roosP N).X p) (b : T ⟶ (roosP N').X q) :
    T ⟶ (roosP (mappingCone f)).X q :=
  productLift (mappingCone f) q (fun n ↦
    a ≫ π N p n ≫ ((mappingCone.inl f).v p q (by omega)).app (op n) +
      b ≫ π N' q n ≫ ((mappingCone.inr f).f q).app (op n))

@[reassoc (attr := simp)]
private theorem productPair_target
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (q p : ℤ) (h : q + 1 = p) {T : A}
    (a : T ⟶ (roosP N).X p) (b : T ⟶ (roosP N').X q) :
    productPair f q p h a b ≫ productTarget f q = b := by
  apply product_ext N' q
  intro n
  simp only [Category.assoc, productTarget_π, productPair, productLift_π_assoc,
    Preadditive.add_comp]
  have h₁ := congrArg (fun k ↦ k.app (op n)) (mappingCone.inl_v_snd_v f p q (by omega))
  have h₂ := congrArg (fun k ↦ k.app (op n)) (mappingCone.inr_f_snd_v f q)
  simp only [NatTrans.comp_app, NatTrans.app_zero, NatTrans.id_app] at h₁ h₂
  simp only [coneTarget, h₁, h₂, comp_zero, zero_add]
  simpa only [Category.assoc, HomologicalComplex.asFunctor] using
    Category.comp_id (obj := A) (b ≫ π N' q n)

@[reassoc (attr := simp)]
private theorem productPair_source
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (q p : ℤ) (h : q + 1 = p) {T : A}
    (a : T ⟶ (roosP N).X p) (b : T ⟶ (roosP N').X q) :
    productPair f q p h a b ≫ productSource f q p h = a := by
  apply product_ext N p
  intro n
  simp only [Category.assoc, productSource_π, productPair, productLift_π_assoc,
    Preadditive.add_comp]
  have h₁ := congrArg (fun k ↦ k.app (op n)) (mappingCone.inl_v_fst_v f p q (by omega))
  have h₂ := congrArg (fun k ↦ k.app (op n)) (mappingCone.inr_f_fst_v f q p h)
  simp only [NatTrans.comp_app, NatTrans.app_zero, NatTrans.id_app] at h₁ h₂
  simp only [coneSource, h₁, h₂, comp_zero, add_zero]
  simpa only [Category.assoc, HomologicalComplex.asFunctor] using
    Category.comp_id (obj := A) (a ≫ π N p n)

attribute [local irreducible] productPair

private theorem productCone_ext
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (q p : ℤ) (h : q + 1 = p) {T : A}
    {a b : T ⟶ (roosP (mappingCone f)).X q}
    (ht : a ≫ productTarget f q = b ≫ productTarget f q)
    (hs : a ≫ productSource f q p h = b ≫ productSource f q p h) : a = b := by
  apply product_ext (mappingCone f) q
  intro n
  have ht' := congrArg (fun k ↦ k ≫ π N' q n) ht
  have hs' := congrArg (fun k ↦ k ≫ π N p n) hs
  simp only [Category.assoc, productTarget_π, productSource_π] at ht' hs'
  have he := congrArg (fun k ↦ k.app (op n)) (mappingCone.id_X f q p h)
  simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app] at he
  calc
    a ≫ π (mappingCone f) q n = (a ≫ π (mappingCone f) q n) ≫ 𝟙 _ := by simp
    _ = (a ≫ π (mappingCone f) q n) ≫
        (((mappingCone.fst f).1.v q p h).app (op n) ≫
          ((mappingCone.inl f).v p q (by omega)).app (op n) +
          (coneTarget f q).app (op n) ≫ ((mappingCone.inr f).f q).app (op n)) := by
      exact congrArg (fun x ↦ (a ≫ π (mappingCone f) q n) ≫ x) he.symm
    _ = (b ≫ π (mappingCone f) q n) ≫
        (((mappingCone.fst f).1.v q p h).app (op n) ≫
          ((mappingCone.inl f).v p q (by omega)).app (op n) +
          (coneTarget f q).app (op n) ≫ ((mappingCone.inr f).f q).app (op n)) := by
      simpa only [Preadditive.comp_add, Category.assoc, coneSource] using
        congrArg₂ (fun x y ↦ x ≫ ((mappingCone.inl f).v p q (by omega)).app (op n) +
          y ≫ ((mappingCone.inr f).f q).app (op n)) hs' ht'
    _ = b ≫ π (mappingCone f) q n := by
      exact (congrArg (fun x ↦ (b ≫ π (mappingCone f) q n) ≫ x) he).trans
        (Category.comp_id _)

private theorem roos_ext_at {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {T : A} (q p : ℤ) (hp : q - 1 = p) {f g : T ⟶ (roosF.obj N).X q}
    (hv : f ≫ v N q = g ≫ v N q)
    (hu : f ≫ ucoord N q p hp = g ≫ ucoord N q p hp) : f = g := by
  have hid := mappingCocone.id_X (roosU N) q p (by omega)
  change v N q ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
    ucoord N q p hp ≫
      (mappingCocone.inr (roosU N)).1.v p q (by omega) = 𝟙 _ at hid
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by rw [hid]
    _ = g ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hv, hu]
    _ = g := by rw [hid, Category.comp_id]

private theorem roos_ext {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {T : A} (q : ℤ) {f g : T ⟶ (roosF.obj N).X q}
    (hv : f ≫ v N q = g ≫ v N q)
    (hu : f ≫ ucoord N q (q - 1) rfl = g ≫ ucoord N q (q - 1) rfl) : f = g :=
  roos_ext_at q (q - 1) rfl hv hu

private theorem ucoord_χ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    ucoord N (p + 1) p (by omega) = (roosχ N p).hom ≫ biprod.fst := by
  have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
      HomologicalComplex.homotopyCofiber.sndX (roosU N) r =
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU N) r q hq).hom ≫
          biprod.snd := by
    obtain rfl := (ComplexShape.up ℤ).next_eq' hq
    dsimp only [HomologicalComplex.homotopyCofiber.sndX]
    rw [dite_eq_left hq]
  simp [ucoord, roosχ, mappingCocone.snd, HomComplex.Cochain.leftShift_v,
    show Int.negOnePow 2 = 1 by rfl, mappingCone.snd, hs p (p + 1) rfl]

@[reassoc]
private theorem map_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (hp : q - 1 = p) :
    (roosF.map f).f q ≫ ucoord N' q p hp =
      ucoord N q p hp ≫ (roosPmap f).f p := by
  obtain rfl : q = p + 1 := by omega
  simpa only [ucoord_χ, Category.assoc, biprod.map_fst] using
    congrArg (fun h ↦ h ≫ biprod.fst) (roosF_map_χ f p)

private theorem map_coordinates {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    ((roosF.map f).f q ≫ v N' q = v N q ≫ (roosPmap f).f q) ∧
    ((roosF.map f).f q ≫ ucoord N' q (q - 1) rfl =
      ucoord N q (q - 1) rfl ≫ (roosPmap f).f (q - 1)) := by
  refine ⟨?_, map_u f q (q - 1) rfl⟩
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hp
  subst q
  simpa only [v, roosProj_f, Category.assoc, biprod.map_snd] using
    congrArg (fun h ↦ h ≫ biprod.snd) (roosF_map_χ f p)

@[reassoc]
private theorem map_v {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    (roosF.map f).f q ≫ v N' q = v N q ≫ (roosPmap f).f q :=
  (map_coordinates f q).1

@[reassoc]
private theorem augment_u {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (j : Cone N.asFunctor) (q p : ℤ) (hp : q - 1 = p) :
    (augmentation j).f q ≫ ucoord N q p hp = 0 := by
  obtain rfl : q = p + 1 := by omega
  simpa only [augmentation, ucoord_χ, Category.assoc, biprod.lift_fst] using
    congrArg (fun h ↦ h ≫ biprod.fst) (roosAugment_χ (fun n ↦ j.π.app (op n))
      (fun n ↦ j.w (homOfLE (Nat.le_succ n)).op) p)

private theorem augment_coordinates {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (j : Cone N.asFunctor) (q : ℤ) :
    ((augmentation j).f q ≫ v N q = (Pi.lift (fun n ↦ j.π.app (op n))).f q) ∧
    ((augmentation j).f q ≫ ucoord N q (q - 1) rfl = 0) := by
  refine ⟨?_, augment_u j q (q - 1) rfl⟩
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hp
  subst q
  simpa only [augmentation, v, roosProj_f, Category.assoc, biprod.lift_snd] using
    congrArg (fun h ↦ h ≫ biprod.snd) (roosAugment_χ (fun n ↦ j.π.app (op n))
      (fun n ↦ j.w (homOfLE (Nat.le_succ n)).op) p)

private theorem differential_coordinates (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    ((roosF.obj N).d q (q + 1) ≫ v N (q + 1) =
      v N q ≫ (roosP N).d q (q + 1)) ∧
    ((roosF.obj N).d q (q + 1) ≫ ucoord N (q + 1) q (by omega) =
      -(ucoord N q (q - 1) rfl ≫ (roosP N).d (q - 1) q) -
        v N q ≫ (roosU N).f q) := by
  constructor
  · exact ((roosProj N).comm q (q + 1)).symm
  · have h := mappingCone.d_snd_v (roosU N) (q + -1) q (by omega)
    simp only [ucoord, v, roosProj, mappingCocone.snd,
      HomComplex.Cocycle.leftShift_coe, HomologicalComplex.neg_f_apply,
      HomComplex.Cocycle.homOf]
    rw [HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ q (by omega),
      HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ (q + -1) (by omega),
      HomComplex.Cochain.leftShift_v (n := 1) _ _ _ _ _ _ _ (q + -1) (by omega)]
    dsimp only [roosF, Functor.comp_obj, roosConeFunctor]
    simp only [show (-1 * -1 + -1 * (-1 - 1) / 2 : ℤ) = 2 by rfl,
      show (-1 * 0 + -1 * (-1 - 1) / 2 : ℤ) = 1 by rfl,
      show Int.negOnePow 2 = 1 by rfl, Int.negOnePow_one, Units.neg_smul,
      one_smul, neg_neg, shiftFunctor_obj_d', Int.negOnePow_neg,
      shiftFunctorObjXIso, Preadditive.neg_comp, Category.assoc,
      HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    rw [← (roosP N).XIsoOfEq_hom_comp_d (by omega : q - 1 = q + -1) q]
    simp only [← Category.assoc, HomComplex.Cochain.v_comp_XIsoOfEq_hom]
    rw [h]
    erw [Category.id_comp, Category.id_comp]
    simp only [neg_add_rev]
    abel

private noncomputable def coneHomComponent
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (q : ℤ) :
    (roosF.obj (mappingCone f)).X q ⟶ (mappingCone (roosF.map f)).X q :=
  conePair (roosF.map f) q (q + 1) rfl
    (fibrePair N (q + 1) q (by omega)
      (v (mappingCone f) q ≫ productSource f q (q + 1) rfl)
      (-(ucoord (mappingCone f) q (q - 1) rfl ≫
        productSource f (q - 1) q (by omega))))
    (fibrePair N' q (q - 1) rfl
      (v (mappingCone f) q ≫ productTarget f q)
      (ucoord (mappingCone f) q (q - 1) rfl ≫ productTarget f (q - 1)))

private noncomputable def coneInvComponent
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (q : ℤ) :
    (mappingCone (roosF.map f)).X q ⟶ (roosF.obj (mappingCone f)).X q :=
  fibrePair (mappingCone f) q (q - 1) rfl
    (productPair f q (q + 1) rfl
      (coneSource (roosF.map f) q (q + 1) rfl ≫ v N (q + 1))
      (coneTarget (roosF.map f) q ≫ v N' q))
    (productPair f (q - 1) q (by omega)
      (-(coneSource (roosF.map f) q (q + 1) rfl ≫ ucoord N (q + 1) q (by omega)))
      (coneTarget (roosF.map f) q ≫ ucoord N' q (q - 1) rfl))

@[reassoc (attr := simp)]
private theorem coneInv_v {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    coneInvComponent f q ≫ v (mappingCone f) q =
      productPair f q (q + 1) rfl
        (coneSource (roosF.map f) q (q + 1) rfl ≫ v N (q + 1))
        (coneTarget (roosF.map f) q ≫ v N' q) := by
  simp only [coneInvComponent, fibrePair_v]

@[reassoc (attr := simp)]
private theorem coneInv_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    coneInvComponent f q ≫ ucoord (mappingCone f) q (q - 1) rfl =
      productPair f (q - 1) q (by omega)
        (-(coneSource (roosF.map f) q (q + 1) rfl ≫ ucoord N (q + 1) q (by omega)))
        (coneTarget (roosF.map f) q ≫ ucoord N' q (q - 1) rfl) := by
  simp only [coneInvComponent, fibrePair_u]

attribute [local irreducible] coneInvComponent

@[reassoc (attr := simp)]
private theorem coneHom_t_v {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    coneHomComponent f q ≫ coneTarget (roosF.map f) q ≫ v N' q =
      v (mappingCone f) q ≫ productTarget f q := by
  simp [coneHomComponent]

@[reassoc (attr := simp)]
private theorem coneHom_t_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q p : ℤ) (hp : q - 1 = p) :
    coneHomComponent f q ≫ coneTarget (roosF.map f) q ≫ ucoord N' q p hp =
      ucoord (mappingCone f) q p hp ≫ productTarget f p := by
  subst p
  simp [coneHomComponent]

@[reassoc (attr := simp)]
private theorem coneHom_s_v {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q r : ℤ) (hr : q + 1 = r) :
    coneHomComponent f q ≫ coneSource (roosF.map f) q r hr ≫ v N r =
      v (mappingCone f) q ≫ productSource f q r hr := by
  subst r
  simp [coneHomComponent]

@[reassoc (attr := simp)]
private theorem coneHom_s_u {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q r : ℤ) (hr : q + 1 = r) :
    coneHomComponent f q ≫ coneSource (roosF.map f) q r hr ≫
        ucoord N r q (by omega) =
      -(ucoord (mappingCone f) q (q - 1) rfl ≫ productSource f (q - 1) q (by omega)) := by
  subst r
  simp [coneHomComponent]

@[reassoc]
private theorem differential_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (hp : q - 1 = p) :
    (roosF.obj N).d q (q + 1) ≫ ucoord N (q + 1) q (by omega) =
      -(ucoord N q p hp ≫ (roosP N).d p q) - v N q ≫ (roosU N).f q := by
  subst p
  exact (differential_coordinates N q).2

@[reassoc]
private theorem cone_d_target {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone f).d q (q + 1) ≫ coneTarget f (q + 1) =
      coneSource f q (q + 1) rfl ≫ f.f (q + 1) + coneTarget f q ≫ L.d q (q + 1) :=
  mappingCone.d_snd_v f q (q + 1) rfl

@[reassoc]
private theorem cone_d_source {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone f).d q (q + 1) ≫ coneSource f (q + 1) ((q + 1) + 1) rfl =
      -(coneSource f q (q + 1) rfl ≫ K.d (q + 1) ((q + 1) + 1)) :=
  mappingCone.d_fst_v f q (q + 1) ((q + 1) + 1) rfl rfl

@[reassoc]
private theorem differential_v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    (roosF.obj N).d q (q + 1) ≫ v N (q + 1) =
      v N q ≫ (roosP N).d q (q + 1) := (differential_coordinates N q).1

private theorem coneHom_s_u_at {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q r p : ℤ) (hr : q + 1 = r) (hp : q - 1 = p) :
    coneHomComponent f q ≫ coneSource (roosF.map f) q r hr ≫
        ucoord N r q (by omega) =
      -(ucoord (mappingCone f) q p hp ≫ productSource f p q (by omega)) := by
  subst p
  exact coneHom_s_u f q r hr

private theorem coneHom_comm {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) :
    coneHomComponent f q ≫ (mappingCone (roosF.map f)).d q (q + 1) =
      (roosF.obj (mappingCone f)).d q (q + 1) ≫ coneHomComponent f (q + 1) := by
  apply mappingCone.ext_to (roosF.map f) (q + 1) ((q + 1) + 1) rfl
  · apply roos_ext_at ((q + 1) + 1) (q + 1) (by omega)
    · simp only [Category.assoc, cone_d_source, Preadditive.neg_comp,
        Preadditive.comp_neg, coneHom_s_v_assoc, differential_v_assoc, differential_v,
        coneHom_s_v, productSource_d, Preadditive.comp_neg]
    · simp only [Category.assoc, cone_d_source, Preadditive.neg_comp,
        Preadditive.comp_neg, differential_u N (q + 1) q (by omega),
        Preadditive.comp_sub, Preadditive.sub_comp, coneHom_s_v_assoc,
        coneHom_s_u_assoc, coneHom_s_u_at f (q + 1) ((q + 1) + 1) q rfl (by omega),
        differential_u_assoc, productSource_u,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
      have hsd := productSource_d f (q - 1) q (q + 1) (by omega) rfl
      simp only [hsd, Preadditive.comp_neg, neg_neg]
  · apply roos_ext_at (q + 1) q (by omega)
    · simp only [Category.assoc, cone_d_target, Preadditive.add_comp,
        Preadditive.comp_add, coneHom_t_v, coneHom_s_v_assoc, coneHom_t_v_assoc,
        (map_coordinates _ _).1, differential_v_assoc, differential_v, productTarget_d]
    · simp only [Category.assoc, cone_d_target, Preadditive.add_comp,
        Preadditive.comp_add, coneHom_t_u f (q + 1) q (by omega),
        map_u, differential_u, Preadditive.comp_sub, Preadditive.sub_comp,
        Preadditive.comp_neg, Preadditive.neg_comp, coneHom_s_u_assoc,
        coneHom_t_u_assoc, coneHom_t_v_assoc, differential_u_assoc,
        productTarget_u]
      have htd : (roosP (mappingCone f)).d (q - 1) q ≫ productTarget f q =
          productSource f (q - 1) q (by omega) ≫ (roosPmap f).f q +
            productTarget f (q - 1) ≫ (roosP N').d (q - 1) q := by
        exact productTarget_d_at f (q - 1) q (by omega)
      simp only [htd, Preadditive.comp_add]
      abel

-- The four coordinate equations are the API for the signed permutation.
attribute [local irreducible] coneHomComponent

private noncomputable def coneComponentIso
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (q : ℤ) :
    (roosF.obj (mappingCone f)).X q ≅ (mappingCone (roosF.map f)).X q where
  hom := coneHomComponent f q
  inv := coneInvComponent f q
  hom_inv_id := by
    apply roos_ext q
    · apply productCone_ext f q (q + 1) rfl
      · simp [Category.assoc]
      · simp [Category.assoc]
    · apply productCone_ext f (q - 1) q (by omega)
      · simp [Category.assoc]
      · simp [Category.assoc]
  inv_hom_id := by
    apply mappingCone.ext_to (roosF.map f) q (q + 1) rfl
    · apply roos_ext_at (q + 1) q (by omega)
      · simp [Category.assoc]
      · simp [Category.assoc]
    · apply roos_ext q
      · simp [Category.assoc]
      · simp [Category.assoc]

private noncomputable def coneIso
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') :
    roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f) :=
  HomologicalComplex.Hom.isoOfComponents (coneComponentIso f) (by
    intro q p hp
    obtain rfl : p = q + 1 := hp.symm
    exact coneHom_comm f q)

@[simp]
private theorem coneIso_hom_f {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (q : ℤ) : (coneIso f).hom.f q = coneHomComponent f q := rfl

-- Avoid unfolding the inverse and its proofs when using the chain isomorphism.
attribute [local irreducible] coneComponentIso coneIso

private theorem coneIso_formula
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') :
    ConeFormula f (coneIso f) := by
  intro q n
  simp only [Category.assoc, coneIso_hom_f, coneHom_t_v_assoc, coneHom_t_u_assoc,
    coneHom_s_v_assoc, coneHom_s_u_assoc, productTarget_π, productSource_π,
    Preadditive.neg_comp, and_self]

@[reassoc (attr := simp)]
private theorem coneMap_target {B : Type a} [Category.{b} B] [Abelian B]
    {K L K' L' : CochainComplex B ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) (q : ℤ) :
    (mappingCone.map f g a b h).f q ≫ coneTarget g q =
      coneTarget f q ≫ b.f q := by
  apply mappingCone.ext_from f (q + 1) q rfl
  · simp [mappingCone.map, coneTarget, Category.assoc,
      HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, coneTarget, Category.assoc]

@[reassoc (attr := simp)]
private theorem coneMap_source {B : Type a} [Category.{b} B] [Abelian B]
    {K L K' L' : CochainComplex B ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g)
    (q p : ℤ) (hp : q + 1 = p) :
    (mappingCone.map f g a b h).f q ≫ coneSource g q p hp =
      coneSource f q p hp ≫ a.f p := by
  apply mappingCone.ext_from f p q hp
  · simp [mappingCone.map, coneSource, Category.assoc,
      HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, coneSource, Category.assoc]

private theorem productTarget_natural
    {N N' M M' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (g : M ⟶ M') (a : N ⟶ M) (b : N' ⟶ M')
    (h : f ≫ b = a ≫ g) (q : ℤ) :
    (roosPmap (mappingCone.map f g a b h)).f q ≫ productTarget g q =
      productTarget f q ≫ (roosPmap b).f q := by
  apply product_ext M' q
  intro n
  have hh := congrArg (fun k ↦ k.app (op n)) (coneMap_target f g a b h q)
  simp only [NatTrans.comp_app] at hh
  simpa only [Category.assoc, productTarget_π, π_map, productTarget_π_assoc,
    π_map_assoc] using congrArg (fun k ↦ π (mappingCone f) q n ≫ k) hh

private theorem productSource_natural
    {N N' M M' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (g : M ⟶ M') (a : N ⟶ M) (b : N' ⟶ M')
    (h : f ≫ b = a ≫ g) (q p : ℤ) (hp : q + 1 = p) :
    (roosPmap (mappingCone.map f g a b h)).f q ≫ productSource g q p hp =
      productSource f q p hp ≫ (roosPmap a).f p := by
  apply product_ext M p
  intro n
  have hh := congrArg (fun k ↦ k.app (op n)) (coneMap_source f g a b h q p hp)
  simp only [NatTrans.comp_app] at hh
  simpa only [Category.assoc, productSource_π, π_map, productSource_π_assoc,
    π_map_assoc] using congrArg (fun k ↦ π (mappingCone f) q n ≫ k) hh

private theorem coneIso_natural
    {N N' M M' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (g : M ⟶ M') (a : N ⟶ M) (b : N' ⟶ M')
    (h : f ≫ b = a ≫ g) :
    roosF.map (mappingCone.map f g a b h) ≫ (coneIso g).hom =
      (coneIso f).hom ≫ mappingCone.map (roosF.map f) (roosF.map g)
        (roosF.map a) (roosF.map b)
        (by rw [← Functor.map_comp, ← Functor.map_comp, h]) := by
  ext q : 1
  simp only [HomologicalComplex.comp_f, coneIso_hom_f]
  change (roosF.map (mappingCone.map f g a b h)).f q ≫ coneHomComponent g q =
    coneHomComponent f q ≫ _
  apply mappingCone.ext_to (roosF.map g) q (q + 1) rfl
  · apply roos_ext_at (q + 1) q (by omega)
    · simp only [Category.assoc, coneHom_s_v, coneMap_source_assoc,
        (map_coordinates _ _).1, coneHom_s_v_assoc]
      rw [← Category.assoc, (map_coordinates _ _).1, Category.assoc,
        productSource_natural]
    · simp only [Category.assoc, coneHom_s_u, coneMap_source_assoc,
        map_u, coneHom_s_u_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
      rw [← Category.assoc, map_u, Category.assoc, productSource_natural]
  · apply roos_ext q
    · simp only [Category.assoc, coneHom_t_v, coneMap_target_assoc,
        (map_coordinates _ _).1, coneHom_t_v_assoc]
      rw [← Category.assoc, (map_coordinates _ _).1, Category.assoc,
        productTarget_natural]
    · simp only [Category.assoc, coneHom_t_u, coneMap_target_assoc,
        map_u, coneHom_t_u_assoc]
      rw [← Category.assoc, map_u, Category.assoc, productTarget_natural]

private noncomputable abbrev levelFunctor (n : ℕ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj N := N.asFunctor.obj (op n)
  map f := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  map_id N := by ext q; rfl
  map_comp f g := by ext q; rfl

@[instance_reducible]
private noncomputable def levelCommShift (n : ℕ) :
    (levelFunctor (A := A) n).CommShift ℤ := by
  change (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).CommShift ℤ
  infer_instance

attribute [local instance] levelCommShift

omit [HasCountableProducts A] in
private theorem levelShift_f (n : ℕ) (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) :
    ((Functor.commShiftIso (levelFunctor (A := A) n)
      (self := levelCommShift n) r).hom.app N).f q =
      𝟙 ((N.X (q + r)).obj (op n)) := by
  rfl

private noncomputable abbrev productFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  ProductShift.productFunctor (levelFunctor (A := A))

@[instance_reducible]
private noncomputable def productShift : (productFunctor (A := A)).CommShift ℤ :=
  ProductShift.productCommShift (levelFunctor (A := A))

attribute [local instance] productShift

private noncomputable def productShiftComponent
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosP (N⟦r⟧)).X q ⟶ (roosP N).X (q + r) :=
  (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q

private theorem productShiftComponent_eq
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    productShiftComponent N r q =
      (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q := rfl

private theorem productShift_π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) (n : ℕ) :
    productShiftComponent N r q ≫
        π N (q + r) n =
      π (N⟦r⟧) q n ≫
        ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n) := by
  have h := congrArg (fun k ↦ k.f q)
    (ProductShift.productShiftIso_π (levelFunctor (A := A)) N r n)
  simp only [HomologicalComplex.comp_f, levelShift_f] at h
  erw [Category.comp_id] at h
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [productShiftComponent, π, shiftFunctor_map_f'] using h

attribute [local irreducible] productShiftComponent

private noncomputable def productShiftComponentAt
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q p : ℤ) (h : q + r = p) :
    (roosP (N⟦r⟧)).X q ⟶ (roosP N).X p :=
  productShiftComponent N r q ≫ ((roosP N).XIsoOfEq h).hom

private theorem productShiftAt_π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q p : ℤ) (h : q + r = p) (n : ℕ) :
    productShiftComponentAt N r q p h ≫ π N p n =
      π (N⟦r⟧) q n ≫ ((shiftFunctorObjXIso N r q p h.symm).hom).app (op n) := by
  subst p
  simpa only [productShiftComponentAt, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using productShift_π N r q n

attribute [local irreducible] productShiftComponentAt

private noncomputable def transitionEndomorphism : productFunctor (A := A) ⟶ productFunctor where
  app := roosU
  naturality _ _ f := (roosU_natural f).symm

private theorem transitionEndomorphism_shift :
    NatTrans.CommShift (transitionEndomorphism (A := A)) ℤ := by
  constructor
  intro r
  apply NatTrans.ext
  funext N
  change (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom ≫
      (roosU N)⟦r⟧' =
    roosU (N⟦r⟧) ≫ (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom
  apply ProductShift.productShift_hom_ext (levelFunctor (A := A)) N r
  intro n
  rw [Category.assoc, ← Functor.map_comp]
  have hu (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
      roosU M ≫ Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n =
        Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n -
          Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) (n + 1) ≫
            M.asFunctor.map (homOfLE (Nat.le_succ n)).op :=
    (towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ M.asFunctor.obj (op n))
      (fun n : ℕ ↦ M.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
  erw [hu]
  rw [Category.assoc, ProductShift.productShiftIso_π]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub]
  erw [ProductShift.productShiftIso_π, ProductShift.productShiftIso_π_assoc]
  conv_rhs => erw [← Category.assoc, hu]
  simp only [Preadditive.sub_comp, Category.assoc]
  congr 1
  ext q
  simp [HomologicalComplex.comp_f, shiftFunctor_map_f', levelShift_f, levelFunctor]

attribute [local instance] transitionEndomorphism_shift

private noncomputable abbrev signedFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  SignedCoconeShift.coconeFunctor productFunctor productFunctor transitionEndomorphism

@[instance_reducible]
private noncomputable def signedCommShift : (signedFunctor (A := A)).CommShift ℤ :=
  SignedCoconeShift.coconeCommShift _ _ _

omit [HasCountableProducts A] in
private theorem cofiberMap_eq_coneMap
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    mappingCone.map, mappingCone.desc, mappingCone.descCochain,
    HomComplex.Cochain.comp_v, mappingCone.inl, mappingCone.fst, mappingCone.snd,
    mappingCone.inr]

private noncomputable def signedRoosIso : signedFunctor (A := A) ≅ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro N N' f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (cofiberMap_eq_coneMap (roosU N) (roosU N')
        (roosPmap f) (roosPmap f) (roosU_natural f)))

@[instance_reducible]
private noncomputable def roosCommShift : (roosF (A := A)).CommShift ℤ := by
  letI := signedCommShift (A := A)
  exact Functor.CommShift.ofIso signedRoosIso ℤ

private noncomputable def roosShiftMap (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosF.obj (N⟦r⟧) ⟶ (roosF.obj N)⟦r⟧ :=
  (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N

private theorem roosShiftMap_eq (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N := rfl

attribute [local irreducible] roosShiftMap

private theorem roosShift_hom (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (SignedCoconeShift.coconeFunctorShiftIso productFunctor productFunctor
        transitionEndomorphism N r).hom := by
  rw [roosShiftMap_eq]
  let := signedCommShift (A := A)
  change ((Functor.CommShift.ofIso signedRoosIso ℤ).commShiftIso r).hom.app N = _
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app, signedRoosIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom,
    Iso.refl_inv, Functor.map_id, Category.comp_id]
  erw [Category.id_comp]
  rfl

attribute [local irreducible] roosCommShift

@[reassoc]
private theorem roosShift_inl (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (mappingCocone.inl (roosU (N⟦r⟧))).v q q (add_zero q) ≫
        (roosShiftMap N r).f q =
      productShiftComponent N r q ≫
        (mappingCocone.inl (roosU N)).v (q + r) (q + r) (add_zero _) ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inl
    productFunctor productFunctor transitionEndomorphism N r q

@[reassoc]
private theorem roosShift_inr (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r p q : ℤ) (h : p + 1 = q) :
    (mappingCocone.inr (roosU (N⟦r⟧))).1.v p q h ≫
        (roosShiftMap N r).f q =
      r.negOnePow •
        (productShiftComponent N r p ≫
          (mappingCocone.inr (roosU N)).1.v (p + r) (q + r) (by omega) ≫
          (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv) := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inr
    productFunctor productFunctor transitionEndomorphism N r p q h

private theorem v_eq_fst (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    v N q = (mappingCocone.fst (roosU N)).f q := rfl

@[reassoc]
private theorem roosShift_v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫ v N (q + r) =
      v (N⟦r⟧) q ≫
        productShiftComponent N r q := by
  simp only [v_eq_fst]
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_fst_f, mappingCocone.inl_v_fst_f_assoc,
      Category.comp_id]
  · rw [roosShift_inr_assoc]
    simp only [Category.assoc, Linear.units_smul_comp,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_fst_f, mappingCocone.inr_v_fst_f_assoc,
      comp_zero, zero_comp, smul_zero]

@[reassoc]
private theorem roosShift_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) ((q - 1) + r) (by omega) =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫
        productShiftComponent N r (q - 1)) := by
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [ucoord, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_snd_v, mappingCocone.inl_v_snd_v_assoc,
      comp_zero, zero_comp, smul_zero]
  · rw [roosShift_inr_assoc]
    simp only [ucoord, Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_snd_v, mappingCocone.inr_v_snd_v_assoc,
      Category.comp_id]

private theorem roosShift_u_at (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q p : ℤ) (h : (q - 1) + r = p) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) p (by omega) =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫
        productShiftComponentAt N r (q - 1) p h) := by
  subst p
  simpa only [productShiftComponentAt, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using roosShift_u N r q

private theorem shift_formula : ShiftFormula (roosCommShift (A := A)) := by
  intro N r q n
  simp only [← roosShiftMap_eq]
  constructor
  · rw [roosShift_v_assoc, productShift_π]
  · rw [roosShift_u_assoc]
    simp only [Linear.units_smul_comp, Category.assoc, productShift_π]

private theorem roos_additive : (roosF (A := A)).Additive := by
  constructor
  intro N N' f g
  have hp : roosPmap (f + g) = roosPmap f + roosPmap g := by
    apply Pi.hom_ext
    intro n
    ext q
    simp [roosPmap, HomologicalComplex.add_f_apply, Preadditive.add_comp,
      Preadditive.comp_add]
  ext q : 1
  apply roos_ext q
  · simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp,
      (map_coordinates _ _).1, hp, HomologicalComplex.add_f_apply, Preadditive.comp_add]
  · simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp,
      (map_coordinates _ _).2, hp, HomologicalComplex.add_f_apply, Preadditive.comp_add]

private theorem augmentation_natural : AugmentationNaturality A := by
  intro N N' f j j' g h
  have hp : Pi.lift (fun n ↦ j.π.app (op n)) ≫ roosPmap f =
      g ≫ Pi.lift (fun n ↦ j'.π.app (op n)) := by
    apply Pi.hom_ext
    intro n
    simpa [roosPmap, Category.assoc] using h n
  ext q : 1
  apply roos_ext q
  · simp only [HomologicalComplex.comp_f, Category.assoc, (map_coordinates _ _).1]
    rw [← Category.assoc, (augment_coordinates _ _).1]
    simpa only [HomologicalComplex.comp_f, (augment_coordinates _ _).1] using
      congrArg (fun f ↦ f.f q) hp
  · simp only [HomologicalComplex.comp_f, Category.assoc, (map_coordinates _ _).2]
    rw [← Category.assoc, (augment_coordinates _ _).2]
    simp only [zero_comp, (augment_coordinates _ _).2, comp_zero]

@[reassoc (attr := simp)]
private theorem augment_v_π {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (j : Cone N.asFunctor) (q : ℤ) (n : ℕ) :
    (augmentation j).f q ≫ v N q ≫ π N q n = (j.π.app (op n)).f q := by
  rw [← Category.assoc, (augment_coordinates j q).1]
  exact congrArg (fun k ↦ k.f q) (Pi.lift_comp_π (fun n ↦ j.π.app (op n)) n)

private theorem shift_augmentation : ShiftAugmentation (roosCommShift (A := A)) := by
  intro N j r js c h
  rw [← roosShiftMap_eq]
  ext q : 1
  apply roos_ext_at (q + r) ((q - 1) + r) (by omega)
  · apply product_ext N (q + r)
    intro n
    have hv := roosShift_v N r q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hv
    erw [Category.id_comp] at hv
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [reassoc_of% hv, productShift_π]
    have hh := h q n
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, NatTrans.id_app] at hh
    erw [Category.id_comp] at hh
    simpa only [Category.assoc, augment_v_π, augment_v_π_assoc,
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id,
      Category.id_comp] using hh
  · have hu := roosShift_u N r q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hu
    erw [Category.id_comp] at hu
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [hu]
    simp only [Linear.comp_units_smul, augment_u_assoc, smul_zero,
      augment_u, comp_zero, zero_comp]

private theorem cone_augmentation :
    ConeAugmentation (fun f ↦ coneIso f) (augmentation_natural (A := A)) := by
  intro N N' f j j' g h jc c hc
  ext q : 1
  simp only [HomologicalComplex.comp_f, coneIso_hom_f]
  change c.f q ≫ (augmentation jc).f q ≫ coneHomComponent f q = _
  apply mappingCone.ext_to (roosF.map f) q (q + 1) rfl
  · apply roos_ext_at (q + 1) q (by omega)
    · apply product_ext N (q + 1)
      intro n
      have hh := (hc q n).2
      simpa only [HomologicalComplex.comp_f, Category.assoc,
        coneHom_s_v, productSource_π, coneMap_source_assoc,
        augment_v_π, augment_v_π_assoc] using hh
    · simp only [Category.assoc,
        coneHom_s_u, coneMap_source_assoc, augment_u,
        Preadditive.comp_neg, Category.assoc,
        augment_u_assoc, comp_zero, zero_comp, neg_zero]
  · apply roos_ext q
    · apply product_ext N' q
      intro n
      have hh := (hc q n).1
      simpa only [HomologicalComplex.comp_f, Category.assoc,
        coneHom_t_v, productTarget_π, coneMap_target_assoc,
        augment_v_π, augment_v_π_assoc] using hh
    · simp only [Category.assoc,
        coneHom_t_u, coneMap_target_assoc, Category.assoc,
        augment_u_assoc, augment_u, comp_zero, zero_comp]

private theorem cone_inclusion {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') :
    roosF.map (mappingCone.inr f) ≫ (coneIso f).hom =
      mappingCone.inr (roosF.map f) := by
  ext q : 1
  simp only [HomologicalComplex.comp_f, coneIso_hom_f]
  apply mappingCone.ext_to (roosF.map f) q (q + 1) rfl
  · apply roos_ext_at (q + 1) q (by omega)
    · apply product_ext N (q + 1)
      intro n
      simp only [Category.assoc, coneHom_s_v, productSource_π,
        map_v_assoc, π_map_assoc]
      simp [coneSource, ← NatTrans.comp_app]
    · apply product_ext N q
      intro n
      simp only [Category.assoc, coneHom_s_u, Preadditive.comp_neg,
        Preadditive.neg_comp, productSource_π, map_u_assoc, π_map_assoc]
      simp [coneSource, ← NatTrans.comp_app]
  · apply roos_ext q
    · apply product_ext N' q
      intro n
      simp only [Category.assoc, coneHom_t_v, productTarget_π,
        map_v_assoc, π_map_assoc]
      simp [coneTarget, ← NatTrans.comp_app]
    · apply product_ext N' (q - 1)
      intro n
      simp only [Category.assoc, coneHom_t_u, productTarget_π, map_u_assoc, π_map_assoc]
      simp [coneTarget, ← NatTrans.comp_app]

private theorem cone_boundary_component {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ) :
    (mappingCone.triangle f).mor₃.f q = -coneSource f q (q + 1) rfl := by
  apply mappingCone.ext_from f (q + 1) q rfl
  · simp [coneSource, shiftFunctorObjXIso]
  · simp [coneSource]

@[reassoc]
private theorem roosShift_one_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    (roosShiftMap N (1 : ℤ)).f q ≫
        ucoord N (q + 1) q (by omega) =
      -(ucoord (N⟦(1 : ℤ)⟧) q (q - 1) rfl ≫
        productShiftComponentAt N 1 (q - 1) q (by omega)) := by
  have h := roosShift_u_at N 1 q q (by omega)
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Int.negOnePow_one, Units.neg_smul, one_smul] at h
  erw [Category.id_comp] at h
  exact h

private theorem cone_boundary {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') :
    roosF.map (mappingCone.triangle f).mor₃ ≫
        roosShiftMap N (1 : ℤ) =
      (coneIso f).hom ≫ (mappingCone.triangle (roosF.map f)).mor₃ := by
  ext q : 1
  simp only [HomologicalComplex.comp_f, coneIso_hom_f]
  apply roos_ext_at (q + 1) q (by omega)
  · apply product_ext N (q + 1)
    intro n
    simp only [Category.assoc]
    have hv := roosShift_v N 1 q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hv
    erw [Category.id_comp] at hv
    erw [reassoc_of% hv]
    simp only [productShift_π,
      cone_boundary_component,
      Preadditive.comp_neg, Preadditive.neg_comp, coneHom_s_v_assoc,
      productSource_π]
    erw [map_v_assoc, π_map_assoc]
    simp only [cone_boundary_component, NatTrans.app_neg,
      Preadditive.comp_neg, Preadditive.neg_comp, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id]
    simp only [mappingCone.triangle_obj₃]
  · apply product_ext N q
    intro n
    simp only [Category.assoc]
    rw [roosShift_one_u_assoc]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp,
      productShiftAt_π, cone_boundary_component,
      neg_neg, coneHom_s_u_assoc, productSource_π]
    erw [map_u_assoc, π_map_assoc]
    simp only [cone_boundary_component, NatTrans.app_neg, Preadditive.comp_neg,
      Preadditive.neg_comp, neg_neg, ← NatTrans.comp_app,
      coneSource, shiftFunctorObjXIso, HomComplex.Cochain.v_comp_XIsoOfEq_hom]
    simp only [mappingCone.triangle_obj₃]

private theorem cone_compatibility :
    ConeCompatibility (roosCommShift (A := A)) (fun f ↦ coneIso f) := by
  refine ⟨?_, ?_⟩
  · intro N N' M M' f g a b h
    exact coneIso_natural f g a b h
  · intro N N' f
    refine ⟨cone_inclusion f, ?_⟩
    simpa only [roosShiftMap_eq] using cone_boundary f

private theorem derived_roos [HasDerivedCategory.{w} A]
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hp : Nonempty (IsLimit (DerivedCategory.Q.mapCone
      (limit.cone (Discrete.functor (fun n : ℕ ↦ N.asFunctor.obj (op n))))))) :
    DerivedRoos N := by
  classical
  refine ⟨hp, DerivedCategory.mappingCocone_triangle_distinguished _, ?_⟩
  intro hproduct
  let Q := DerivedCategory.Q.{w} (C := A)
  let K := fun n : ℕ ↦ N.asFunctor.obj (op n)
  let KD := fun n : ℕ ↦ Q.obj (K n)
  let P : Fan K := limit.cone (Discrete.functor K)
  let hfan := (Fan.isLimitMapConeEquiv Q K P) hp.some
  let e : Q.obj P.pt ≅ ∏ᶜ KD := hfan.conePointUniqueUpToIso (productIsProduct KD)
  have he (n : ℕ) : e.hom ≫ Pi.π KD n = Q.map (Pi.π K n) :=
    hfan.conePointUniqueUpToIso_hom_comp (productIsProduct KD) ⟨n⟩
  let sd := towerTransitionEndomorphism (K := KD)
    (fun n : ℕ ↦ Q.map (N.asFunctor.map (homOfLE (Nat.le_succ n)).op))
  have hs : Q.map (roosU N) ≫ e.hom = e.hom ≫ sd := by
    apply Pi.hom_ext
    intro n
    have hsπ (n : ℕ) : roosU N ≫ Pi.π K n = Pi.π K n -
        Pi.π K (n + 1) ≫ N.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
      exact (towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ N.asFunctor.obj (op n))
        (fun n : ℕ ↦ N.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
    simp only [Category.assoc, he, ← Functor.map_comp, hsπ, Functor.map_sub]
    simp only [sd, towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, he]
    rw [Functor.map_comp, ← Category.assoc, he]
  let T := Q.mapTriangle.obj (mappingCocone.triangle (roosU N))
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished _
  refine ⟨T.mor₁ ≫ e.hom, e.inv ≫ T.mor₃, ?_⟩
  exact (distinguished_iff_of_iso
    (Triangle.isoMk T
      (Triangle.mk (T.mor₁ ≫ e.hom) sd (e.inv ≫ T.mor₃))
      (Iso.refl _) e e (by simp) hs (by simp))).mp hT

private theorem product_quasiIso [HasExactLimitsOfShape (Discrete ℕ) A]
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (hf : ∀ n : ℕ, QuasiIso
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) :
    QuasiIso (roosPmap f) := by
  have (n : ℕ) : QuasiIso
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) := hf n
  constructor
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q
  let a := fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  let K := fun n : ℕ ↦ N.asFunctor.obj (op n)
  let K' := fun n : ℕ ↦ N'.asFunctor.obj (op n)
  have (n : ℕ) : IsIso (H.map (a n)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (a n) q).mp inferInstance
  have : IsIso (piComparison H K) := inferInstance
  have : IsIso (piComparison H K') := inferInstance
  have hc : H.map (roosPmap f) ≫ piComparison H K' =
      piComparison H K ≫ Limits.Pi.map (fun n ↦ H.map (a n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π,
      Limits.Pi.map_π, ← Functor.map_comp, roosPmap, K, K', a]
    erw [Limits.Pi.map_π, piComparison_comp_π_assoc, Functor.map_comp]
  have he : H.map (roosPmap f) =
      piComparison H K ≫ Limits.Pi.map (fun n ↦ H.map (a n)) ≫ inv (piComparison H K') := by
    apply (cancel_mono (piComparison H K')).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hc
  change IsIso (H.map (roosPmap f))
  rw [he]
  infer_instance

private theorem roos_quasiIso [HasDerivedCategory.{w} A]
    {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (hp : QuasiIso (roosPmap f)) : QuasiIso (roosF.map f) := by
  let τ := mappingCone.triangleMap (roosU N) (roosU N')
    (roosPmap f) (roosPmap f) (roosU_natural f)
  have hc : IsIso (DerivedCategory.Q.map (roosConeFunctor.map f)) :=
    isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished (roosU N))
      (DerivedCategory.mappingCone_triangle_distinguished (roosU N'))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
  have : QuasiIso (roosConeFunctor.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  change QuasiIso ((roosConeFunctor.map f)⟦(-1 : ℤ)⟧')
  infer_instance

private theorem assemble_calculus [HasDerivedCategory.{w} A] [CountableAB4Star A] :
    (roosF (A := A)).Additive ∧
    CoordinateCalculus A ∧
    (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
      (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) →
      QuasiIso (roosF.map f)) ∧
    (∀ N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedRoos N) ∧
    ∃ (cs : (roosF (A := A)).CommShift ℤ)
      (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
        (f : N ⟶ N'), roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
      (hnat : AugmentationNaturality A),
      ShiftFormula cs ∧
      (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
        (f : N ⟶ N'), ConeFormula f (e f)) ∧
      ConeCompatibility cs e ∧ ConeAugmentation e hnat ∧ ShiftAugmentation cs := by
  refine ⟨roos_additive, ⟨differential_coordinates, map_coordinates,
    augment_coordinates⟩, ?_, ?_, ?_⟩
  · intro N N' f hf
    apply roos_quasiIso f
    exact product_quasiIso f hf
  · intro N
    exact derived_roos N (derivedCategory_termwiseProduct_isLimit
      A ℕ (fun n ↦ N.asFunctor.obj (op n)))
  · refine ⟨roosCommShift, fun f ↦ coneIso f, augmentation_natural,
      ?_, fun f ↦ coneIso_formula f, ?_, ?_, ?_⟩
    · exact shift_formula
    · exact cone_compatibility
    · exact cone_augmentation
    · exact shift_augmentation

end Coordinates

-- Preserve the abstract functor while elaborating its sheaf-module specialization.
attribute [local irreducible] roosF roosConeFunctor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The strict Roos fibre is additive, preserves levelwise quasi-isomorphisms, computes
Roos derived limits, and has the specified natural cone and coherent shift comparisons,
including compatibility with the actual zero-second-coordinate augmentations.

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-lem-pe-derived-nakayama-first-reduction, Cones paragraph; Stacks 08TC, 07KC,
014E and 011G (blueprint: lem-pe-roos-cone-calculus).

Proof plan:
1. Use the product universal property (def-weil-category-product) to define the transition
   shift and verify it commutes with d and strict product maps (def-weil-inverse-system).
   The existing roosF of def-weil-strict-roos-model is Cone(1-T)[-1]; expanding its
   coordinates gives (dv,-du-(1-T)v). Projectionwise verification gives additivity,
   the diagonal map formula and naturality of the zero-second-coordinate augmentation.
2. By proposition-exact-products--2, the product of levelwise quasi-isomorphisms is a
   quasi-isomorphism. Apply lem-pe-roos-coordinates-quasi-iso with endomorphism -(1-T)
   to get the same result for the diagonal Roos map; no boundedness is required.
3. The actual localized product cone is limiting by proposition-exact-products--2. Thus Q(1-T)
   is the derived transition endomorphism. Inverse rotation of the cone triangle using
   def-weil-triangulated-category gives the localized mapping-cocone triangle, with
   projection v and last map w↦(0,w). This is def-weil-derived-limit's Roos triangle;
   transport along the unique projection-preserving product isomorphism.
4. For epsilon=(-1)^r the shift comparison (v,u)↦(v,epsilon u) commutes with d, is
   natural, and is involutive in these coordinates. The identities epsilon(0)=1 and
   epsilon(r+s)=epsilon(r)epsilon(s) give coherent shifts. This is the existing signed
   comparison of lem-weil-roos-comm-shift transported to the strict-tower presentation.
5. Expand both double cones: the source differential on (b,a,b',a') is
   (db+Fa,-da,-db'-Fa'-(1-T')b,da'-(1-T)a). The permutation with sign
   (b,a,b',a')↦(b,b',a,-a') intertwines it with the target differential, and has
   inverse (b,b',a,c)↦(b,a,b',-c). The four projection equations uniquely specify it.
6. Every strict square acts by the four diagonal product maps, which commute with
   this permutation and sign. The inclusion sends (b,b') to (b,0,b',0).
   The boundary -p followed by the shift comparison is (-a,a'), also -p after
   the cone comparison. These establish naturality, inclusion and boundary identities.
7. For a compatible family j, (1-T)J=0 after every product projection. Therefore
   (J,0) is the existing chain map roosAugment; diagonal product maps give naturality.
8. Shifts multiply its zero coordinate by a sign and preserve it. The induced cone
   augmentation ((J'm',Jm),(0,0)) goes to ((J'm',0),(Jm,0)), the cone map of the
   two augmentations. Checking the two levelwise coordinates proves the stated
   conditional compatibility for every induced cone and shifted augmentation. -/
theorem roos_cone_calculus
    (X : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)] :
    (roosF (A := ringedSiteModules.{max u (t + 1)} R)).Additive ∧
    CoordinateCalculus (ringedSiteModules.{max u (t + 1)} R) ∧
    (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
      (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) →
      QuasiIso (roosF.map f)) ∧
    (∀ N : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ,
      DerivedRoos N) ∧
    ∃ (cs : (roosF (A := ringedSiteModules.{max u (t + 1)} R)).CommShift ℤ)
      (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
      (hnat : AugmentationNaturality (ringedSiteModules.{max u (t + 1)} R)),
      ShiftFormula cs ∧
      (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), ConeFormula f (e f)) ∧
      ConeCompatibility cs e ∧ ConeAugmentation e hnat ∧ ShiftAugmentation cs := by
  let : CountableAB4Star (ringedSiteModules.{max u (t + 1)} R) :=
    ⟨fun I _ ↦ AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} X R I⟩
  exact @assemble_calculus (ringedSiteModules.{max u (t + 1)} R) _ _ _
    (inferInstance : HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R))
    inferInstance

end CategoryTheory.RoosConeCalculus
