/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-!
# AffineTraceRightNormalForm
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

/-- The specified shiftedComp construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def shiftedComp {C : Type*} [Category C] [HasShift C ℤ]
    (F G H : C ⥤ C) [G.CommShift ℤ] (e : F ⋙ G ≅ H) (a b : ℤ) :
    (F ⋙ shiftFunctor _ a) ⋙ (G ⋙ shiftFunctor _ b) ≅
      H ⋙ shiftFunctor _ (a + b) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.commShiftIso a) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e _ ≪≫
    Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a b).symm

/-- The specified tensorShiftCompGeneral construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def tensorShiftCompGeneral
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M : DerivedCategory (Sheaf X.smallEtaleTopology B)) (a b : ℤ) :
    (derivedTensorRight B X L ⋙ shiftFunctor _ a) ⋙
        (derivedTensorRight B X M ⋙ shiftFunctor _ b) ≅
      derivedTensorRight B X (((derivedTensor B X).obj L).obj M) ⋙ shiftFunctor _ (a + b) :=
  shiftedComp _ _ _ (tensorRightTensor L M).symm a b

/-- The specified singleProductGeneral construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def singleProductGeneral
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M R : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (e : L ⊗ M ≅ R) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj R :=
  singleFunctorObjTensorIso L M hL ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e

@[irreducible]
private def singleLeftUnitGeneral
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology B).obj (𝟙_ B)))).obj L ≅ L :=
  ((derivedTensor B X).mapIso (singleFunctorObjUnitIso B X)).app L ≪≫
    derivedTensorLeftUnitor B X L

/-- The specified lineShiftGeneral construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def lineShiftGeneral
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U P S : Scheme.{u}} (j : U ⟶ P) (q : P ⟶ S) (p : U ⟶ S)
    (w : j ≫ q = p) [(upperStar B j).PreservesFlat]
    (L : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf U.smallEtaleTopology B))
    (e : (upperStar B j).leftDerivedFunctor.obj L ≅ M⟦(2 : ℤ)⟧) :
    ((upperStar B q).leftDerivedFunctor ⋙ derivedTensorRight B P L) ⋙
        (upperStar B j).leftDerivedFunctor ≅
      (upperStar B p).leftDerivedFunctor ⋙ derivedTensorRight B U M ⋙
        shiftFunctor _ (2 : ℤ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (derivedTensorRightCompLeftDerivedUpperStarIso B j L ≪≫
        Functor.isoWhiskerLeft _
          ((derivedTensorRightFunctor B U).mapIso e ≪≫ derivedTensorRightShiftIso B M 2)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp B j q p w.symm).symm _

section General
variable (B : Type*) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (N : ℕ) (E : ∀ X : Scheme.{u}, ℕ → Sheaf X.smallEtaleTopology B)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (upperStar B f).PreservesFlat]

/-- The specified singleE construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
abbrev singleE (X : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj (E X d)

/-- The specified lineR construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
abbrev lineR (X : Scheme.{u}) :=
  ((upperStar B (ProjectiveLine X ↘ X)).leftDerivedFunctor ⋙
    derivedTensorRight B (ProjectiveLine X) ((singleE B E (ProjectiveLine X) 1)⟦(2 : ℤ)⟧)) ⋙
      (upperStar B (ProjectiveLine.affineChart X)).leftDerivedFunctor

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) → ∀ d : ℕ,
  (upperStar B f).obj (E Y d) ≅ E X d)

/-- The specified singleEPullback construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def singleEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (upperStar B f).leftDerivedFunctor.obj (singleE B E Y d) ≅ singleE B E X d :=
  (singleFunctorCompLeftDerivedUpperStarIso B f).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (c f hY d)

/-- The specified tensorEPullback construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def tensorEPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) (a : ℤ) :
    (derivedTensorRight B Y (singleE B E Y d) ⋙ shiftFunctor _ a) ⋙
        (upperStar B f).leftDerivedFunctor ≅
      (upperStar B f).leftDerivedFunctor ⋙ derivedTensorRight B X (singleE B E X d) ⋙
        shiftFunctor _ a :=
  letI := commShiftLeftDerivedUpperStar B f
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((upperStar B f).leftDerivedFunctor.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedTensorRightCompLeftDerivedUpperStarIso B f _) _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      ((derivedTensorRightFunctor B X).mapIso (singleEPullback B N E c f hY d)) _)

/-- The specified lineENormalForm construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def lineENormalForm (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    lineR B E X ≅ (upperStar B (AffineSpace PUnit.{u + 1} X ↘ X)).leftDerivedFunctor ⋙
      derivedTensorRight B (AffineSpace PUnit.{u + 1} X)
        (singleE B E (AffineSpace PUnit.{u + 1} X) 1) ⋙ shiftFunctor _ (2 : ℤ) := by
  let j := ProjectiveLine.affineChart X
  letI := commShiftLeftDerivedUpperStar B j
  apply lineShiftGeneral B j (ProjectiveLine X ↘ X)
    (AffineSpace PUnit.{u + 1} X ↘ X) (ProjectiveLine.affineChart_over X)
  exact ((upperStar B j).leftDerivedFunctor.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (singleEPullback B N E c j (affineTraceProjectiveInvertible N X hX) 1)

variable (e0 : ∀ X : Scheme.{u}, E X 0 ≅ (constantSheaf X.smallEtaleTopology B).obj (𝟙_ B))
  (flat : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, ObjectProperty.flat (E X d))
  (prod : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, E X d ⊗ E X 1 ≅ E X (d + 1))

/-- The specified productE construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def productE (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    ((derivedTensor B X).obj (singleE B E X d)).obj (singleE B E X 1) ≅
      singleE B E X (d + 1) :=
  singleProductGeneral B X _ _ _ (flat X hX d) (prod X hX d)

/-- The specified towerENormalForm construction used by the affine trace normal form.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: lem-amb-affine-trace-right-normal-form). -/
@[irreducible]
def towerENormalForm (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineTraceRightTower (fun e ↦ lineR B E (affineTraceTower S e)) d ≅
      (upperStar B (affineTraceProjection S d)).leftDerivedFunctor ⋙
        derivedTensorRight B (affineTraceTower S d) (singleE B E (affineTraceTower S d) d) ⋙
          shiftFunctor _ (2 * (d : ℤ)) := by
  induction d with
  | zero =>
    let e : derivedTensorRight B S (singleE B E S 0) ≅ 𝟭 _ :=
      (derivedTensorRightFunctor B S).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (e0 S) ≪≫ singleFunctorObjUnitIso B S) ≪≫
          derivedTensorRightUnitorNatIso B S
    exact (Functor.isoWhiskerRight (leftDerivedUpperStarId B S) _ ≪≫
      Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight e _ ≪≫
        Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm
  | succ d ih =>
    let T := affineTraceTower S d
    let U := affineTraceTower S (d + 1)
    let p := AffineSpace PUnit.{u + 1} T ↘ T
    let P := (upperStar B (affineTraceProjection S d)).leftDerivedFunctor
    let Q := (upperStar B p).leftDerivedFunctor
    let L := singleE B E U d
    let M := singleE B E U 1
    let k : (derivedTensorRight B U L ⋙ shiftFunctor _ (2 * (d : ℤ))) ⋙
        (derivedTensorRight B U M ⋙ shiftFunctor _ (2 : ℤ)) ≅
        derivedTensorRight B U (singleE B E U (d + 1)) ⋙
          shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ)) :=
      tensorShiftCompGeneral B U L M (2 * (d : ℤ)) 2 ≪≫
      Functor.isoWhiskerRight ((derivedTensorRightFunctor B U).mapIso
        (productE B N E flat prod U (affineTraceInvertible N S hS (d + 1)) d)) _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (by congr 1))
    exact Functor.isoWhiskerRight ih (lineR B E T) ≪≫
      Functor.isoWhiskerLeft _
        (lineENormalForm B N E c T (affineTraceInvertible N S hS d)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (tensorEPullback B N E c p (affineTraceInvertible N S hS d) d (2 * (d : ℤ))) _ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarComp B p (affineTraceProjection S d)).symm _

@[irreducible]
private def pullbackUnitTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (derivedTensorRight B X L).obj ((upperStar B f).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology B).obj (𝟙_ B)))) ≅ L :=
  (derivedTensorRight B X L).mapIso
    ((singleFunctorCompLeftDerivedUpperStarIso B f).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Scheme.upperStarConstantSheafIso B f).app (𝟙_ B))) ≪≫
    singleLeftUnitGeneral B X L

private theorem boundedOfIsoSingleShift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (Y : DerivedCategory C) (M : C) (a : ℤ)
    (e : Y ≅ ((DerivedCategory.singleFunctor C 0).obj M)⟦a⟧) :
    DerivedCategory.TStructure.t.plus Y := by
  apply (DerivedCategory.TStructure.t.plus).prop_of_iso e.symm
  have : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C 0).obj M) 0 :=
    inferInstance
  exact ⟨-a, DerivedCategory.TStructure.t.isGE_shift _ 0 a (-a) (by omega)⟩

include c e0 flat prod in
private theorem towerEBounded (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    DerivedCategory.TStructure.t.plus
      ((affineTraceRightTower (fun e ↦ lineR B E (affineTraceTower S e)) d).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf S.smallEtaleTopology B).obj (𝟙_ B)))) := by
  let e := towerENormalForm B N E c e0 flat prod S hS d
  apply boundedOfIsoSingleShift _ (E (affineTraceTower S d) d) (2 * (d : ℤ))
  exact e.app _ ≪≫ (shiftFunctor _ (2 * (d : ℤ))).mapIso
    (pullbackUnitTensor B (affineTraceProjection S d) (singleE B E (affineTraceTower S d) d))
end General
private theorem twistFlat (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    ObjectProperty.flat (Scheme.finiteEtaleTateSheaf A N X hA (d : ℤ)) := by
  have hstalk : ∀ x : X, IsUnit (N : X.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom
  apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
  exact (Scheme.finite_etale_torsion_twist_line X N hN hstalk A hA d).2.2.1

@[irreducible]
private def twistSheafProduct (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A N hA)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    Scheme.finiteEtaleTateSheaf A N X hA (d : ℤ) ⊗
      Scheme.finiteEtaleTateSheaf A N X hA 1 ≅
      Scheme.finiteEtaleTateSheaf A N X hA ((d + 1 : ℕ) : ℤ) :=
  t.p X hX d 1 ≪≫ eqToIso
    (congrArg (Scheme.finiteEtaleTateSheaf A N X hA) (by omega))

/-- The coordinate right functor has its ordinary finite Tate normal form.
Source: blueprint lemma-integral-linear-character--1, proof steps 6--7
(blueprint: lem-amb-affine-trace-right-normal-form).

Proof: induct on the number of coordinates. At zero, the zero Tate twist is
the constant tensor unit, pullback by identity is identity, and shift zero is
identity. At a successor, commute pullback through the preceding tensor and
shift by the canonical inverse-image tensor and shift comparisons. Combine the
two pullbacks using composition. The Tate pullback comparison identifies the
pulled-back old line with the same twist upstairs. Associativity of derived
tensor, flatness of Tate sheaves, and their signed tensor product identify the
two factors with the next positive Tate power. Shift addition changes 2d+2 to
2(d+1). This yields a natural isomorphism, not just objectwise isomorphisms.
On the constant input, exact inverse image preserves degree-zero sheaves and
tensoring flat Tate sheaves computes ordinary tensor. The result is a single
sheaf shifted by 2d, hence bounded below. All arguments include d=0, the empty
base and N=1 (zero coefficients). -/
theorem affineTraceRight_normalForm (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (affineTraceRight A N hA S d ≅
      ordinaryFinitePullback A (affineTraceProjection S d) ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S d) hA (d : ℤ))) ⋙
        shiftFunctor _ (2 * (d : ℤ))) ∧
    _root_.DerivedCategory.TStructure.t.plus
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let t := Scheme.finiteEtaleTwistPullbackData A N hN hA
  let E := fun (X : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf A N X hA (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let e0 := fun X ↦ Iso.refl (E X 0)
  let flat := fun X hX d ↦ twistFlat A N hN hA X hX d
  let prod := fun X hX d ↦ twistSheafProduct A N hA t X hX d
  exact ⟨⟨towerENormalForm (ModuleCat.{u + 1} A) N E c e0 flat prod S hS d⟩,
    towerEBounded (ModuleCat.{u + 1} A) N E c e0 flat prod S hS d⟩

end AlgebraicGeometry.Etale
