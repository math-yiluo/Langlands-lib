/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDerivedLimitFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.CompletedTowerPullback
/-!
# Pullback of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1261;
Stacks Project, Tag 099N (blueprint: def-weil-pbc-completed-pullback).

The structure map into the completed coefficient ring is built from its finite
projections. It is a morphism, with no invertibility assumption. The functor here
precedes derived inverse limit and acts on every strict derived tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

/-- Transport a homotopy-level derived counit to its actual complex representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
This is the composite of the existing quotient comparisons with the supplied counit. -/
def leftDerivedCounitOnComplex {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- Finite constant coefficient inverse image has its canonical isomorphism.
Source: Stacks Tags 09AK and 09AL (blueprint: def-weil-pbc-completed-pullback).
Proof: the constant sheaf inverse image comparison is an isomorphism; the other two
factors are the fixed constant-section coefficient comparisons. Compose these isomorphisms. -/
@[instance]
theorem completedFiniteCoefficientMap_isIso (n : ℕ) :
    IsIso (completedFiniteCoefficientMap g d n) := by
  change IsIso (d.finiteRingIso g n).hom
  infer_instance

/-- Module inverse image followed by extension along the completed structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleModuleInverseImage g (pbcAdicCompletion Y d) ⋙
    reductionChange X (completedCoefficientMap g d)

/-- Completed module pullback is additive.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-completed-pullback).
Proof: inverse image of abelian sheaves respects sums of maps, as does the induced
module inverse image. Sheafified scalar extension respects sums on tensor generators.
The composite therefore respects addition. -/
@[instance]
theorem completedModulePullback_additive : (completedModulePullback g d).Additive := by
  dsimp only [completedModulePullback]
  infer_instance

/-- Apply the module pullback to objects and maps at each strict tower level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerModulePullback :
    pbcTowers Y (pbcAdicCompletion Y d) ⥤ pbcTowers X (pbcAdicCompletion X d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedModulePullback g d)

/-- Levelwise pullback is additive, with equality checked at every level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: each component is the additive completed module pullback, and equality of
natural transformations is componentwise. -/
@[instance]
theorem completedTowerModulePullback_additive :
    (completedTowerModulePullback g d).Additive := by
  constructor
  intro M N f h
  apply NatTrans.ext
  funext n
  exact (completedModulePullback g d).map_add

private theorem completedCoefficientMap_eq_integralRingIso :
    completedCoefficientMap g d = (d.integralRingIso g).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap g d ≫ d.projection X n.unop =
    (d.integralRingIso g).hom ≫ d.projection X n.unop
  calc
    _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      rfl

private theorem completedModulePullback_eq_exact :
    completedModulePullback g d =
      proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g) := by
  unfold completedModulePullback
  rw [completedCoefficientMap_eq_integralRingIso]
  refine CategoryTheory.Functor.ext (fun M ↦
    (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose
      ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)) ?_
  intro M N f
  exact (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose_spec.choose
    ((proEtaleModuleInverseImage g (d.completedRing Y)).map f)

private instance completedModulePullback_finiteLimits :
    PreservesFiniteLimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedModulePullback_finiteColimits :
    PreservesFiniteColimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedTowerModulePullback_finiteLimits :
    PreservesFiniteLimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

private instance completedTowerModulePullback_finiteColimits :
    PreservesFiniteColimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedTowerPullbackPair
    (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      ∀ P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ,
        (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d)
          (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
            (op n)).mapHomologicalComplex (.up ℤ) |>.obj P)) →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The universal left derived pair is computed on objectwise K-flat representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: strict diagram K-flat replacements supply a quasi-isomorphism with objectwise
K-flat flat-term source. Pullback preserves quasi-isomorphisms between these by exact
inverse image and K-flat scalar extension. The additive termwise functor preserves
shifts and cones. Apply the resolving-class left-derived theorem; its counit is
invertible on every object of this class. All transitions are pulled back with the
same functor, so the computation remains a strict tower computation. -/
theorem completedTowerPullback_exists :
    ∃ (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedTowerPullbackPair g d LF ε := by
  let F := completedTowerModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · exact ⟨inferInstance, inferInstance⟩
  · intro P _
    infer_instance

/-- Canonical total left derived levelwise pullback, with its universal comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullback :
    DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) :=
  (completedTowerPullback_exists g d).choose

/-- The universal counit of strict tower pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullbackCounit :
    DerivedCategory.Qh ⋙ completedTowerPullback g d ⟶
      (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedTowerPullback_exists g d).choose_spec.choose

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedOrdinaryPullbackPair
    (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- Ordinary derived pullback has the universal pair computed by the one-object
K-flat resolving class. This is ordinary pullback before completion.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: use exact module inverse image followed by the K-flat scalar extension along c_g.
K-flat flat-term resolutions exist on the small site. Scalar extension preserves
quasi-isomorphisms between K-flat complexes. Apply the resolving-class theorem. -/
theorem completedOrdinaryPullback_exists :
    ∃ (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedOrdinaryPullbackPair g d LF ε := by
  let F := completedModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · intro P _
    infer_instance

/-- Ordinary total left derived completed-coefficient pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullback :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedOrdinaryPullback_exists g d).choose

/-- The fixed ordinary left-derived counit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullbackCounit :
    DerivedCategory.Qh ⋙ completedOrdinaryPullback g d ⟶
      (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedOrdinaryPullback_exists g d).choose_spec.choose

attribute [irreducible] completedTowerPullback completedOrdinaryPullback

private theorem independentKFlatRepresentatives
    {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u₂} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u₂}]
    [HasSheafify J AddCommGrpCat.{u₂}]
    (R : Sheaf J CommRingCat.{u₂})
    [HasDerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (K : DerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let G := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have := hp
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

/-- The tower universal counit on actual cochain representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullbackComplexCounit
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    (completedTowerPullback g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((completedTowerModulePullback g d).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d)
    (completedTowerPullback g d) (completedTowerPullbackCounit g d) P

/-- The ordinary universal counit on actual cochain representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullbackComplexCounit
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (completedOrdinaryPullback g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((completedModulePullback g d).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedModulePullback g d)
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackCounit g d) P

private theorem mapComplexObject_eq_of_functor_eq
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (h : F = G) (P : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P := by
  subst G
  rfl

/-- The two ordinary constant-tower pullback complexes are the same strict complex.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: at each degree and tower index both have g^*(P^q), differential g^*(d^q), and
identity transition. The structure maps and their proofs agree by extensionality. -/
theorem completedPullbackConstantComplex_eq
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    ((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) =
    ((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hobj (M : pbcModules Y (pbcAdicCompletion Y d)) :
      (Functor.const ℕᵒᵖ).obj ((completedModulePullback g d).obj M) =
        (Functor.const ℕᵒᵖ).obj M ⋙ completedModulePullback g d := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
      Functor.comp_map, Functor.const_obj_map]
    exact ((completedModulePullback g d).map_id M).symm
  have he : completedModulePullback g d ⋙ completedTowerConstant d X =
      completedTowerConstant d Y ⋙ completedTowerModulePullback g d := by
    refine CategoryTheory.Functor.ext hobj ?_
    intro M N f
    apply NatTrans.ext
    funext n
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  exact mapComplexObject_eq_of_functor_eq he P

/-- The representative normalization fixing the canonical comparison uniquely.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def HasCompletedPullbackConstantNormalization
    (e : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
        completedDerivedConstant d Y ⋙ completedTowerPullback g d) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) P →
        (completedDerivedConstant d X).map
            (completedOrdinaryPullbackComplexCounit g d P) ≫
          ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
            (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P)) =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (completedTowerPullback g d).map
            (((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P) ≫
          completedTowerPullbackComplexCounit g d
            (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)

private theorem exactComplexCounit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) [IsIso ε]
    (P : CochainComplex C ℤ) : IsIso (F.leftDerivedCounitOnComplex L ε P) := by
  dsimp only [Functor.leftDerivedCounitOnComplex]
  infer_instance

private theorem iso_eq_on_representatives
    {C D S : Type*} [Category C] [Category D]
    (L R : C ⥤ D) (b b' : L ≅ R) (Q : S → C) (p : S → Prop)
    (hrep : ∀ K, ∃ P, p P ∧ Nonempty (Q P ≅ K))
    (h : ∀ P, p P → b'.hom.app (Q P) = b.hom.app (Q P)) : b' = b := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨P, hP, ⟨eP⟩⟩ := hrep K
  apply (cancel_epi (L.map eP.hom)).1
  rw [b'.hom.naturality, b.hom.naturality, h P hP]

private theorem exactPullbackCounit_isIso
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] : IsIso ε := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedUnique L F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom ε W
  have he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε =
      F.mapDerivedCategoryFactorsh.hom := by
    simp only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
      Functor.leftDerivedNatTrans_fac, Iso.refl_hom, Category.comp_id]
  have : IsIso (Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (Functor.whiskerLeft DerivedCategory.Qh e.hom) ε

private def exactPullbackIso
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] :
    L ≅ F.mapDerivedCategory :=
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso B (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  (Functor.leftDerivedUnique L F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom ε
    (HomotopyCategory.quasiIso B (.up ℤ))).symm

open CategoryTheory.Functor

-- Exact-presentation proof utilities from CompletedOpenExchangeTransport.
-- They are private here because that downstream module cannot be imported.
private theorem exactDerivedCounitComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : L ≅ F.mapDerivedCategory, ∀ P : CochainComplex C ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let e := CategoryTheory.Functor.leftDerivedUnique F.mapDerivedCategory L ε
    F.mapDerivedCategoryFactorsh.hom W
  have hc (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
    have he := CategoryTheory.Functor.leftDerivedNatTrans_app L F.mapDerivedCategory ε
      F.mapDerivedCategoryFactorsh.hom W (𝟙 _)
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
    dsimp at hn
    simp only [NatTrans.id_app, Category.comp_id] at he
    change e.hom.app _ ≫ _ = _ at he
    simp only [CategoryTheory.Functor.leftDerivedCounitOnComplex]
    rw [← he, F.mapDerivedCategoryFactorsh_hom_app]
    simp only [← Category.assoc]
    rw [hn]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    simp
  refine ⟨e, hc, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hp : e'.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) =
      e.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) := by
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage K))).1
    rw [he', hc]
  apply (cancel_epi (L.map (DerivedCategory.Q.objObjPreimageIso K).hom)).1
  rw [e'.hom.naturality, e.hom.naturality, hp]

/-- Counit normalization for an exact presentation of a left-derived functor.
Naming the entire condition keeps the concrete module-category presentations out of
repeated elaborations of the choice predicate.
Source: Stacks 05S7, 099N
(blueprint: def-weil-pbc-completed-pullback). -/
private def PullbackCounitNormalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [hLim : PreservesFiniteLimits G] [hColim : PreservesFiniteColimits G]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory) : Prop :=
  ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P =
    ε P ≫ DerivedCategory.Q.map (eqToIso (hp P)).hom

private theorem exactDerivedCounitTransport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (he : F = G)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (hp : ∀ P : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P) :
    ∃! e : L ≅ G.mapDerivedCategory,
      PullbackCounitNormalization F G L
        (CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε) hp e := by
  cases he
  simpa only [PullbackCounitNormalization, eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id,
    Category.comp_id] using exactDerivedCounitComparison F L ε

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance exactTowerFiniteLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

private instance exactTowerFiniteColimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

private theorem constantComplex_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (P : CochainComplex C ℤ) :
    ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj
        (((Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C).mapHomologicalComplex (.up ℤ)).obj P) := by
  refine HomologicalComplex.ext ?_ ?_
  · funext q
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro n m f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (F.map_id (P.X q)).symm
  · intro i j _
    ext n
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

private theorem exactConstantComparison
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  exact Functor.exactSquare_fac e P

private theorem exactSquare_symm
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private def constantDerivedSquare
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)

private theorem constantDerivedSquare_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C) ⋙
      (Functor.whiskeringRight ℕᵒᵖ C D).obj F ≅
        F ⋙ (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D))
    (he : e = (Functor.compConstIso ℕᵒᵖ F).symm) :
    constantDerivedSquare F = (Functor.mapDerivedCategorySquareIso e).symm := by
  subst e
  apply Iso.ext
  exact exactSquare_symm (Functor.compConstIso ℕᵒᵖ F).symm

private def transportedSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (et : T ≅ T') (c : L' ⋙ DD ≅ DC ⋙ T') : L ⋙ DD ≅ DC ⋙ T :=
  isoWhiskerRight e DD ≪≫ c ≪≫ isoWhiskerLeft DC et.symm

attribute [local irreducible] constantDerivedSquare transportedSquare

private theorem transportConstantComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F G : C ⥤ D) [hF : F.Additive] [hG : G.Additive]
    [hLim : PreservesFiniteLimits G] [hColim : PreservesFiniteColimits G] (he : F = G)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (τ : ∀ P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ, Lt.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P)
    (hpt : ∀ P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj P =
        (((Functor.whiskeringRight ℕᵒᵖ C D).obj G).mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory)
    (E : Lt ≅ ((Functor.whiskeringRight ℕᵒᵖ C D).obj G).mapDerivedCategory)
    (hn : PullbackCounitNormalization F G L ε hp e)
    (ht : PullbackCounitNormalization
      ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ C D).obj G) Lt τ hpt E)
    (P : CochainComplex C ℤ) :
    let Ct := (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C)
    let Dt := (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D)
    let c := constantDerivedSquare G
    let b := transportedSquare Ct.mapDerivedCategory Dt.mapDerivedCategory e E c
    Dt.mapDerivedCategory.map (ε P) ≫
        Dt.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eqToHom (constantComplex_eq F P)) =
      b.hom.app (DerivedCategory.Q.obj P) ≫
        Lt.map (Ct.mapDerivedCategoryFactors.hom.app P) ≫
        τ ((Ct.mapHomologicalComplex (.up ℤ)).obj P) := by
  -- Equality of the ordinary functors also identifies every strict transition.
  simp only [PullbackCounitNormalization] at hn ht
  cases he
  simp only [eqToIso_refl, Iso.refl_hom] at hn ht
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn ht
  have hq :
      ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F).hom (.up ℤ)).app P) =
        eqToHom (constantComplex_eq F P) := by
    ext q n
    simp only [HomologicalComplex.eqToHom_f, eqToHom_app, eqToHom_refl]
    rfl
  dsimp only
  simp only [transportedSquare, constantDerivedSquare, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Category.assoc]
  erw [← E.inv.naturality_assoc]
  erw [← ht, Iso.inv_hom_id_app_assoc]
  have hs := exactConstantComparison (Functor.compConstIso ℕᵒᵖ F) P
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hs
  erw [hs]
  erw [← Functor.map_comp_assoc, hn, hq]

private theorem transportedComparison_cancel
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (E : T ≅ T') (c : L' ⋙ DD ≅ DC ⋙ T') (K : C) :
    (transportedSquare DC DD e E c).hom.app K ≫
        E.hom.app (DC.obj K) = DD.map (e.hom.app K) ≫ c.hom.app K := by
  simp only [transportedSquare, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem transportedComparison_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (et : T ≅ T') (c c' : L' ⋙ DD ≅ DC ⋙ T')
    (c₀ : L ⋙ DD ≅ DC ⋙ T) (hc : c = c')
    (hb : transportedSquare DC DD e et c = c₀) (K : C) :
    c₀.hom.app K ≫ et.hom.app (DC.obj K) =
      DD.map (e.hom.app K) ≫ c'.hom.app K := by
  subst c₀
  subst c'
  exact transportedComparison_cancel DC DD e et c K

private theorem exactLeftDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (P : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app P) := by
  have hh := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at hh
  rw [F.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  apply (cancel_mono (G.rightDerivedFunctor.map
    (F.mapDerivedCategoryFactors.hom.app P))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [G.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at hh
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hh
  exact hh

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits

private theorem exactConstantIso_existsUnique
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εt : DerivedCategory.Qh ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    [Lt.IsLeftDerivedFunctor εt (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ C) (.up ℤ))]
    (p : CochainComplex C ℤ → Prop)
    (hrep : ∀ K, ∃ P, p P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K)) :
    let Ct := (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C)
    let Dt := (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D)
    ∃! b : L ⋙ Dt.mapDerivedCategory ≅ Ct.mapDerivedCategory ⋙ Lt,
      ∀ P, p P →
        Dt.mapDerivedCategory.map (F.leftDerivedCounitOnComplex L ε P) ≫
          Dt.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (eqToHom (constantComplex_eq F P)) =
        b.hom.app (DerivedCategory.Q.obj P) ≫
          Lt.map (Ct.mapDerivedCategoryFactors.hom.app P) ≫
          Functor.leftDerivedCounitOnComplex ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)
            Lt εt ((Ct.mapHomologicalComplex (.up ℤ)).obj P) := by
  let Ct := (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C)
  let Dt := (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D)
  let Ft := (Functor.whiskeringRight ℕᵒᵖ C D).obj F
  have : PreservesFiniteLimits Ft := exactTowerFiniteLimits F
  have : PreservesFiniteColimits Ft := exactTowerFiniteColimits F
  obtain ⟨e, he, _⟩ := exactDerivedCounitTransport F F rfl L ε (fun _ ↦ rfl)
  obtain ⟨et, het, _⟩ := exactDerivedCounitTransport Ft Ft rfl Lt εt (fun _ ↦ rfl)
  let b : L ⋙ Dt.mapDerivedCategory ≅ Ct.mapDerivedCategory ⋙ Lt :=
    transportedSquare Ct.mapDerivedCategory Dt.mapDerivedCategory e et (constantDerivedSquare F)
  have hb (P) (_ : p P) := transportConstantComparison F F rfl L Lt
    (Functor.leftDerivedCounitOnComplex F L ε)
    (Functor.leftDerivedCounitOnComplex Ft Lt εt)
    (fun _ ↦ rfl) (fun _ ↦ rfl) e et he het P
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply iso_eq_on_representatives _ _ b b' DerivedCategory.Q.obj p hrep
  intro P hP
  have : IsIso εt := exactPullbackCounit_isIso Ft Lt εt
  have : IsIso (Functor.leftDerivedCounitOnComplex Ft Lt εt
      ((Ct.mapHomologicalComplex (.up ℤ)).obj P)) := exactComplexCounit_isIso Ft Lt εt _
  apply (cancel_mono (Lt.map (Ct.mapDerivedCategoryFactors.hom.app P) ≫
    Functor.leftDerivedCounitOnComplex Ft Lt εt
      ((Ct.mapHomologicalComplex (.up ℤ)).obj P))).1
  exact (hb' P hP).symm.trans (hb P hP)

private instance pullbackOrdinaryUniversal :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold completedOrdinaryPullback completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.1

private instance pullbackTowerUniversal :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  unfold completedTowerPullback completedTowerPullbackCounit
  exact (completedTowerPullback_exists g d).choose_spec.choose_spec.1

/-- Pullback of a constant tower is canonically the constant tower of ordinary pullback.
The equality on strict representatives and both universal counits fix the comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: constant K-flat representatives lie in the tower resolving class. Both sides
compute the same pulled-back constant complex. Its strict equality gives the displayed
normalization. Universal left derivation extends it uniquely and proves invertibility. -/
theorem completedPullbackConstantIso_exists :
    ∃! e : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
        completedDerivedConstant d Y ⋙ completedTowerPullback g d,
      HasCompletedPullbackConstantNormalization g d e := by
  exact exactConstantIso_existsUnique
    (hC := proEtaleRingModules_hasDerivedCategory Y (pbcAdicCompletion Y d))
    (hD := proEtaleRingModules_hasDerivedCategory X (pbcAdicCompletion X d))
    (hCt := pbcTowers_hasDerivedCategory Y (pbcAdicCompletion Y d))
    (hDt := pbcTowers_hasDerivedCategory X (pbcAdicCompletion X d))
    (completedModulePullback g d) (completedOrdinaryPullback g d)
    (completedTowerPullback g d) (completedOrdinaryPullbackCounit g d)
    (completedTowerPullbackCounit g d)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d))
    (independentKFlatRepresentatives (pbcAdicCompletion Y d))

/-- The uniquely normalized constant-tower pullback comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedPullbackConstantIso :
    completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ completedTowerPullback g d :=
  (completedPullbackConstantIso_exists g d).exists.choose

/-- Completed pullback is the derived inverse limit of the pulled-back reduction tower.
Its restriction to intrinsically complete objects is the completed pullback of the node.
Source: Stacks Tag 099N (blueprint: definition-completed-inverse-image--1). -/
def completedPullbackObject
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedTowerRlim d X).obj
    ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K))

/-- The strict-tower-induced comparison, using the canonical K → Rlim ΔK unit.
No map between independently selected cones is used.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedPullbackComparison
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    (completedOrdinaryPullback g d).obj K ⟶ completedPullbackObject g d K :=
  (completedConstantRlimUnit d X).app ((completedOrdinaryPullback g d).obj K) ≫
    (completedTowerRlim d X).map
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K))

private theorem constantRlimUnit_eq (V : Scheme.{u}) :
    completedConstantRlimUnit d V = (d.constantRlimAdjunction V).unit := by
  apply (completedConstantRlimUnit_exists d V).unique
    (completedConstantRlimUnit_exists d V).exists.choose_spec
  intro P
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact exactLeftDerivedUnit (completedTowerConstant d V) lim constLimAdj P

private theorem pullbackDatumTowerModulePull_eq :
    completedTowerModulePullback g d = d.towerModulePull g := by
  exact congrArg ((Functor.whiskeringRight ℕᵒᵖ _ _).obj) (completedModulePullback_eq_exact g d)

/-- The module comparison on actual complexes, with the additive structures installed.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback).
Proof: substitute completedModulePullback_eq_exact; preservation of zero morphisms is a
proposition, so its two instance witnesses coincide. The mapped complexes agree. -/
private theorem pullbackDatumModulePullComplex_eq
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P =
      ((proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g)).mapHomologicalComplex (.up ℤ)).obj P := by
  have aux (F G : pbcModules Y (pbcAdicCompletion Y d) ⥤
      pbcModules X (pbcAdicCompletion X d))
      [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (he : F = G) :
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P := by
    cases he
    rfl
  exact aux _ _ (completedModulePullback_eq_exact g d)

/-- The strict comparison on complexes keeps all levels and transitions.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback).
Proof: substitute pullbackDatumTowerModulePull_eq. The zero-preservation witnesses
are proof irrelevant, so the mapped strict tower complexes agree. -/
private theorem pullbackDatumTowerPullComplex_eq
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    ((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P =
      ((d.towerModulePull g).mapHomologicalComplex (.up ℤ)).obj P := by
  have aux (F G : pbcTowers Y (pbcAdicCompletion Y d) ⥤
      pbcTowers X (pbcAdicCompletion X d))
      [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (he : F = G) :
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P := by
    cases he
    rfl
  exact aux _ _ (pullbackDatumTowerModulePull_eq g d)

/-- The ordinary derived comparison is uniquely fixed by its resolving counit.
Source: Stacks 099N, 06YS (blueprint: def-weil-pbc-completed-pullback).
Proof: the ordinary functors coincide by completedModulePullback_eq_exact. The datum
presentation is exact, so its termwise factorization is a universal left-derived
counit. Uniqueness of the universal derived pair gives the isomorphism and the
displayed counit equation on complexes. Resolve by K-flat complexes to prove
uniqueness; exactness extends the equation to every representative. -/
private theorem pullbackDatumOrdinaryTransport_exists :
    ∃! e : completedOrdinaryPullback g d ≅ d.pull g,
      PullbackCounitNormalization (completedModulePullback g d)
        (proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g)) (completedOrdinaryPullback g d)
        (completedOrdinaryPullbackComplexCounit g d)
        (pullbackDatumModulePullComplex_eq g d) e := by
  exact exactDerivedCounitTransport (completedModulePullback g d)
    (proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso g)) (completedModulePullback_eq_exact g d)
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackCounit g d)
    (pullbackDatumModulePullComplex_eq g d)

/-- Ordinary pullback transport with its universal-counit normalization.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback). -/
private def pullbackDatumOrdinaryTransport : completedOrdinaryPullback g d ≅ d.pull g :=
  (pullbackDatumOrdinaryTransport_exists g d).exists.choose

/-- The strict derived tower comparison retains the universal resolving counit.
Source: Stacks 099N, 06YS (blueprint: def-weil-pbc-completed-pullback).
Proof: pullbackDatumTowerModulePull_eq identifies the whole ordinary tower functor.
Its exact termwise derived functor and the objectwise K-flat derived construction
are universal left-derived pairs. Their unique comparison satisfies the equation
below. In particular it compares one strict tower, including transitions, rather
than choosing independent isomorphisms of its finite evaluations. -/
private theorem pullbackDatumTowerTransport_exists :
    ∃! e : completedTowerPullback g d ≅ d.towerPull g,
      PullbackCounitNormalization
        (hLim := (d.towerModulePull_exact g).1)
        (hColim := (d.towerModulePull_exact g).2)
        (completedTowerModulePullback g d)
        (d.towerModulePull g) (completedTowerPullback g d)
        (completedTowerPullbackComplexCounit g d)
        (pullbackDatumTowerPullComplex_eq g d) e := by
  have : PreservesFiniteLimits (d.towerModulePull g) :=
    (d.towerModulePull_exact g).1
  have : PreservesFiniteColimits (d.towerModulePull g) :=
    (d.towerModulePull_exact g).2
  exact exactDerivedCounitTransport (completedTowerModulePullback g d)
    (d.towerModulePull g) (pullbackDatumTowerModulePull_eq g d)
    (completedTowerPullback g d) (completedTowerPullbackCounit g d)
    (pullbackDatumTowerPullComplex_eq g d)

/-- Canonical comparison of derived strict tower pullback presentations.
Source: Stacks 099N (blueprint: def-weil-pbc-completed-pullback). -/
private def pullbackDatumTowerTransport : completedTowerPullback g d ≅ d.towerPull g :=
  (pullbackDatumTowerTransport_exists g d).exists.choose

private theorem datumConstantComparison (K : d.derived Y) :
    (completedPullbackConstantIso g d).hom.app K ≫
        (pullbackDatumTowerTransport g d).hom.app ((completedDerivedConstant d Y).obj K) =
      (completedDerivedConstant d X).map ((pullbackDatumOrdinaryTransport g d).hom.app K) ≫
        (d.derivedConstantPullbackIso g).inv.app K := by
  let F := proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
    (d.integralRingIso g)
  let c : d.pull g ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ d.towerPull g :=
    constantDerivedSquare
      (C := pbcModules Y (pbcAdicCompletion Y d))
      (D := pbcModules X (pbcAdicCompletion X d))
      (hC := proEtaleRingModules_hasDerivedCategory Y (pbcAdicCompletion Y d))
      (hD := proEtaleRingModules_hasDerivedCategory X (pbcAdicCompletion X d))
      (hCt := pbcTowers_hasDerivedCategory Y (pbcAdicCompletion Y d))
      (hDt := pbcTowers_hasDerivedCategory X (pbcAdicCompletion X d)) F
  have hc : c = (d.derivedConstantPullbackIso g).symm := by
    have hi : d.constantPullbackIso g = (Functor.compConstIso ℕᵒᵖ F).symm := by
      ext M n
      rfl
    have hframe : c = constantDerivedSquare F := by rfl
    exact hframe.trans (constantDerivedSquare_eq F (d.constantPullbackIso g) hi)
  let b : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ completedTowerPullback g d :=
    transportedSquare (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (pullbackDatumOrdinaryTransport g d) (pullbackDatumTowerTransport g d) c
  have hb : HasCompletedPullbackConstantNormalization g d b := by
    intro P _
    have hp := transportConstantComparison
      (C := pbcModules Y (pbcAdicCompletion Y d))
      (D := pbcModules X (pbcAdicCompletion X d))
      (hC := proEtaleRingModules_hasDerivedCategory Y (pbcAdicCompletion Y d))
      (hD := proEtaleRingModules_hasDerivedCategory X (pbcAdicCompletion X d))
      (hCt := pbcTowers_hasDerivedCategory Y (pbcAdicCompletion Y d))
      (hDt := pbcTowers_hasDerivedCategory X (pbcAdicCompletion X d))
      (hF := completedModulePullback_additive g d)
      (hG := proEtaleRingModulePullback_additive g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g))
      (hLim := proEtaleRingModulePullback_preservesFiniteLimits g
        (d.completedRing Y) (d.completedRing X) (d.integralRingIso g))
      (hColim := proEtaleRingModulePullback_preservesFiniteColimits g
        (d.completedRing Y) (d.completedRing X) (d.integralRingIso g))
      (completedModulePullback g d) F
      (completedModulePullback_eq_exact g d)
      (completedOrdinaryPullback g d) (completedTowerPullback g d)
      (completedOrdinaryPullbackComplexCounit g d) (completedTowerPullbackComplexCounit g d)
      (pullbackDatumModulePullComplex_eq g d) (pullbackDatumTowerPullComplex_eq g d)
      (pullbackDatumOrdinaryTransport g d) (pullbackDatumTowerTransport g d)
      (pullbackDatumOrdinaryTransport_exists g d).exists.choose_spec
      (pullbackDatumTowerTransport_exists g d).exists.choose_spec P
    exact hp
  -- This is equality in the strict derived tower category; evaluating separate
  -- levels would not determine the comparison.
  have he : b = completedPullbackConstantIso g d :=
    (completedPullbackConstantIso_exists g d).unique hb
      (completedPullbackConstantIso_exists g d).exists.choose_spec
  exact transportedComparison_eq (completedDerivedConstant d Y)
    (completedDerivedConstant d X) (pullbackDatumOrdinaryTransport g d)
    (pullbackDatumTowerTransport g d) c (d.derivedConstantPullbackIso g).symm
    (completedPullbackConstantIso g d) hc he K

private theorem reductionAugmentationTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (CT : C ⥤ E) (CS : D ⥤ F) (RY : C ⥤ E) (RX : D ⥤ F)
    (L L' : C ⥤ D) (T T' : E ⥤ F) (e : L ≅ L') (et : T ≅ T')
    (b : L ⋙ CS ≅ CT ⋙ T) (c : CT ⋙ T' ≅ L' ⋙ CS)
    (uY : CT ⟶ RY) (uX : CS ⟶ RX) (τ : RY ⋙ T' ≅ L' ⋙ RX)
    (K : C)
    (hb : b.hom.app K ≫ et.hom.app (CT.obj K) =
      CS.map (e.hom.app K) ≫ c.inv.app K)
    (hτ : T'.map (uY.app K) ≫ τ.hom.app K =
      c.hom.app K ≫ uX.app (L'.obj K)) :
    (b.hom.app K ≫ T.map (uY.app K)) ≫
        (et.hom.app (RY.obj K) ≫ τ.hom.app K ≫ RX.map (e.inv.app K)) =
      uX.app (L.obj K) := by
  calc
    _ = (b.hom.app K ≫ et.hom.app (CT.obj K)) ≫
        (T'.map (uY.app K) ≫ τ.hom.app K) ≫ RX.map (e.inv.app K) := by
      simp only [Category.assoc]
      rw [et.hom.naturality_assoc]
    _ = CS.map (e.hom.app K) ≫ uX.app (L'.obj K) ≫ RX.map (e.inv.app K) := by
      rw [hb, hτ]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    _ = uX.app (L.obj K) ≫ RX.map (e.hom.app K) ≫ RX.map (e.inv.app K) := by
      rw [← Category.assoc, uX.naturality, Category.assoc]
    _ = _ := by
      rw [← RX.map_comp, Iso.hom_inv_id_app, RX.map_id, Category.comp_id]

/-- On intrinsically complete inputs this construction is ordinary pullback followed
by intrinsic derived completion, with exactly its completion unit. Under the canonical
derived-complete constant/completed coefficient equivalences this is Stacks' completed pullback.
Source: Stacks Tag 099N, clauses (2),(5) (blueprint: def-weil-pbc-completed-pullback).
Proof: apply the constant/completed coefficient equivalence to a K-flat representative.
Its finite-reduction comparisons identify the pulled-back strict tower, including
transitions, with the reduction tower of ordinary pullback. They identify the derived
limits and their units. The intrinsic Koszul completion comparison identifies that
limit with the displayed intrinsic completion and takes the comparison to its unit. -/
theorem completedPullback_isCompletion (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r a ha K C e)
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedOrdinaryPullback g d).obj K) :
    ∃ α : completedPullbackObject g d K ≅
        intrinsicCompletion X d r a ha ((completedOrdinaryPullback g d).obj K) P eP,
      completedPullbackComparison g d K ≫ α.hom =
        intrinsicCompletionUnit X d r a ha ((completedOrdinaryPullback g d).obj K) P eP := by
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let R := completedTowerRlim d X
  let t : (completedTowerPullback g d).obj ((completedReductionTower Y d).obj K) ≅
      (completedReductionTower X d).obj ((completedOrdinaryPullback g d).obj K) :=
    eT.app ((completedReductionTower Y d).obj K) ≪≫ τ.app K ≪≫
      (completedReductionTower X d).mapIso (eL.app K).symm
  have ht : ((completedPullbackConstantIso g d).hom.app K ≫
      (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
        t.hom = (completedReductionTowerUnit d X).app
          ((completedOrdinaryPullback g d).obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha
    ((completedOrdinaryPullback g d).obj K) P eP
  refine ⟨R.mapIso t ≪≫ c.symm, ?_⟩
  change completedPullbackComparison g d K ≫ (R.map t.hom ≫ c.inv) = _
  rw [← Category.assoc]
  have hu : completedPullbackComparison g d K ≫ R.map t.hom =
      intrinsicCompletionUnit X d r a ha
        ((completedOrdinaryPullback g d).obj K) P eP ≫ c.hom := by
    dsimp only [completedPullbackComparison]
    rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
    exact hc.symm
  rw [hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme
