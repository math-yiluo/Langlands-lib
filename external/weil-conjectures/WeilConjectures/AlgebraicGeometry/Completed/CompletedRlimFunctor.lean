/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# The derived inverse-limit functor on strict completed-coefficient towers

Source: blueprint, proper base change, proposition Rlim functoriality;
Stacks Tags 079P and 08TC (blueprint: prop-weil-pbc-rlim-functoriality).

## Main statements

- `AlgebraicGeometry.Scheme.completedRlim_computation`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem completedRlimAbSheafify (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem completedRlimAbLocallyBijective (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

attribute [local instance] completedRlimAbSheafify completedRlimAbLocallyBijective

attribute [instance] reductionTower_isGrothendieckAbelian

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The ordinary inverse limit of strict towers, with its canonical limit maps.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerLimit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    reductionTowerCategory T (reductionModuleRing T R) ⥤ reductionModules T R :=
  lim

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Inverse limit is additive because it is a right adjoint and preserves binary products.
Source: blueprint Rlim functoriality (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance coherenceTowerLimit_additive (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedTowerLimit T R).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Rlim is the total right derived functor of the actual strict inverse-limit functor.
Its universal unit, not a choice of triangulated cones, determines its action on maps.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedRlim (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    DerivedCategory (reductionTowerCategory T (reductionModuleRing T R)) ⥤
      reductionDerivedCategory T R :=
  (completedTowerLimit T R).rightDerivedFunctor

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The universal comparison to the K-injective computation of Rlim.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (completedTowerLimit T R).rightDerivedFunctorUnit

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Rlim is computed by inverse limits of K-injective tower resolutions. It is
triangulated, and its universal derived pair identifies all resolution choices.
Source: blueprint proposition Rlim functoriality; Stacks Tags 079P and 08TC.
Proof: strict towers are Grothendieck abelian by the adic coefficient datum, hence have
functorial K-injective resolutions. The K-injective derivability structure constructs
the total right derived functor of inverse limit. Its unit is invertible on K-injectives,
and the derived functor is triangulated. The universal property gives a unique compatible
isomorphism between any two derived pairs; these are the resolution-choice comparisons.
(blueprint: prop-weil-pbc-rlim-functoriality). -/
theorem completedRlim_computation (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    [J.IsKInjective] :
    IsIso ((completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J)) := by
  change IsIso ((completedTowerLimit T R).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj J))
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical derived projection is obtained by deriving the actual limit projection.
Source: blueprint Rlim functoriality and its K-injective construction; Stacks 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimProjection (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) (n : ℕ) :
    completedRlim T R ⟶
      reductionTowerDerivedEvaluation T (reductionModuleRing T R) n :=
  Functor.rightDerivedFunctorNatTrans (lim.π (op n)) ≫
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (reductionTowerEvaluation T (reductionModuleRing T R) n)).hom

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The first Roos arrow is the product of the actual derived limit projections.
Source: blueprint Rlim functoriality and derived inverse limit; Stacks 07KC and 08TC
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimRoosProjection (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d))))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    (completedRlim T (completedReductionCoefficient T d)).obj M ⟶
      ∏ᶜ (completedTowerDerivedSequence T d M) :=
  Pi.lift (fun n ↦ (completedRlimProjection T (completedReductionCoefficient T d) n).app M)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
-- The universal right-derived comparison preserves each actual limit projection.
private theorem completedRlimProjection_unit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    (n : ℕ) :
    (completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J) ≫
        (completedRlimProjection T R n).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app J) ≫
        (reductionTowerEvaluation T (reductionModuleRing T R) n).mapDerivedCategoryFactors.inv.app
          J := by
  dsimp only [completedRlimUnit, completedRlimProjection, NatTrans.comp_app]
  rw [← Category.assoc]
  erw [Functor.rightDerivedNatTrans_app]
  rw [Category.assoc]
  have h := NatTrans.congr_app
    (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      (reductionTowerEvaluation T (reductionModuleRing T R) n))
    ((HomotopyCategory.quotient _ _).obj J)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  erw [h]
  simp only [Functor.mapDerivedCategoryFactorsh,
    Functor.mapHomologicalComplexUpToQuasiIsoFactorsh,
    NatTrans.mapHomotopyCategory, Functor.whiskerRight_app]
  simp
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The K-injective computation of Rlim gives the distinguished Roos triangle with
its specified projections, rather than a cone map chosen in a triangulated category.
Source: blueprint Rlim functoriality and derived inverse limit; Stacks 07KC and 08TC
(blueprint: prop-weil-pbc-rlim-functoriality).
Proof: represent M by a K-injective strict tower J. Exact countable products of
pro-etale module sheaves give the canonical localized Roos triangle for the actual
limit cone of J.asFunctor. The invertible derived unit identifies its first object
with completedRlim(M). Exact evaluation comparison isomorphisms identify its other
objects with the prescribed derived sequence. Naturality of localization lifts
identifies the transitions, and the universal right-derived comparison identifies
each limit projection. Their product is precisely completedRlimRoosProjection.
Transport the distinguished triangle along these isomorphisms. -/
theorem completedRlim_roos (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d))))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    ∃ δ : ∏ᶜ (completedTowerDerivedSequence T d M) ⟶
        ((completedRlim T (completedReductionCoefficient T d)).obj M)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (completedTowerDerivedStep T d M)
        ((completedRlim T (completedReductionCoefficient T d)).obj M)
        (completedRlimRoosProjection T d M) δ := by
  classical
  have := completedRlimAbSheafify T
  have := completedRlimAbLocallyBijective T
  let R := completedReductionCoefficient T d
  let B := reductionModules T R
  let C := reductionTowerCategory T (reductionModuleRing T R)
  have : HasFiniteBiproducts B := CategoryTheory.Abelian.hasFiniteBiproducts
  have : CountableAB4Star B := by
    have : (lim (J := Discrete ℕ) (C := B)).PreservesEpimorphisms :=
      { preserves := by
          intro F G f hf
          have h := (ProEt.countableProducts_exact.{t, t, 0} T R).2.2
            ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
            (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map f = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi B (Discrete ℕ)
    exact CountableAB4Star.of_hasExactLimitsOfShape_nat B
  have : IsGrothendieckAbelian.{t + 1} B :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, 0}
      (ProEt.topology T) R).1
  let hP := (derivedCategory_countableProducts_core.{0} B).choose
  let : HasCountableProducts (DerivedCategory B) := hP
  let E := HomotopyCategory.KInjectives.equivalence C
  obtain ⟨J, hJ, h⟩ := HomotopyCategory.KInjectives.mk_surjective (E.inverse.obj M)
  let eM : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J) ≅ M :=
    (E.functor.mapIso (eqToIso h)).symm ≪≫ E.counitIso.app M
  have : J.IsKInjective := hJ
  let c : Cone J.asFunctor :=
    { pt := ((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj J
      π :=
        { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app J
          naturality := by
            intro n m f
            apply HomologicalComplex.Hom.ext
            funext i
            exact (limit.w (J.X i) f).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro i
    exact limit.isLimit (J.X i)
  obtain ⟨δ, hδ⟩ := derivedCategory_towerLimit_triangle B hP inferInstance J c hc
  let en (n : ℕ) : DerivedCategory.Q.obj (J.asFunctor.obj (op n)) ≅
      completedTowerDerivedSequence T d M n :=
    ((reductionTowerEvaluation T (reductionModuleRing T R) n).mapDerivedCategoryFactors.app
      J).symm ≪≫
      (reductionTowerDerivedEvaluation T (reductionModuleRing T R) n).mapIso eM
  have : IsIso ((completedRlimUnit T R).app
      ((HomotopyCategory.quotient _ _).obj J)) := completedRlim_computation T R J
  let eL : DerivedCategory.Q.obj c.pt ≅ (completedRlim T R).obj M :=
    asIso ((completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J)) ≪≫
      (completedRlim T R).mapIso eM
  let ep := Pi.mapIso en
  have hp : eL.hom ≫ completedRlimRoosProjection T d M =
      Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (op n))) ≫ ep.hom := by
    apply Pi.hom_ext
    intro n
    dsimp only [completedRlimRoosProjection, ep]
    simp only [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
    dsimp only [eL, en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
    erw [Category.assoc, (completedRlimProjection T R n).naturality]
    erw [← Category.assoc, completedRlimProjection_unit]
    simp only [Category.assoc, Iso.app_inv]
    rfl
  have hn (n : ℕ) : (en (n + 1)).hom ≫ completedTowerDerivedStep T d M n =
      DerivedCategory.Q.map (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
        (en n).hom := by
    dsimp only [en, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    let τ := Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) _ _
      (reductionTowerDerivedEvaluation T (reductionModuleRing T R) (n + 1))
      (reductionTowerDerivedEvaluation T (reductionModuleRing T R) n)
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex
        (completedTowerEvaluationStep T (reductionModuleRing T R) n) (.up ℤ))
          DerivedCategory.Q)
    have hnτ := τ.naturality eM.hom
    change _ ≫ τ.app M = _
    erw [Category.assoc, hnτ]
    dsimp only [τ]
    erw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Functor.whiskerRight_app]
    simp only [HomotopyCategory.quotient_obj_as, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.app_inv]
    rfl
  have ht : ep.hom ≫ towerTransitionEndomorphism (completedTowerDerivedStep T d M) =
      towerTransitionEndomorphism (fun n : ℕ ↦ DerivedCategory.Q.map
        (J.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫ ep.hom :=
    towerTransitionEndomorphism_natural_backward _ _ (fun n ↦ (en n).hom) hn
  refine ⟨ep.inv ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map eL.hom, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk _ _ eL ep ep hp.symm ht.symm (by simp))).mp hδ

end AlgebraicGeometry.Scheme
