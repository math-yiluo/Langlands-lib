/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.OrdinaryCommonQuotientTower.OrdinaryCommonQuotientTowerSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

/-! # Strict compatibility of ordinary finite pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteProjection_surjective (T : Scheme.{u}) (n : ℕ)
    (U : T.ProEtᵒᵖ) :
    Function.Surjective ((completedReductionProjection T d n).hom.app U) := by
  let : IsNoetherianRing A := d.noetherian
  let V : (CompletedConstantAlgebra.smallSite T)ᵒᵖ := op (AsSmall.up.obj U.unop)
  let β := CompletedConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)
  let δ := (CompletedConstantAlgebra.pushRing T).mapIso
      (pbcLevelConstantComparison T d n).symm ≪≫
    (CompletedConstantAlgebra.constantsIso T).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  have hp : completedReductionProjection T d n =
      (pbcCompletedComparison T d).inv ≫ limit.π (adicLisseRingSystem T d.ideal) (op n) ≫
        (pbcLevelConstantComparison T d n).hom := by
    apply (cancel_epi (pbcCompletedComparison T d).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_assoc,
      pbcCompletedComparison, completedReductionProjection, reductionCoefficientSystem,
      pbcConstantSystemComparison, NatIso.ofComponents_hom_app] using
      HasLimit.isoOfNatIso_hom_π (pbcConstantSystemComparison T d) (op n)
  have hcomp := CompletedConstantAlgebra.projection_transport T d.ideal
    (pbcCompletedComparison T d) n (pbcLevelConstantComparison T d n)
    (completedReductionProjection T d n) hp
  have heq (b : (pbcAdicCompletion T d).obj.obj U) :
      (ConstantCompletion.projection (CompletedConstantAlgebra.smallTopology T)
          A d.ideal n).hom.app V (β.hom.hom.app V b) =
        δ.hom.hom.app V ((completedReductionProjection T d n).hom.app U b) :=
    congrArg (fun k ↦ k.hom.app V b) hcomp
  have hβ' (b) : β.hom.hom.app V (β.inv.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) β.inv_hom_id) b
  have hδ (b : (reductionCoefficient T d n).obj.obj U) :
      δ.inv.hom.app V (δ.hom.hom.app V b) = b :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app V) δ.hom_inv_id) b
  intro y
  obtain ⟨b, hb⟩ := ((ConstantCompletion.flat_and_quotients
    (CompletedConstantAlgebra.smallTopology T) A d.ideal).2.1 n V.unop).1
      (δ.hom.hom.app V y)
  refine ⟨β.inv.hom.app V b, ?_⟩
  have hh := heq (β.inv.hom.app V b)
  rw [hβ', hb] at hh
  exact (hδ _).symm.trans ((congrArg (δ.inv.hom.app V) hh).symm.trans (hδ _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reductionUnit_epi (T : Scheme.{u}) (n : ℕ)
    (M : pbcModules T (pbcAdicCompletion T d)) :
    Epi (((completedReductionModuleUnit d T).app M).app (op n)) := by
  let q := completedReductionProjection T d n
  let e := eqToIso (reductionChange_obj_eq T q M)
  let u := (((completedReductionModuleUnit d T).app M).app (op n)) ≫
    (pbcRestrict q).map e.hom
  have hq : Presheaf.IsLocallySurjective (ProEt.topology T) q.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _ (finiteProjection_surjective d T n)
  have hu : Epi u := SheafOfModules.quotientUnit_epi q hq M u (by
    intro U x
    change e.hom.val.app U
      (((((completedReductionModuleUnit d T).app M).app (op n))).val.app U x) = _
    erw [show (((completedReductionModuleUnit d T).app M).app (op n)).val.app U x =
      reductionTensorSection T (pbcAdicProjection T d n) M U 1 x from
        (completedReductionModuleUnit_exists d T).exists.choose_spec M n U x]
    unfold reductionTensorSection
    unfold completedAdicChangeTensor
    exact congrArg (fun k ↦ k.val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf q M).presheaf).app U
        ((1 : (reductionCoefficient T d n).obj.obj U) ⊗ₜ[
          (pbcAdicCompletion T d).obj.obj U, (q.hom.app U).hom] x)))
      (eqToHom_trans (reductionChange_obj_eq T q M).symm
        (reductionChange_obj_eq T q M)))
  have : Epi u := hu
  have he : (((completedReductionModuleUnit d T).app M).app (op n)) =
      u ≫ (pbcRestrict q).map e.inv := by
    simp only [u, ← Functor.map_comp, Category.assoc, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [he]
  infer_instance

private def completedAdjunction
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ⟶ S) :
    proEtaleModuleInverseImage g R ⋙ reductionChange X c ⊣ pbcRestrict c ⋙ T g R :=
  (canonicalAdjunction g R).comp
    (pbcScalarAdjunction c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedHomEquiv_section
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ⟶ S)
    (M : pbcModules Y R)
    (N : pbcModules X S)
    (k : (proEtaleModuleInverseImage g R ⋙ reductionChange X c).obj M ⟶ N)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    (((completedAdjunction g R S c).homEquiv M N k).val.app (op V) x) =
      k.val.app (op ((proEtaleBaseChange g).obj V))
        (reductionTensorSection X c _
          (op ((proEtaleBaseChange g).obj V)) 1
          (completedReductionInverseImageGenerator g R M
            V ((proEtaleBaseChange g).obj V) (𝟙 _) x)) := by
  dsimp only [completedModulePullback, reductionChange] at *
  unfold completedAdjunction
  rw [Adjunction.comp_homEquiv]
  change (((canonicalAdjunction g R).homEquiv M _
    (((pbcScalarAdjunction c).homEquiv _ _) k)).val.app
      (op V) x) = _
  rw [Adjunction.homEquiv_unit]
  change (((pbcScalarAdjunction c).homEquiv _ _ k).val.app
    (op ((proEtaleBaseChange g).obj V))
      (((canonicalAdjunction g R).unit.app M).val.app (op V) x)) = _
  rw [canonicalUnit_sections]
  rw [Adjunction.homEquiv_unit]
  change k.val.app _ (((pbcScalarAdjunction c).unit.app
    ((proEtaleModuleInverseImage g R).obj M)).val.app _ _) = _
  erw [(pbcScalarAdjunction_exists c).exists.choose_spec]
  unfold completedReductionInverseImageGenerator
  simp only [op_id]
  rw [((proEtaleModuleInverseImage g R).obj M).val.map_id]
  rfl

private theorem comp_section {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {L M N : pbcModules T R} (f : L ⟶ M) (k : M ⟶ N)
    (V : T.ProEtᵒᵖ) (x : L.val.obj V) :
    (f ≫ k).val.app V x = k.val.app V (f.val.app V x) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonAux
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S B C : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ⟶ S)
    (πb : S ⟶ B) (πa : S ⟶ C) (q : B ⟶ C) (hp : πb ≫ q = πa)
    (hs : ∀ (Q : pbcModules Y R) (N : pbcModules X S)
      (k : (proEtaleModuleInverseImage g R ⋙ reductionChange X c).obj Q ⟶ N)
      (V : Y.ProEt) (x : Q.val.obj (op V)),
      (((completedAdjunction g R S c).homEquiv Q N k).val.app (op V) x) =
        k.val.app (op ((proEtaleBaseChange g).obj V))
          (reductionTensorSection X c _ (op ((proEtaleBaseChange g).obj V)) 1
            (completedReductionInverseImageGenerator g R Q V
              ((proEtaleBaseChange g).obj V) (𝟙 _) x)))
    (M Qb Qa : pbcModules Y R) (ub : M ⟶ Qb) (ua : M ⟶ Qa)
    (δ : Qb ⟶ Qa) [Epi ub] (hu : ub ≫ δ = ua)
    (Nb : pbcModules X B) (Na : pbcModules X C)
    (eb : (proEtaleModuleInverseImage g R ⋙ reductionChange X c).obj Qb ⟶
      (pbcRestrict πb).obj Nb)
    (ea : (proEtaleModuleInverseImage g R ⋙ reductionChange X c).obj Qa ⟶
      (pbcRestrict πa).obj Na)
    (τ : Nb ⟶ (pbcRestrict q).obj Na)
    (gb : ∀ V : Y.ProEt, M.val.obj (op V) → Nb.val.obj
      (op ((proEtaleBaseChange g).obj V)))
    (ga : ∀ V : Y.ProEt, M.val.obj (op V) → Na.val.obj
      (op ((proEtaleBaseChange g).obj V)))
    (hb : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      completedReductionSectionEquation X πb eb (op ((proEtaleBaseChange g).obj V))
        (reductionTensorSection X c _ (op ((proEtaleBaseChange g).obj V)) 1
          (completedReductionInverseImageGenerator g R Qb V
            ((proEtaleBaseChange g).obj V) (𝟙 _) (ub.val.app (op V) x))) (gb V x))
    (ha : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      completedReductionSectionEquation X πa ea (op ((proEtaleBaseChange g).obj V))
        (reductionTensorSection X c _ (op ((proEtaleBaseChange g).obj V)) 1
          (completedReductionInverseImageGenerator g R Qa V
            ((proEtaleBaseChange g).obj V) (𝟙 _) (ua.val.app (op V) x))) (ga V x))
    (ht : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      completedReductionSectionEquation X q τ
        (op ((proEtaleBaseChange g).obj V)) (gb V x) (ga V x)) :
    eb ≫ (pbcRestrict πb).map τ ≫ (pbcRestrictComp πb q πa hp).hom.app Na =
      (proEtaleModuleInverseImage g R ⋙ reductionChange X c).map δ ≫ ea := by
  apply ((completedAdjunction g R S c).homEquiv _ _).injective
  apply (cancel_epi ub).mp
  rw [Adjunction.homEquiv_naturality_left, ← Category.assoc ub δ, hu]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  conv_lhs => rw [comp_section]
  conv_rhs => rw [comp_section]
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  have hb' := hb V.unop x
  have ha' := ha V.unop x
  have ht' := ht V.unop x
  unfold completedReductionSectionEquation at hb' ha' ht'
  change ((pbcRestrictComp πb q πa hp).hom.app Na).val.app _
    (τ.val.app _ (eb.val.app _ _)) = ea.val.app _ _
  exact ((pbcRestrictComp_exists πb q πa hp).exists.choose_spec Na _ _).trans
    ((congrArg (fun t ↦ τ.val.app _ t) hb').trans (ht'.trans ha'.symm))

/-- Ordinary finite pullback balancing respects the actual strict reduction transitions.
Source: main-20261015, sk-prop-sf-cbc, completed extension-by-zero comparison,
finite-reduction compatibility, Step 4; Stacks Tags 03EK and 03EL
(blueprint: lem-cbc-ordinary-finite-quotient-comparison).

Proof: transport the sectionwise surjectivity of the completed constant projection
through the fixed coefficient comparisons. The sheaf quotient unit M to its finite
reduction is therefore epic. Transpose the desired equality through the composite
of canonical inverse image and scalar extension, and cancel that quotient unit.
Naturality of the strict reduction-tower unit identifies its composite with the
tower arrow with the smaller quotient unit. The normalized inverse-image and scalar
units evaluate the transposes on 1 tensor inverse image of the quotient-unit section.
The ordinary comparison sends this to the finite generator (1,1,m), and the quotient
transition sends that generator to (1,1,m) at the smaller level. Restriction
composition is identity on underlying sections. These formulas give equal sections
for both transposes, hence equal maps. The argument covers equal indices, the zero
ring, zero modules, and empty site objects. -/
theorem ordinary_finite_quotient_comparison
    (M : pbcModules Y (pbcAdicCompletion Y d)) (a b : ℕ) (h : a ≤ b) :
    (completedReductionOrdinaryComparison g d b).hom.app M ≫
        (pbcRestrict (completedReductionProjection X d b)).map
          ((completedReductionOrdinaryTransition g d a b h).app M) ≫
        (pbcRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteModules g d a).obj
              ((reductionChange Y (completedReductionProjection Y d a)).obj M)) =
      (((completedTowerModulePullback g d).obj
        ((completedReductionModuleTowerFunctor Y d).obj M)).map (homOfLE h).op) ≫
        (completedReductionOrdinaryComparison g d a).hom.app M := by
  have := reductionUnit_epi d Y b M
  have hu := ((completedReductionModuleUnit d Y).app M).naturality (homOfLE h).op
  change 𝟙 M ≫ _ = _ at hu
  have hu' := hu.symm.trans (Category.id_comp _)
  apply comparisonAux g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (reductionCoefficient X d b) (reductionCoefficient X d a)
    (completedCoefficientMap g d) (completedReductionProjection X d b)
    (completedReductionProjection X d a) (reductionCoefficientMap X d b a h)
    (completedReductionProjection_comp X d b a h)
    (completedHomEquiv_section g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (completedCoefficientMap g d)) M _ _
    (((completedReductionModuleUnit d Y).app M).app (op b))
    (((completedReductionModuleUnit d Y).app M).app (op a))
    (((completedReductionModuleTowerFunctor Y d).obj M).map (homOfLE h).op)
    hu' _ _ ((completedReductionOrdinaryComparison g d b).hom.app M)
    ((completedReductionOrdinaryComparison g d a).hom.app M)
    ((completedReductionOrdinaryTransition g d a b h).app M)
    (fun V x ↦ completedReductionFiniteGenerator g d b M V
      ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x)
    (fun V x ↦ completedReductionFiniteGenerator g d a M V
      ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x)
  · intro V x
    have hn := (completedReductionOrdinaryComparison_exists g d b).exists.choose_spec
    change HasCompletedReductionOrdinaryComparisonNormalization g d b
      (completedReductionOrdinaryComparison g d b) at hn
    unfold HasCompletedReductionOrdinaryComparisonNormalization at hn
    have hh := hn M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 x
    simp only [map_one] at hh
    unfold completedReductionSectionEquation at hh ⊢
    exact hh
  · intro V x
    have hn := (completedReductionOrdinaryComparison_exists g d a).exists.choose_spec
    change HasCompletedReductionOrdinaryComparisonNormalization g d a
      (completedReductionOrdinaryComparison g d a) at hn
    unfold HasCompletedReductionOrdinaryComparisonNormalization at hn
    have hh := hn M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 x
    simp only [map_one] at hh
    unfold completedReductionSectionEquation at hh ⊢
    exact hh
  · intro V x
    have hn := (completedReductionOrdinaryTransition_exists g d a b h).exists.choose_spec
    change HasCompletedReductionOrdinaryTransitionNormalization g d a b h
      (completedReductionOrdinaryTransition g d a b h) at hn
    unfold HasCompletedReductionOrdinaryTransitionNormalization at hn
    simpa only [map_one] using hn M V ((proEtaleBaseChange g).obj V) (𝟙 _) 1 1 x

end AlgebraicGeometry.Scheme
