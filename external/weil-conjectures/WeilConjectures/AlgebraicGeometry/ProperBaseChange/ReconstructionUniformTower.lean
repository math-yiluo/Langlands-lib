/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.DeligneLaumon.SequentialDerivedInverseLimit
public import WeilConjectures.CategoryTheory.ProperBaseChange.SequentialTowerEvaluationFull
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
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
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.Right.RightFractionDenseSubcategory
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Reconstruction of a uniform local tower

The auxiliary constructions keep the actual inverse-image coefficients on local models.

## Main statements

- `uniformTowerRlim`: the actual total right derived inverse limit.
- `UniformLocalEquipment`: a coherent lift of the specified local level maps.
- `reconstructionUniformTower`: reconstruction with projections, completeness and naturality.

## References

* Stacks Tags 099M, 099L, 09C7, 09C0
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme

/-- Strict module towers are Grothendieck, retaining the small pro-etale site sizes. -/
@[instance] theorem uniformTowers_grothendieck (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    IsGrothendieckAbelian.{u + 1} (pbcTowers X R) := by
  let B := pbcModules X R
  have : IsGrothendieckAbelian.{u + 1} B :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology X) ((adicLisseForget X).obj R)
  let G := separator B
  have hG := isSeparator_separator B
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint B n).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight B n
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ B) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ B) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ B) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

variable {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- A retained witness of the definition's common window, stratification, covers and models. -/
structure UniformAdicTowerData (M : AdicTower X d)
    (strata : Stratification X) where
  lower : ℤ
  upper : ℤ
  bounds : lower ≤ upper
  cover : ∀ α : Fin strata.n, Sieve (⊤_ (strata.domain α).ProEt)
  covering : ∀ α : Fin strata.n,
    cover α ∈ ProEt.topology (strata.domain α) (⊤_ (strata.domain α).ProEt)
  model : ∀ (α : Fin strata.n) (U : (strata.domain α).ProEt)
    (f : U ⟶ ⊤_ (strata.domain α).ProEt), cover α f →
      AdicTowerLocalModel d (U.hom ≫ strata.immersion α) M lower upper

variable (Y : Scheme.{u})
  (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (R : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (π : (Functor.const ℕᵒᵖ).obj B ⟶ R)

/-- Ordinary quotient reduction with the integral coefficient action restored.
This applies also to the inverse-image coefficient diagram on a stratum cover. -/
def localReductionLevel (n : ℕ) : pbcModules Y B ⥤ pbcModules Y B :=
  pbcExtend (π.app (op n)) ⋙ pbcRestrict (π.app (op n))

attribute [local irreducible] completedAdicChangeData

private theorem tensorCast_smul
    {T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : B ⟶ T)
    (M : pbcModules Y B) (E : pbcModules Y T)
    (hE : E = SheafOfModules.changeOfRings c M)
    (V : Y.ProEtᵒᵖ) (b : T.obj.obj V) (x : M.val.obj V) :
    (eqToHom hE.symm).val.app V
        ((toSheafify (ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app V
            (b ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x)) =
      ((E.val.obj V).smul b).asHom.hom ((eqToHom hE.symm).val.app V
        ((toSheafify (ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app V
            ((1 : T.obj.obj V) ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x))) := by
  subst E
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((adicLisseForget Y).obj T).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M)
  change η.app V (b ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x) =
    b • η.app V ((1 : T.obj.obj V) ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x)
  convert (η.app V).hom.map_smul b
    ((1 : T.obj.obj V) ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x) using 1
  congr 1
  rw [ModuleCat.ExtendScalars.smul_tmul (c.hom.app V).hom, mul_one]

private theorem localTensorSection_smul
    {T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : B ⟶ T)
    (M : pbcModules Y B) (V : Y.ProEtᵒᵖ) (b : T.obj.obj V) (x : M.val.obj V) :
    pbcTensorSection c M V b x =
      ((((pbcExtend c).obj M).val.obj V).smul b).asHom.hom (pbcTensorSection c M V 1 x) := by
  dsimp only [pbcTensorSection, completedAdicChangeTensor, pbcExtend, completedAdicChange]
  exact tensorCast_smul Y B c M _ ((pbcExtensionExistence c).choose_spec.choose M) V b x

private theorem tensorCast_ext
    {T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : B ⟶ T)
    (M : pbcModules Y B) (E : pbcModules Y T)
    (hE : E = SheafOfModules.changeOfRings c M) (N : pbcModules Y B)
    (f g : (pbcRestrict c).obj E ⟶ N)
    (h : ∀ (V : Y.ProEtᵒᵖ) (b : T.obj.obj V) (x : M.val.obj V),
      f.val.app V ((eqToHom hE.symm).val.app V
        ((toSheafify (ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app V
            (b ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x))) =
      g.val.app V ((eqToHom hE.symm).val.app V
        ((toSheafify (ProEt.topology Y)
          (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app V
            (b ⊗ₜ[B.obj.obj V,(c.hom.app V).hom] x)))) : f = g := by
  subst E
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology Y) _ _ N.isSheaf
  ext V z
  induction z using TensorProduct.inductionOn with
  | tmul b x => exact h V b x
  | add z w hz hw =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hw

private theorem localTensorSection_ext
    {T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : B ⟶ T)
    (M : pbcModules Y B) (N : pbcModules Y B)
    (f g : (pbcRestrict c).obj ((pbcExtend c).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEtᵒᵖ) (b : T.obj.obj V) (x : M.val.obj V),
      f.val.app V (pbcTensorSection c M V b x) =
        g.val.app V (pbcTensorSection c M V b x)) : f = g := by
  dsimp only [pbcTensorSection, completedAdicChangeTensor] at h
  exact tensorCast_ext Y B c M _ ((pbcExtensionExistence c).choose_spec.choose M) N f g h

/-- The unique adjacent map is fixed by the sectionwise tensor formula. -/
theorem localReductionStep_exists (n : ℕ) :
    ∃! τ : localReductionLevel Y B R π (n + 1) ⟶ localReductionLevel Y B R π n,
      ∀ (M : pbcModules Y B) (V : Y.ProEtᵒᵖ)
        (b : (R.obj (op (n + 1))).obj.obj V) (x : M.val.obj V),
        (τ.app M).val.app V (pbcTensorSection (π.app (op (n + 1))) M V b x) =
          pbcTensorSection (π.app (op n)) M V
            ((R.map (homOfLE (Nat.le_succ n)).op).hom.app V b) x := by
  let c := π.app (op (n + 1))
  let a := π.app (op n)
  let q := R.map (homOfLE (Nat.le_succ n)).op
  have hc : c ≫ q = a := by
    simpa using (π.naturality (homOfLE (Nat.le_succ n)).op).symm
  let e := pbcRestrictComp c q a hc
  have he (M : pbcModules Y (R.obj (op n))) (V : Y.ProEtᵒᵖ)
      (x : M.val.obj V) : (e.hom.app M).val.app V x = x :=
    (pbcRestrictComp_exists c q a hc).exists.choose_spec M V x
  have hei (M : pbcModules Y (R.obj (op n))) (V : Y.ProEtᵒᵖ)
      (x : M.val.obj V) : (e.inv.app M).val.app V x = x := by
    have h := congrArg (fun f ↦ f.val.app V x) (e.inv_hom_id_app M)
    exact (he M V _).symm.trans h
  let k : 𝟭 (pbcModules Y B) ⟶ (pbcExtend a ⋙ pbcRestrict q) ⋙ pbcRestrict c :=
    (pbcScalarAdjunction a).unit ≫ Functor.whiskerLeft (pbcExtend a) e.inv
  let t : pbcExtend c ⟶ pbcExtend a ⋙ pbcRestrict q :=
    { app := fun M ↦ ((pbcScalarAdjunction c).homEquiv M _).symm (k.app M)
      naturality := by
        intro M N f
        apply ((pbcScalarAdjunction c).homEquiv _ _).injective
        rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
          Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
        exact k.naturality f }
  have ht : (pbcScalarAdjunction c).unit ≫ Functor.whiskerRight t (pbcRestrict c) = k := by
    apply NatTrans.ext
    funext M
    have h := ((pbcScalarAdjunction c).homEquiv M _).apply_symm_apply (k.app M)
    rw [Adjunction.homEquiv_unit] at h
    exact h
  let τ : localReductionLevel Y B R π (n + 1) ⟶ localReductionLevel Y B R π n :=
    Functor.whiskerRight t (pbcRestrict c) ≫ Functor.whiskerLeft (pbcExtend a) e.hom
  have ht_one (M : pbcModules Y B) (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
      (t.app M).val.app V (pbcTensorSection c M V 1 x) =
        pbcTensorSection a M V 1 x := by
    have h := congrArg (fun f ↦ (f.app M).val.app V x) ht
    change (t.app M).val.app V (((pbcScalarAdjunction c).unit.app M).val.app V x) =
      (e.inv.app _).val.app V (((pbcScalarAdjunction a).unit.app M).val.app V x) at h
    have uc : ((pbcScalarAdjunction c).unit.app M).val.app V x =
        pbcTensorSection c M V 1 x :=
      (pbcScalarAdjunction_exists c).exists.choose_spec M V x
    have ua : ((pbcScalarAdjunction a).unit.app M).val.app V x =
        pbcTensorSection a M V 1 x :=
      (pbcScalarAdjunction_exists a).exists.choose_spec M V x
    exact (congrArg ((t.app M).val.app V) uc).symm.trans
      (h.trans ((hei ((pbcExtend a).obj M) V _).trans ua))
  have hτ (M : pbcModules Y B) (V : Y.ProEtᵒᵖ)
      (b : (R.obj (op (n + 1))).obj.obj V) (x : M.val.obj V) :
      (τ.app M).val.app V (pbcTensorSection c M V b x) =
        pbcTensorSection a M V (q.hom.app V b) x := by
    change (e.hom.app _).val.app V
      ((t.app M).val.app V (pbcTensorSection c M V b x)) = _
    rw [he, localTensorSection_smul Y B c]
    change (t.app M).val.app V (b • pbcTensorSection c M V 1 x) = _
    rw [((t.app M).val.app V).hom.map_smul, ht_one]
    change (q.hom.app V b) • pbcTensorSection a M V 1 x = _
    exact (localTensorSection_smul Y B a M V (q.hom.app V b) x).symm
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  apply localTensorSection_ext Y B c M _
  intro V b x
  exact (hτ' M V b x).trans (hτ M V b x).symm

/-- Canonical adjacent quotient map. -/
def localReductionStep (n : ℕ) :
    localReductionLevel Y B R π (n + 1) ⟶ localReductionLevel Y B R π n :=
  (localReductionStep_exists Y B R π n).exists.choose

/-- The strict quotient tower of a module, with its actual adjacent transitions. -/
def localReductionModuleTower : pbcModules Y B ⥤ pbcTowers Y B :=
  (Functor.ofOpSequence (X := fun n : ℕ ↦ localReductionLevel Y B R π n)
    (fun n ↦ localReductionStep Y B R π n)).flip

/-- Tensor towers are additive. -/
@[instance] theorem localReductionModuleTower_additive :
    (localReductionModuleTower Y B R π).Additive := by
  have (n : ℕ) : (localReductionLevel Y B R π n).Additive := by
    dsimp only [localReductionLevel]
    infer_instance
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (localReductionLevel Y B R π n.unop).map_add

/-- A universal left derived pair for the strict reduction tower, retaining its
K-flat computation. The universal property fixes the pair up to unique compatible
isomorphism. Packaging the pair avoids repeatedly reducing nested existential choices. -/
structure LocalReductionDerivedData where
  functor : DerivedCategory (pbcModules Y B) ⥤ DerivedCategory (pbcTowers Y B)
  counit : DerivedCategory.Qh ⋙ functor ⟶
    (localReductionModuleTower Y B R π).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (pbcModules Y B) (.up ℤ))
  kFlat : ∀ P : CochainComplex (pbcModules Y B) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
      IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

private theorem derivedDataFromResolutions
    {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ (ℕᵒᵖ ⥤ A)) [F.Additive] (P : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (K' : CochainComplex A ℤ) (s : K' ⟶ K), P K' ∧ QuasiIso s)
    (hinv : ∀ (K K' : CochainComplex A ℤ) (s : K ⟶ K'),
      P K → P K' → QuasiIso s →
        QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s)) :
    ∃ (LF : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
      (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        ∀ K : CochainComplex A ℤ, P K →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory A (.up ℤ)) :=
    {K | ∃ K' : CochainComplex A ℤ, P K' ∧ (HomotopyCategory.quotient _ _).obj K' = K}
  have hr : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
    intro K
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨K', s, hK', hs⟩ := res K
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨K', hK', rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hi : ∀ K K' : HomotopyCategory A (.up ℤ), ∀ s : K ⟶ K',
      K ∈ S → K' ∈ S → HomotopyCategory.quasiIso _ _ s → IsIso (H.map s) := by
    intro K K' s hK hK' hs
    obtain ⟨K, hK, rfl⟩ := hK
    obtain ⟨K', hK', rfl⟩ := hK'
    obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have hs' := hinv K K' s hK hK'
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs)
    dsimp only [H, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hs'
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass _ _ H S hr hi
  exact ⟨LF, ε, hLF, fun K hK ↦ hε _ ⟨K, hK, rfl⟩⟩

/-- The local strict reduction tower has the universal left derived pair. -/
theorem localReductionDerived_exists : Nonempty (LocalReductionDerivedData Y B R π) := by
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨LF, ε, hLF, hε⟩ := derivedDataFromResolutions
    (localReductionModuleTower Y B R π)
    (CochainComplex.IsKFlatIndependentCoefficients (R := B))
    (ScalarReductionDerivedProof.kFlatResolutions
      (J := ProEt.topology Y) (O := B)) (by
      intro K K' s hK hK' hs
      apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      have he : QuasiIso
          (((pbcExtend (π.app n)).mapHomologicalComplex (.up ℤ)).map s) :=
        (pbcExtensionExistence (π.app n)).choose_spec.choose_spec.choose_spec.choose_spec.1
          s hK hK' hs
      change QuasiIso
        (((pbcRestrict (π.app n)).mapHomologicalComplex (.up ℤ)).map
          (((pbcExtend (π.app n)).mapHomologicalComplex (.up ℤ)).map s))
      exact HomologicalComplex.quasiIso_map_of_preservesHomology _ (pbcRestrict (π.app n)))
  exact ⟨⟨LF, ε, hLF, hε⟩⟩

/-- The universal derived pair, chosen only up to its unique compatible isomorphism. -/
def localReductionDerivedData : LocalReductionDerivedData Y B R π :=
  Classical.choice (localReductionDerived_exists Y B R π)

/-- The left derived strict local tensor tower, with the universal comparison retained. -/
def localReductionDerived :
    DerivedCategory (pbcModules Y B) ⥤ DerivedCategory (pbcTowers Y B) :=
  (localReductionDerivedData Y B R π).functor

/-- Its universal comparison on homotopy categories. -/
def localReductionCounit :
    DerivedCategory.Qh ⋙ localReductionDerived Y B R π ⟶
      (localReductionModuleTower Y B R π).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  (localReductionDerivedData Y B R π).counit

/-- The local universal comparison written on actual cochain representatives. -/
def localReductionComplexCounit (P : CochainComplex (pbcModules Y B) ℤ) :
    (localReductionDerived Y B R π).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((localReductionModuleTower Y B R π).mapHomologicalComplex (.up ℤ)).obj P) :=
  (CategoryTheory.derivedCochainCounit (localReductionModuleTower Y B R π)
    (localReductionDerived Y B R π) (localReductionCounit Y B R π)).app P

private theorem restrictionLocalization
    {C D : Type*} [Category C] [Category D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] (P : ObjectProperty C)
    (res : ∀ X : C, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  obtain ⟨_, F, hF, ⟨e⟩⟩ :=
    rightFractionDenseSubcategory W inferInstance P res L V.Q
  have : F.IsEquivalence := hF
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V e

private theorem comparisonOnResolvingClass
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hα : ∀ X : P.FullSubcategory, IsIso (α.app X.obj))
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! e : F ≅ G, ∀ X : P.FullSubcategory,
      e.hom.app (L.obj X.obj) ≫ γ.app X.obj = α.app X.obj := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  let τ : S ⋙ F ≅ S ⋙ G := NatIso.ofComponents
    (fun X ↦ asIso (α.app X.obj) ≪≫ (asIso (γ.app X.obj)).symm) (by
      intro X Y f
      change (L ⋙ F).map f.hom ≫ α.app Y.obj ≫ inv (γ.app Y.obj) =
        (α.app X.obj ≫ inv (γ.app X.obj)) ≫ (L ⋙ G).map f.hom
      rw [← Category.assoc, α.naturality, Category.assoc, Category.assoc]
      apply congrArg (α.app X.obj ≫ ·)
      apply (cancel_mono (γ.app Y.obj)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [γ.naturality f.hom]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp])
  let E' := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  have : E'.Full := Localization.full_whiskeringLeft S V E
  have : E'.Faithful := Localization.faithful_whiskeringLeft S V E
  let e : F ≅ G := E'.preimageIso τ
  have he (X : P.FullSubcategory) :
      e.hom.app (L.obj X.obj) = α.app X.obj ≫ inv (γ.app X.obj) := by
    exact congrArg (fun k ↦ k.app X) (E'.map_preimage τ.hom)
  refine ⟨e, ?_, ?_⟩
  · intro X
    rw [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro e' he'
    apply Iso.ext
    apply Localization.natTrans_ext S V
    intro X
    apply (cancel_mono (γ.app X.obj)).1
    change e'.hom.app (L.obj X.obj) ≫ γ.app X.obj =
      e.hom.app (L.obj X.obj) ≫ γ.app X.obj
    rw [he' X, he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem counitRepresentative
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) :
    G.mapDerivedCategory.map
        (LF.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors]
  erw [LF.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp,
    G.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id, Category.id_comp]
  erw [Category.comp_id]

private theorem whiskerCounit_isIso
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] (e : F ⋙ G ≅ H)
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : HomotopyCategory A (.up ℤ)) (h : IsIso (ε.app K)) :
    IsIso (G.mapDerivedCategory.map (ε.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K)) := by
  infer_instance

private def complexCounit
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (F : A ⥤ C) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) : LF.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  (CategoryTheory.derivedCochainCounit F LF ε).app K

private theorem complexCounit_formula
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (F : A ⥤ C) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) :
    complexCounit F LF ε K =
      LF.map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj K) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  simp only [complexCounit, CategoryTheory.derivedCochainCounit,
    CategoryTheory.derivedCochainComparisonFactors, NatTrans.comp_app,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

private def complexComparison
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [Abelian A] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) [F.Additive] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ D) [H.Additive] (e : F ⋙ G ≅ H)
    (LF : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) :
    G.mapDerivedCategory.obj (LF.obj (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj K)) :=
  G.mapDerivedCategory.map (complexCounit F LF ε K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj K))

private theorem complexComparison_homotopy
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [Abelian A] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) [F.Additive] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ D) [H.Additive] (e : F ⋙ G ≅ H)
    (LF : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) :
    complexComparison F G H e LF ε K =
      G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj K)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj K)) := by
  dsimp only [complexComparison]
  rw [complexCounit_formula, ← Category.assoc, counitRepresentative, Category.assoc]
  rfl

private theorem complexComparison_refl
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [Abelian A] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ C) [F.Additive] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex A ℤ) :
    complexComparison F G (F ⋙ G) (Iso.refl _) LF ε K =
      G.mapDerivedCategory.map (complexCounit F LF ε K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  dsimp only [complexComparison]
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  erw [DerivedCategory.Qh.map_id, Category.comp_id]

private theorem normalizedDerivedComparison
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (T : A ⥤ (ℕᵒᵖ ⥤ A)) [T.Additive]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (n : ℕ) (H : A ⥤ A) [H.Additive]
    (p : T ⋙ (CategoryTheory.evaluation ℕᵒᵖ A).obj (op n) ≅ H)
    (q : E ⋙ V ≅ H)
    (LT : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
    (LE : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LT ⟶
      T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : DerivedCategory.Qh ⋙ LE ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (K' : CochainComplex A ℤ) (s : K' ⟶ K), P K' ∧ QuasiIso s)
    (hε : ∀ K : CochainComplex A ℤ, P K →
      IsIso (ε.app ((HomotopyCategory.quotient _ _).obj K)))
    (hδ : ∀ K : CochainComplex A ℤ, P K →
      IsIso (δ.app ((HomotopyCategory.quotient _ _).obj K))) :
    ∃! e : LT ⋙ ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ≅
        LE ⋙ V.mapDerivedCategory,
      ∀ K : CochainComplex A ℤ, P K →
        e.hom.app (DerivedCategory.Q.obj K) ≫ complexComparison E V H q LE δ K =
          complexComparison T ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)) H p LT ε K := by
  let P' : ObjectProperty (HomotopyCategory A (.up ℤ)) :=
    fun K ↦ ∃ K' : CochainComplex A ℤ,
      P K' ∧ (HomotopyCategory.quotient _ _).obj K' = K
  have hres : ∀ K, ∃ (K' : P'.FullSubcategory) (s : K'.obj ⟶ K),
      HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro K
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨K', s, hK', hs⟩ := res K
    exact ⟨⟨_, ⟨K', hK', rfl⟩⟩, (HomotopyCategory.quotient _ _).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have : (P'.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P'.ι) :=
    restrictionLocalization _ DerivedCategory.Qh P' hres
  let F := LT ⋙ ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  let G := LE ⋙ V.mapDerivedCategory
  let R := H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let α : DerivedCategory.Qh ⋙ F ⟶ R :=
    Functor.whiskerRight ε ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ≫
      Functor.whiskerLeft (T.mapHomotopyCategory (.up ℤ))
        ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso p (.up ℤ)).hom
        DerivedCategory.Qh
  let γ : DerivedCategory.Qh ⋙ G ⟶ R :=
    Functor.whiskerRight δ V.mapDerivedCategory ≫
      Functor.whiskerLeft (E.mapHomotopyCategory (.up ℤ)) V.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso q (.up ℤ)).hom
        DerivedCategory.Qh
  have hα (K : P'.FullSubcategory) : IsIso (α.app K.obj) := by
    rcases K with ⟨K, hK⟩
    obtain ⟨K', hK', rfl⟩ := hK
    exact whiskerCounit_isIso T ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)) H p LT ε _
      (hε K' hK')
  have hγ (K : P'.FullSubcategory) : IsIso (γ.app K.obj) := by
    rcases K with ⟨K, hK⟩
    obtain ⟨K', hK', rfl⟩ := hK
    exact whiskerCounit_isIso E V H q LE δ _ (hδ K' hK')
  obtain ⟨e, he, hu⟩ := comparisonOnResolvingClass P' DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ _) F G R α γ hα hγ
  have hL (K : CochainComplex A ℤ) :
      complexComparison T ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)) H p LT ε K =
        α.app ((HomotopyCategory.quotient _ _).obj K) :=
    complexComparison_homotopy T ((CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)) H p LT ε K
  have hR (K : CochainComplex A ℤ) : complexComparison E V H q LE δ K =
      γ.app ((HomotopyCategory.quotient _ _).obj K) :=
    complexComparison_homotopy E V H q LE δ K
  refine ⟨e, ?_, ?_⟩
  · intro K hK
    exact (congrArg (e.hom.app (DerivedCategory.Q.obj K) ≫ ·) (hR K)).trans
      ((he ⟨_, ⟨K, hK, rfl⟩⟩).trans (hL K).symm)
  · intro e' he'
    apply hu e'
    intro K
    rcases K with ⟨K, hK⟩
    obtain ⟨K', hK', rfl⟩ := hK
    exact (congrArg (e'.hom.app (DerivedCategory.Q.obj K') ≫ ·) (hR K')).symm.trans
      ((he' K' hK').trans (hL K'))

/-- Evaluation of the local strict derived tower is exactly scalar reduction followed
by scalar restriction. Its isomorphism is fixed on every K-flat computation. -/
theorem localReductionEvaluation_exists (n : ℕ) :
    ∃! e : localReductionDerived Y B R π ⋙ pbcTowerEvaluation Y B n ≅
        pbcDerivedExtend (π.app (op n)) ⋙ pbcDerivedRestrict (π.app (op n)),
      ∀ P : CochainComplex (pbcModules Y B) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcDerivedRestrict (π.app (op n))).map (pbcComplexCounit (π.app (op n)) P) ≫
            (pbcRestrict (π.app (op n))).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (π.app (op n))).mapHomologicalComplex (.up ℤ)).obj P) =
          (pbcTowerEvaluation Y B n).map (localReductionComplexCounit Y B R π P) ≫
            (Functor.mapDerivedCategoryFactors
              ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y B)).obj (op n))).hom.app
                (((localReductionModuleTower Y B R π).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let E := pbcExtend (π.app (op n))
  let V := pbcRestrict (π.app (op n))
  let T := localReductionModuleTower Y B R π
  let Ev := (CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y B)).obj (op n)
  let p : T ⋙ Ev ≅ E ⋙ V := Iso.refl _
  obtain ⟨e, he, hu⟩ := normalizedDerivedComparison T E V n (E ⋙ V) p (Iso.refl _)
    (localReductionDerived Y B R π) (pbcDerivedExtend (π.app (op n)))
    (localReductionCounit Y B R π) (pbcExtensionCounit (π.app (op n)))
    (fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (R := B) K)
    (fun K ↦ ScalarReductionDerivedProof.kFlatResolutions K)
    (localReductionDerivedData Y B R π).kFlat
    (pbcExtensionCounit_isIso (π.app (op n)))
  have hcR (K : CochainComplex (pbcModules Y B) ℤ) :
      complexComparison E V (E ⋙ V) (Iso.refl _)
          (pbcDerivedExtend (π.app (op n))) (pbcExtensionCounit (π.app (op n))) K =
        (pbcDerivedRestrict (π.app (op n))).map (pbcComplexCounit (π.app (op n)) K) ≫
          V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [complexComparison_refl, complexCounit_formula]
    rfl
  have hcL (K : CochainComplex (pbcModules Y B) ℤ) :
      complexComparison T Ev (E ⋙ V) p
          (localReductionDerived Y B R π) (localReductionCounit Y B R π) K =
        (pbcTowerEvaluation Y B n).map (localReductionComplexCounit Y B R π K) ≫
          Ev.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj K) := by
    exact complexComparison_refl T Ev (localReductionDerived Y B R π)
      (localReductionCounit Y B R π) K
  refine ⟨e, ?_, ?_⟩
  · intro K hK
    exact (congrArg (e.hom.app (DerivedCategory.Q.obj K) ≫ ·) (hcR K)).symm.trans
      ((he K hK).trans (hcL K))
  · intro e' he'
    apply hu e'
    intro K hK
    exact (congrArg (e'.hom.app (DerivedCategory.Q.obj K) ≫ ·) (hcR K)).trans
      ((he' K hK).trans (hcL K).symm)

/-- The uniquely normalized evaluation comparison. -/
def localReductionEvaluation (n : ℕ) :
    localReductionDerived Y B R π ⋙ pbcTowerEvaluation Y B n ≅
      pbcDerivedExtend (π.app (op n)) ⋙ pbcDerivedRestrict (π.app (op n)) :=
  (localReductionEvaluation_exists Y B R π n).exists.choose

/-- Actual inverse limit of strict towers. -/
abbrev uniformTowerLimit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcTowers X R ⥤ pbcModules X R := lim

/-- Inverse limit is additive. -/
@[instance] theorem uniformTowerLimit_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (uniformTowerLimit X R).Additive := by
  constructor
  intro M N f g
  apply limit.hom_ext
  intro n
  simp [uniformTowerLimit, Preadditive.add_comp, Preadditive.comp_add]

/-- Total right derived inverse limit, computed by K-injective tower resolutions. -/
def uniformTowerRlim (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    DerivedCategory (pbcTowers X R) ⥤ DerivedCategory (pbcModules X R) :=
  (uniformTowerLimit X R).rightDerivedFunctor

/-- The exact constant tower functor. -/
abbrev uniformConstantTower (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcTowers X R := Functor.const ℕᵒᵖ

/-- Constants are additive. -/
@[instance] theorem uniformConstantTower_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (uniformConstantTower X R).Additive := by
  constructor
  intro M N f g
  rfl

/-- The canonical derived constant/limit adjunction. -/
def uniformTowerAdjunction (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (uniformConstantTower X R).mapDerivedCategory ⊣ uniformTowerRlim X R :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (constLimAdj : uniformConstantTower X R ⊣ uniformTowerLimit X R)

/-- Evaluation of a derived constant tower is canonically the original object. -/
def uniformConstantEvaluation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :
    (uniformConstantTower X R).mapDerivedCategory ⋙ pbcTowerEvaluation X R n ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryCompIso (uniformConstantTower X R)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).obj (op n)) ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The canonical derived-limit projection, evaluated from the adjunction counit. -/
def uniformTowerProjection (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : DerivedCategory (pbcTowers X R)) (n : ℕ) :
    (uniformTowerRlim X R).obj M ⟶ (pbcTowerEvaluation X R n).obj M :=
  (uniformConstantEvaluation X R n).inv.app ((uniformTowerRlim X R).obj M) ≫
    (pbcTowerEvaluation X R n).map ((uniformTowerAdjunction X R).counit.app M)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The inverse-image coefficient diagram on a stratum cover. -/
abbrev uniformLocalRings := pbcAdicRings X d ⋙ adicTowerInverseImage g

/-- The actual restricted completed ring, without recompleting it. -/
abbrev uniformLocalRing := (adicTowerInverseImage g).obj (pbcAdicCompletion X d)

/-- Inverse images of the global projections form a natural cone. -/
theorem uniformLocalProjections_naturality (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj (uniformLocalRing g d)).map f ≫
        (adicTowerInverseImage g).map (pbcAdicProjection X d j.unop) =
      (adicTowerInverseImage g).map (pbcAdicProjection X d i.unop) ≫
        (uniformLocalRings g d).map f := by
  change 𝟙 ((adicTowerInverseImage g).obj (limit (pbcAdicRings X d))) ≫
      (adicTowerInverseImage g).map (limit.π (pbcAdicRings X d) j) =
    (adicTowerInverseImage g).map (limit.π (pbcAdicRings X d) i) ≫
      (adicTowerInverseImage g).map ((pbcAdicRings X d).map f)
  rw [Category.id_comp, ← Functor.map_comp]
  exact congrArg (adicTowerInverseImage g).map (limit.w (pbcAdicRings X d) f).symm

/-- Restricted limit projections, with their actual mapped projections as components. -/
def uniformLocalProjections :
    (Functor.const ℕᵒᵖ).obj (uniformLocalRing g d) ⟶ uniformLocalRings g d where
  app n := (adicTowerInverseImage g).map (pbcAdicProjection X d n.unop)
  naturality := uniformLocalProjections_naturality g d

/-- Apply exact inverse image to strict towers before derived localization. -/
abbrev uniformModuleTowerPull :=
  (Functor.whiskeringRight ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))
    (pbcModules Y (uniformLocalRing g d))).obj
      (proEtaleRingModulePullback g (pbcAdicCompletion X d)
        (uniformLocalRing g d) (Iso.refl _))

/-- Strict-tower inverse image preserves finite limits, computed at each level. -/
@[instance] theorem uniformModuleTowerPull_preservesFiniteLimits :
    PreservesFiniteLimits (uniformModuleTowerPull g d) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro n
  change PreservesLimitsOfShape J
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj n ⋙
      proEtaleRingModulePullback g (pbcAdicCompletion X d) (uniformLocalRing g d)
        (Iso.refl _))
  infer_instance

/-- Strict-tower inverse image preserves finite colimits, computed at each level. -/
@[instance] theorem uniformModuleTowerPull_preservesFiniteColimits :
    PreservesFiniteColimits (uniformModuleTowerPull g d) := by
  constructor
  intro J _ _
  apply preservesColimitsOfShape_of_evaluation
  intro n
  change PreservesColimitsOfShape J
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj n ⋙
      proEtaleRingModulePullback g (pbcAdicCompletion X d) (uniformLocalRing g d)
        (Iso.refl _))
  infer_instance

/-- Derived exact restriction of strict towers. -/
def uniformTowerPull :
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcTowers Y (uniformLocalRing g d)) :=
  (uniformModuleTowerPull g d).mapDerivedCategory

/-- Exact evaluation and exact inverse image commute canonically. -/
def uniformPullEvaluation (n : ℕ) :
    uniformTowerPull g d ⋙ pbcTowerEvaluation Y (uniformLocalRing g d) n ≅
      pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙
        adicTowerPullback g (pbcAdicCompletion X d) :=
  Functor.mapDerivedCategoryCompIso (uniformModuleTowerPull g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (uniformLocalRing g d))).obj (op n)) ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIso
      ((CategoryTheory.evaluation ℕᵒᵖ
        (pbcModules X (pbcAdicCompletion X d))).obj (op n))
      (proEtaleRingModulePullback g (pbcAdicCompletion X d)
        (uniformLocalRing g d) (Iso.refl _))).symm

/-- The canonical strict reduction tower of a local complex. -/
def uniformLocalTower (L : CochainComplex (pbcModules Y (uniformLocalRing g d)) ℤ) :
    DerivedCategory (pbcTowers Y (uniformLocalRing g d)) :=
  (localReductionDerived Y (uniformLocalRing g d) (uniformLocalRings g d)
    (uniformLocalProjections g d)).obj (DerivedCategory.Q.obj L)

/-- The canonical scalar unit, read as a map to each evaluation of the strict local tower. -/
def uniformLocalUnit (L : CochainComplex (pbcModules Y (uniformLocalRing g d)) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj L ⟶
      (pbcTowerEvaluation Y (uniformLocalRing g d) n).obj (uniformLocalTower g d L) :=
  (pbcDerivedScalarAdjunction ((uniformLocalProjections g d).app (op n))).unit.app
      (DerivedCategory.Q.obj L) ≫
    (localReductionEvaluation Y (uniformLocalRing g d) (uniformLocalRings g d)
      (uniformLocalProjections g d) n).inv.app (DerivedCategory.Q.obj L)

/-- The specified level map from restricted evaluation to the local reduction tower.
It uses the given e_n and the canonical evaluation and scalar-restriction comparisons. -/
def uniformLocalLevel (M : AdicTower X d) {a b : ℤ}
    (L : AdicTowerLocalModel d g M a b) (n : ℕ) :
    (pbcTowerEvaluation Y (uniformLocalRing g d) n).obj ((uniformTowerPull g d).obj M.tower) ⟶
      (pbcTowerEvaluation Y (uniformLocalRing g d) n).obj
        (uniformLocalTower g d L.complex) :=
  (uniformPullEvaluation g d n).hom.app M.tower ≫
    (adicTowerPullback g (pbcAdicCompletion X d)).map (M.evaluation n).inv ≫
    (proEtaleRingRestrictionDerivedPullback g
      (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
      (uniformLocalRing g d) ((uniformLocalRings g d).obj (op n))
      (pbcAdicProjection X d n) ((uniformLocalProjections g d).app (op n))
      (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app (M.level n) ≫
    (pbcDerivedRestrict ((uniformLocalProjections g d).app (op n))).map
      (L.identification n).hom ≫
    (localReductionEvaluation Y (uniformLocalRing g d) (uniformLocalRings g d)
      (uniformLocalProjections g d) n).inv.app (DerivedCategory.Q.obj L.complex)

/-- Equipment is a coherent derived-tower isomorphism lifting precisely the specified e_n.
No choice or uniqueness of such a lift is built into this definition. -/
structure UniformLocalEquipment (M : AdicTower X d) {a b : ℤ}
    (L : AdicTowerLocalModel d g M a b) where
  comparison : (uniformTowerPull g d).obj M.tower ≅ uniformLocalTower g d L.complex
  evaluation : ∀ n : ℕ,
    (pbcTowerEvaluation Y (uniformLocalRing g d) n).map comparison.hom =
      uniformLocalLevel g d M L n

/-- The canonical quotient-linear counit, adjoint to the actual global limit projection. -/
def uniformReconstructionCounit (M : AdicTower X d) (n : ℕ) :
    (pbcDerivedExtend (pbcAdicProjection X d n)).obj
      ((uniformTowerRlim X (pbcAdicCompletion X d)).obj M.tower) ⟶ M.level n :=
  ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).homEquiv _ _).symm
    (uniformTowerProjection X (pbcAdicCompletion X d) M.tower n ≫ (M.evaluation n).inv)

/-- The actual reconstructed object, rather than an independent limit variable. -/
def uniformReconstructionLimit (M : AdicTower X d) :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (uniformTowerRlim X (pbcAdicCompletion X d)).obj M.tower

/-- The type of local isomorphism families indexed by coherent equipment, with every
local model of a retained uniform presentation on the given finite stratification. -/
abbrev UniformReconstructionFamily (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : Stratification X) :=
  ∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
    (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
    (hf : W.cover α f)
    (_E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)),
    DerivedCategory.Q.obj (W.model α U f hf).complex ≅
      (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).obj
        (uniformReconstructionLimit d M)

/-- Uniform reconstruction, including the actual projections, quotient-linear counits,
normalization, cohomological window, and naturality for equipped models.
-/
theorem reconstructionUniformTower {k : Type u} [Field k] (X : Scheme.{u})
    (fX : X ⟶ Spec (.of k)) (_hX : LocallyOfFiniteType fX ∧ QuasiCompact fX)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : Stratification X) :
    ∃ φ : UniformReconstructionFamily X d S,
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S)
        (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : W.cover α f),
        Nonempty (UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf)) ∧
          ∀ E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf),
            ∀ n : ℕ,
              (φ M W α U f hf E).hom ≫
                  CategoryTheory.Functor.map
                    (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d))
                    (uniformTowerProjection X (pbcAdicCompletion X d) M.tower n) ≫
                  (uniformPullEvaluation (U.hom ≫ S.immersion α) d n).inv.app M.tower =
                uniformLocalUnit (U.hom ≫ S.immersion α) d (W.model α U f hf).complex n ≫
                  (pbcTowerEvaluation U.left
                    (uniformLocalRing (U.hom ≫ S.immersion α) d) n).map E.comparison.inv) ∧
      (∀ (M : AdicTower X d) (W : UniformAdicTowerData d M S),
        (∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
          (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
          (e : DerivedCategory.Q.obj C ≅ uniformReconstructionLimit d M),
          IsDerivedCompleteIntrinsic X d r a ha (uniformReconstructionLimit d M) C e) ∧
        (∀ n : ℕ, IsIso (uniformReconstructionCounit d M n)) ∧
        (∀ (b a : ℕ) (hab : a ≤ b),
          (pbcDerivedExtend (pbcAdicQuotient X d b a hab)).map
              (uniformReconstructionCounit d M b) ≫ (M.normalization b a hab).hom =
            (pbcReductionNormalization (pbcAdicProjection X d b)
              (pbcAdicQuotient X d b a hab) (pbcAdicProjection X d a)
              (pbcAdicProjection_comp X d b a hab)
              (uniformReconstructionLimit d M)).hom ≫ uniformReconstructionCounit d M a) ∧
        ∀ q : ℤ, q < W.lower ∨ W.upper < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj (uniformReconstructionLimit d M))) ∧
      (∀ (M N : AdicTower X d) (W : UniformAdicTowerData d M S)
        (V : UniformAdicTowerData d N S) (α : Fin S.n) (U : (S.domain α).ProEt)
        (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : W.cover α f) (hf' : V.cover α f)
        (E : UniformLocalEquipment (U.hom ≫ S.immersion α) d M (W.model α U f hf))
        (E' : UniformLocalEquipment (U.hom ≫ S.immersion α) d N (V.model α U f hf'))
        (v : M.tower ⟶ N.tower)
        (h : DerivedCategory.Q.obj (W.model α U f hf).complex ⟶
          DerivedCategory.Q.obj (V.model α U f hf').complex),
        (uniformTowerPull (U.hom ≫ S.immersion α) d).map v ≫ E'.comparison.hom =
          E.comparison.hom ≫
            (localReductionDerived U.left (uniformLocalRing (U.hom ≫ S.immersion α) d)
              (uniformLocalRings (U.hom ≫ S.immersion α) d)
              (uniformLocalProjections (U.hom ≫ S.immersion α) d)).map h →
        h ≫ (φ N V α U f hf' E').hom = (φ M W α U f hf E).hom ≫
          (adicTowerPullback (U.hom ≫ S.immersion α) (pbcAdicCompletion X d)).map
            ((uniformTowerRlim X (pbcAdicCompletion X d)).map v)) := by
  sorry

end AlgebraicGeometry.Scheme
