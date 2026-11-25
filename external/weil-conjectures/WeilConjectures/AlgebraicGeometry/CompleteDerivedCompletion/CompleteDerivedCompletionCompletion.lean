/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionDefs
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionLimit
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Center.Linear
import WeilConjectures.Algebra.Homology.ScalarTowerProductFibre
import Mathlib.CategoryTheory.Conj
import all WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import all WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import all WeilConjectures.SixFunctors.ProEtale.InternalQuotientPrincipalConeComparison
import WeilConjectures.SixFunctors.ProEtale.InternalRoosOutputComplete
import WeilConjectures.Algebra.Homology.SixFunctors.TermwiseConeHomotopyExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare

/-!
# Towers and the derived completion: reduction tower and completion

The derived reduction tower is triangulated and its evaluations are the finite reductions;
bounded finite-free tensor commutes with the derived limit; the completion is derived
complete, the completion unit `kappa` becomes invertible after every finite reduction, and
its invertibility characterizes derived completeness; the completion is computed by the
Roos model of any K-flat representative.
Source: blueprint Assertions 5--6 (blueprint: proposition-proper-base-change-complete-integral).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

attribute [local instance] AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified right derived inverse limit has the normalized strict Roos model.
Source: blueprint Notation 1, Stacks Tag 0941
(blueprint: det-pbc-complete-derived-completion).
Proof: use the exact-products comparison for the integral module category. Its
comparison with ordinary inverse limit is invertible on K-injective towers by the
construction of the total right derived functor. Reverse the resulting comparison. -/
theorem roosComparison (T : Scheme.{u}) :
    Nonempty (DerivedCategory.Q ⋙ rlim l E T ≅ ExactProductsRoos.fibre ⋙ DerivedCategory.Q) := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  obtain ⟨e, _⟩ := ExactProductsRoos.comparisonIso (rlim l E T)
    (show (inverseLimit l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ rlim l E T from
      { app := (inverseLimit l E T).rightDerivedFunctorUnitQ
        naturality _ _ a := (inverseLimit l E T).rightDerivedFunctorUnitQ_naturality a })
    (fun I hI ↦ by
      let := hI
      change IsIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I)
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance)
  exact ⟨e.symm⟩

/-- The constant-tower functor on derived categories is fully faithful, so the
canonical constant-limit unit is invertible.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: evaluation at the terminal level is exact and left adjoint to the constant
functor. Derive this adjunction. The composite constant then evaluation is the identity,
so the derived constant functor is fully faithful. The unit of any adjunction with
fully faithful left adjoint is invertible, in particular the specified limit adjunction. -/
theorem constantLimitUnit_isIso (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsIso ((constantLimitAdjunction l E T).unit.app M) := by
  let a := (UnboundedExactTower.evaluationZeroConstAdjunction
    (AdicCompletion.Modules l E T)).mapDerivedCategoryRightDerivedAdjunction
    |>.ofNatIsoRight (constant l E T).rightDerivedFunctorIsoMapDerivedCategory
  let e : dconstant l E T ⋙ dev l E T 0 ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso (constant l E T) (ev l E T 0) ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.constCompEvaluationObj (C := ℕᵒᵖ)
          (D := AdicCompletion.Modules l E T) (op 0)) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let h := a.fullyFaithfulROfCompIsoId e
  let := h.full
  let := h.faithful
  infer_instance

/-- Scalar powers are respected by the induced action on every integral module.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: the scalar action is the composite of pullback, conjugation by the regular-module
comparison, tensoring on the left, and conjugation by the left unitor. Each is a monoid
homomorphism on endomorphisms, so their composite preserves powers. -/
theorem scalarOnModules_pow (T : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (k : ℕ) :
    DerivedNakayama.scalarOnModules l E T (d ^ k) =
      ((End.of (DerivedNakayama.scalarOnModules l E T d)) ^ k).asHom := by
  let A := AdicCompletion.Modules l E T
  let F₁ := (DerivedNakayama.pullback l E T).mapEnd
    (Mod.regular (DerivedNakayama.integerRing l E))
  let F₂ := (DerivedNakayama.regularPullbackIso l E T).conj.toMonoidHom
  let F₃ := (tensoringLeft A).mapEnd (𝟙_ A)
  let F₄ := (leftUnitorNatIso A).conj.toMonoidHom
  exact congrArg End.asHom ((F₄.comp (F₃.comp (F₂.comp F₁))).map_pow d k)

/-- The derived reduction tower is triangulated with its totalization shift.
Source: blueprint Notation 3 and Assertion 6
(blueprint: proposition-proper-base-change-complete-integral).
Proof: the strict functor is the cone of a termwise natural transformation between
additive functors. Its two-column totalization is exact on homotopy categories.
The factorization through complexes agrees with the specified localized functor.
Fully faithful precomposition with the homotopy quotient gives the comparison on
homotopy categories. Transport its shift through localization and descend exactness
using the essential surjectivity of localization on arrows. -/
theorem red_triangulated (T : Scheme.{u}) :
    ∃ (_shift : (red l E T).CommShift ℤ), (red l E T).IsTriangulated := by
  let A := AdicCompletion.Modules l E T
  let B := Tow l E T
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  obtain ⟨H, eH, cH, hH⟩ := CochainComplex.termwiseCone_homotopy_exact
    (scalarTower l E T) (constant l E T) (powerMap l E T)
  let := cH
  let := hH
  let eC : qA ⋙ (DerivedCategory.Qh ⋙ red l E T) ≅
      qA ⋙ (H ⋙ DerivedCategory.Qh) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (red l E T) ≪≫
      redFactors l E T ≪≫
      Functor.isoWhiskerRight (eqToIso (show strictRed l E T =
        CochainComplex.termwiseCone (scalarTower l E T) (constant l E T)
          (powerMap l E T) from rfl)) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eH.symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let e : DerivedCategory.Qh ⋙ red l E T ≅ H ⋙ DerivedCategory.Qh :=
    (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj qA)).preimageIso eC
  let : Localization.Lifting (DerivedCategory.Qh (C := A))
      (HomotopyCategory.quasiIso A (.up ℤ)) (H ⋙ DerivedCategory.Qh) (red l E T) := ⟨e⟩
  let c := Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ)) ℤ (H ⋙ DerivedCategory.Qh) (red l E T)
  let := c
  have := Localization.essSurj_mapArrow (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (.up ℤ))
  have : NatTrans.CommShift e.hom ℤ := by
    change NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) (H ⋙ DerivedCategory.Qh) (red l E T)).hom ℤ
    infer_instance
  exact ⟨c, Functor.isTriangulated_of_precomp_iso e⟩

private theorem tower_flat_of_levelwise (T : Scheme.{u}) (X : Tow l E T)
    (hX : ∀ n : ℕᵒᵖ, ObjectProperty.flat (X.obj n)) : ObjectProperty.flat X := by
  constructor <;> constructor
  · apply preservesFiniteLimits_of_evaluation
    intro n
    let := (hX n).tensorLeft.preservesFiniteLimits
    exact inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorLeft (X.obj n)))
  · apply preservesFiniteColimits_of_evaluation
    intro n
    let := (hX n).tensorLeft.preservesFiniteColimits
    exact inferInstanceAs (PreservesFiniteColimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorLeft (X.obj n)))
  · apply preservesFiniteLimits_of_evaluation
    intro n
    let := (hX n).tensorRight.preservesFiniteLimits
    exact inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorRight (X.obj n)))
  · apply preservesFiniteColimits_of_evaluation
    intro n
    let := (hX n).tensorRight.preservesFiniteColimits
    exact inferInstanceAs (PreservesFiniteColimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorRight (X.obj n)))

private theorem tower_functorialFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Tow l E T) := by
  let A := AdicCompletion.Modules l E T
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some
  let F₀ := (Functor.whiskeringRight ℕᵒᵖ A A).obj (Λ.F ⋙ ObjectProperty.flat.ι)
  let F := ObjectProperty.lift ObjectProperty.flat F₀
    (fun X ↦ tower_flat_of_levelwise l E T (F₀.obj X)
      (fun n ↦ (Λ.F.obj (X.obj n)).property))
  let π : F ⋙ ObjectProperty.flat.ι ⟶ 𝟭 (Tow l E T) :=
    { app X :=
        { app n := Λ.π.app (X.obj n)
          naturality _ _ t := Λ.π.naturality (X.map t) }
      naturality _ _ f := by
        apply NatTrans.ext
        funext n
        exact Λ.π.naturality (f.app n) }
  refine ⟨{ F := F, π := π, epi_π_app := ?_ }⟩
  intro X
  have (n : ℕᵒᵖ) : Epi ((π.app X).app n) := Λ.epi_π_app (X.obj n)
  exact NatTrans.epi_of_epi_app _

private noncomputable instance towerClosed (T : Scheme.{u}) :
    MonoidalClosed (Tow l E T) :=
  Functor.functorCategoryMonoidalClosed ℕᵒᵖ (AdicCompletion.Modules l E T)

private instance towerFunctorialFlat (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Tow l E T) := tower_functorialFlatResolution l E T

private noncomputable instance constantMonoidal (T : Scheme.{u}) :
    (constant l E T).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)
      μIso_hom_natural_left := by intros; ext n; simp
      μIso_hom_natural_right := by intros; ext n; simp
      associativity := by intros; ext n; simp
      left_unitality := by
        intro X
        apply NatTrans.ext
        funext n
        change (λ_ X).hom = (𝟙 _ ▷ X) ≫ 𝟙 _ ≫ (λ_ X).hom
        simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
      right_unitality := by
        intro X
        apply NatTrans.ext
        funext n
        change (ρ_ X).hom = (X ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ X).hom
        simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp] }

private instance constantPreservesFlat (T : Scheme.{u}) :
    (constant l E T).PreservesFlat where
  flat_obj hX := tower_flat_of_levelwise l E T _ (fun _ ↦ hX)

private theorem finiteFree_dualizable (T : Scheme.{u})
    (M : AdicCompletion.Modules l E T) (hM : Mod.IsFree (AdicCompletion.ring l E T) M) :
    IsDualizable M := by
  obtain ⟨r, ⟨e⟩⟩ := hM
  exact IsDualizable.of_iso e.symm (isDualizable_biproduct_unit r)

private theorem constantComplex_kFlat (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ)).kFlat
      (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨a, b, ha, hb⟩ := hb
  let := ha
  let := hb
  apply CochainComplex.kFlat_of_bounded_of_flat _ a b
  intro j
  exact tower_flat_of_levelwise l E T _ (fun _ ↦ (finiteFree_dualizable l E T _ (hf j)).flat)

private theorem tensorTower_realization (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    Nonempty (tensorTower l E T P hb hf ≅
      tensorRight ((dconstant l E T).obj (DerivedCategory.Q.obj P))) := by
  let B := Tow l E T
  let C := ((constant l E T).mapHomologicalComplex (.up ℤ)).obj P
  let Ck : CochainComplex.KFlat B := ⟨C, constantComplex_kFlat l E T P hb hf⟩
  let L := DerivedCategory.TensorCommShift₂.L B
  let eL := DerivedCategory.quotientCompQhIso B
  let e : DerivedCategory.Q ⋙ tensorRight (DerivedCategory.Q.obj C) ≅
      strictTensor l E T P ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q
      ((curriedTensor (DerivedCategory B)).flip.mapIso (eL.app C).symm) ≪≫
      Functor.isoWhiskerRight eL.symm (tensorRight (L.obj C)) ≪≫
      asIso (DerivedCategory.TensorCommShift₂.tensorRightLift Ck) ≪≫
      Functor.isoWhiskerLeft (strictTensor l E T P) eL
  let r : tensorTower l E T P hb hf ≅ tensorRight (DerivedCategory.Q.obj C) :=
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso B (.up ℤ)) (DerivedCategory B)).preimageIso
        (Localization.fac (strictTensor l E T P ⋙ DerivedCategory.Q)
          (strictTensor_inverts l E T P hb hf) DerivedCategory.Q ≪≫ e.symm)
  exact ⟨r ≪≫ (curriedTensor (DerivedCategory B)).flip.mapIso
    ((constant l E T).mapDerivedCategoryFactors.app P).symm⟩

/-- Bounded finite-free tensor commutes naturally with derived inverse limit.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: form functorial flat covers of towers levelwise, so the pointwise monoidal
structure has its derived tensor. The exact constant tower functor is strong monoidal
on derived categories. A bounded finite-free complex is dualizable. The projection
formula for its constant/limit adjunction is therefore an isomorphism. The K-flat
comparison identifies derived tensor by its constant tower with the specified
localized strict total tensor, giving the asserted natural comparison. -/
theorem tensorLimitIso (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    Nonempty (rlim l E T ⋙
        (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) T).flip.obj
          (DerivedCategory.Q.obj P) ≅
      tensorTower l E T P hb hf ⋙ rlim l E T) := by
  let F := constant l E T
  let : F.IsLeftAdjoint := (constLimAdj : F ⊣ inverseLimit l E T).isLeftAdjoint
  let : F.mapDerivedCategory.OplaxMonoidal := F.mapDerivedCategoryOplaxMonoidal
  have : IsIso (Functor.OplaxMonoidal.η F.mapDerivedCategory) :=
    F.isIso_mapDerivedCategoryOplaxMonoidal_η
  have (X Y : DerivedCategory (AdicCompletion.Modules l E T)) :
      IsIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory X Y) := by
    rw [F.mapDerivedCategoryOplaxMonoidal_δ]
    infer_instance
  let := Functor.Monoidal.ofOplaxMonoidal F.mapDerivedCategory
  let : SymmetricCategory (DerivedCategory (AdicCompletion.Modules l E T)) :=
    DerivedCategory.symmetricCategory _
  have hbounded := hb
  obtain ⟨a, b, ha, hb'⟩ := hbounded
  let := ha
  let := hb'
  have hP := DerivedCategory.isDualizable_Q_obj P a b
    (fun j ↦ finiteFree_dualizable l E T _ (hf j))
  let φ := F.mapDerivedCategoryTensorComparison
  let π := (constantLimitAdjunction l E T).rightAdjointProjectionMap φ
  let p : rlim l E T ⋙ tensorRight (DerivedCategory.Q.obj P) ⟶
      tensorRight ((dconstant l E T).obj (DerivedCategory.Q.obj P)) ⋙ rlim l E T :=
    { app X := (π.app X).app (DerivedCategory.Q.obj P)
      naturality _ _ f := NatTrans.congr_app (π.naturality f) (DerivedCategory.Q.obj P) }
  have (X : DTow l E T) : IsIso (p.app X) :=
    (constantLimitAdjunction l E T).isIso_rightAdjointProjectionMap_app_app_of_isDualizable
      φ (fun _ _ ↦ rfl) X hP
  have : IsIso p := NatIso.isIso_of_isIso_app p
  obtain ⟨r⟩ := tensorTower_realization l E T P hb hf
  exact ⟨asIso p ≪≫ Functor.isoWhiskerRight r.symm (rlim l E T)⟩

/-- The finite scalar tensor functor is the restricted derived reduction.
Source: blueprint Assertion 5 and the normalized internal K-flat scalar comparison
(blueprint: proposition-proper-base-change-complete-integral).
Proof: the pulled-back finite coefficient module is the regular quotient module with
scalars restricted. Apply the natural K-flat scalar-tower realization; its canonical
unit and transition equations imply, in particular, the asserted natural isomorphism. -/
theorem finiteScalarComparison (T : Scheme.{u}) (n : ℕ) :
    Nonempty (DerivedNakayama.reductionFunctor l E T (n + 1) ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n) := by
  obtain ⟨e, _, _⟩ := Mod.KFlatScalarTower.derived_realization
    (AdicCompletion.ring l E T) (AdicCompletion.finiteRing l E T)
    (AdicCompletion.quotient l E T) (AdicCompletion.transition l E T)
    (AdicCompletion.quotient_transition l E T) (AdicCompletion.finiteModule l E T)
    (AdicCompletion.finiteUnit l E T)
    (fun n ↦ (DerivedNakayama.pullback l E T).map (AdicCompletion.quotientStep l E n))
    (AdicCompletion.finiteModuleIso l E T)
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint T).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint T).map (AdicCompletion.transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint T).map (AdicCompletion.transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id])
  exact ⟨e n⟩

private theorem evaluatedPowerMap (T : Scheme.{u}) (n : ℕ) :
    Functor.whiskerRight (complexPowerMap l E T) ((ev l E T n).mapHomologicalComplex (.up ℤ)) =
      NatTrans.mapHomologicalComplex
        (DerivedNakayama.scalarOnModules l E T (uniformizer l E ^ (n + 1))) (.up ℤ) := by
  rw [scalarOnModules_pow]
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.Hom.ext
  funext j
  exact congrArg End.asHom
    ((((evaluation _ _).obj (P.X j)).mapEnd (𝟭 (AdicCompletion.Modules l E T))).map_pow
      (End.of (scalar l E T)) (n + 1)).symm

private abbrev principalScalar (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) : End P :=
  End.of (DerivedNakayama.scalarOnComplex l E T (uniformizer l E) P)

private theorem scalarOnComplex_pow (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (k : ℕ) :
    DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ k) P =
      (principalScalar l E T P ^ k).asHom := by
  apply HomologicalComplex.Hom.ext
  funext j
  change (DerivedNakayama.scalarOnModules l E T (uniformizer l E ^ k)).app (P.X j) = _
  rw [scalarOnModules_pow]
  have h₁ := (((evaluation (AdicCompletion.Modules l E T)
    (AdicCompletion.Modules l E T)).obj (P.X j)).mapEnd
      (𝟭 (AdicCompletion.Modules l E T))).map_pow (End.of (scalar l E T)) k
  have h₂ := ((HomologicalComplex.eval (AdicCompletion.Modules l E T) (.up ℤ) j).mapEnd P).map_pow
    (principalScalar l E T P) k
  exact congrArg End.asHom (h₁.trans h₂.symm)

private theorem power_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    ((ev l E T n).mapHomologicalComplex (.up ℤ)).map ((complexPowerMap l E T).app P) =
      (principalScalar l E T P ^ (n + 1)).asHom := by
  apply HomologicalComplex.Hom.ext
  funext j
  exact congrArg End.asHom
    (((HomologicalComplex.eval (AdicCompletion.Modules l E T) (.up ℤ) j).mapEnd P).map_pow
      (principalScalar l E T P) (n + 1)).symm

private theorem principal_levelConeTowerIso_app
    {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : K ⟶ L) (n : ℕ) :
    (levelConeTowerIso
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).app (op n) =
        CochainComplex.mappingCone.mapHomologicalComplexIso f
          ((evaluation ℕᵒᵖ A).obj (op n)) := rfl

private theorem principal_coneIso_inr
    {A : Type*} [Category A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ≅ K') (b : L ≅ L') (h : f ≫ b.hom = a.hom ≫ g) :
    CochainComplex.mappingCone.inr f ≫ (coneIso f g a b h).hom =
      b.hom ≫ CochainComplex.mappingCone.inr g :=
  (CochainComplex.mappingCone.triangleMap f g a.hom b.hom h).comm₂

private theorem strictPrincipalLevels (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ b : ∀ n : ℕ, ((strictRed l E T).obj P).asFunctor.obj (op n) ≅
        CochainComplex.PrincipalCone.level
          (principalScalar l E T P) n,
      (∀ n : ℕ, ((strictRed l E T).obj P).asFunctor.map
          (homOfLE (Nat.le_succ n)).op ≫ (b n).hom =
        (b (n + 1)).hom ≫ CochainComplex.PrincipalCone.step
          (principalScalar l E T P) n) ∧
      (∀ n : ℕ, ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
          ((strictAugmentation l E T).app P) ≫ (b n).hom =
        CochainComplex.mappingCone.inr
          (principalScalar l E T P ^ (n + 1)).asHom) := by
  let μ := principalScalar l E T P
  let X := (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P).asFunctor
  let Y := (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P).asFunctor
  let f : X ⟶ Y := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    ((complexPowerMap l E T).app P)
  let e : ((strictRed l E T).obj P).asFunctor ≅ levelConeTower f := levelConeTowerIso f
  have hf (n : ℕ) : f.app (op n) = (μ ^ (n + 1)).asHom := power_on_complex l E T P n
  let c (n : ℕ) := coneIso (f.app (op n)) (μ ^ (n + 1)).asHom
    (Iso.refl P) (Iso.refl P) (by
      change (f.app (op n) : P ⟶ P) ≫ 𝟙 P = 𝟙 P ≫ (μ ^ (n + 1)).asHom
      erw [Category.comp_id, Category.id_comp]
      exact hf n)
  let b (n : ℕ) := e.app (op n) ≪≫ c n
  refine ⟨b, ?_, ?_⟩
  · intro n
    have hX : X.map (homOfLE (Nat.le_succ n)).op = μ.asHom := by
      apply HomologicalComplex.Hom.ext
      funext j
      change ((Functor.ofOpSequence
        (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
        (fun _ ↦ scalar l E T)).map (homOfLE (Nat.le_succ n)).op).app (P.X j) = _
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    have hn := e.hom.naturality (homOfLE (Nat.le_succ n)).op
    have hc : (levelConeTower f).map (homOfLE (Nat.le_succ n)).op ≫ (c n).hom =
        (c (n + 1)).hom ≫ CochainComplex.PrincipalCone.step μ n := by
      change CochainComplex.mappingCone.map _ _ (X.map _) (Y.map _)
          (f.naturality (homOfLE (Nat.le_succ n)).op).symm ≫ (c n).hom =
        (c (n + 1)).hom ≫ CochainComplex.PrincipalCone.step μ n
      apply coneIso_natural
      · change (X.map (homOfLE (Nat.le_succ n)).op : P ⟶ P) ≫ 𝟙 P = 𝟙 P ≫ μ.asHom
        erw [Category.comp_id, Category.id_comp]
        exact hX
      · change (Y.map (homOfLE (Nat.le_succ n)).op : P ⟶ P) ≫ 𝟙 P = 𝟙 P ≫ 𝟙 P
        erw [Category.comp_id]
    change _ ≫ (e.hom.app (op n) ≫ (c n).hom) =
      (e.hom.app (op (n + 1)) ≫ (c (n + 1)).hom) ≫ _
    calc
      _ = (_ ≫ e.hom.app (op n)) ≫ (c n).hom := (Category.assoc _ _ _).symm
      _ = (e.hom.app (op (n + 1)) ≫
          (levelConeTower f).map (homOfLE (Nat.le_succ n)).op) ≫ (c n).hom :=
        congrArg (fun g ↦ g ≫ (c n).hom) hn
      _ = e.hom.app (op (n + 1)) ≫ ((levelConeTower f).map
          (homOfLE (Nat.le_succ n)).op ≫ (c n).hom) := Category.assoc _ _ _
      _ = e.hom.app (op (n + 1)) ≫ ((c (n + 1)).hom ≫ _) :=
        congrArg (fun g ↦ e.hom.app (op (n + 1)) ≫ g) hc
      _ = _ := (Category.assoc _ _ _).symm
  · intro n
    dsimp only [b, Iso.trans_hom, e]
    rw [principal_levelConeTowerIso_app]
    change ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCone.inr ((complexPowerMap l E T).app P)) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          ((complexPowerMap l E T).app P) (ev l E T n)).hom ≫ (c n).hom = _
    rw [← Category.assoc, CochainComplex.mappingCone.map_inr]
    change CochainComplex.mappingCone.inr (f.app (op n)) ≫ (c n).hom = _
    rw [principal_coneIso_inr]
    exact Category.id_comp _

private abbrev strictProductUnit (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ ((strictRed l E T).obj P).asFunctor.obj (op n)) :=
  Pi.lift (fun n : ℕ ↦ ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
    ((strictAugmentation l E T).app P))

private theorem strictProductUnit_difference (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    strictProductUnit l E T P ≫
      ExactProductsRoos.difference.app ((strictRed l E T).obj P) = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [strictProductUnit, towerTransitionEndomorphism,
    towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, sub_eq_zero, zero_comp]
  apply HomologicalComplex.Hom.ext
  funext j
  have h := (((strictAugmentation l E T).app P).f j).naturality
    (homOfLE (Nat.le_succ n)).op
  change 𝟙 (P.X j) ≫ (((strictAugmentation l E T).app P).f j).app (op n) = _ at h
  change (((strictAugmentation l E T).app P).f j).app (op n) = _
  exact (Category.id_comp _).symm.trans h

private def strictRoosAugmentation (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    P ⟶ CochainComplex.mappingCocone
      (ExactProductsRoos.difference.app ((strictRed l E T).obj P)) :=
  CochainComplex.mappingCocone.lift _ (strictProductUnit l E T P) 0
    (by
      have h := congrArg CochainComplex.HomComplex.Cochain.ofHom
        (strictProductUnit_difference l E T P)
      simpa only [CochainComplex.HomComplex.Cochain.ofHom_zero,
        CochainComplex.HomComplex.δ_zero, zero_add] using h)

private theorem principalPositiveRoos (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (principalScalar l E T P)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCocone
        (ExactProductsRoos.difference.app ((strictRed l E T).obj P))),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
          (principalScalar l E T P)) ≫ c.hom =
        DerivedCategory.Q.map (strictRoosAugmentation l E T P) := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  let μ := principalScalar l E T P
  let X := ((strictRed l E T).obj P).asFunctor
  let t (n : ℕ) := X.map (homOfLE (Nat.le_succ n)).op
  let u (n : ℕ) : P ⟶ X.obj (op n) :=
    ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
    ((strictAugmentation l E T).app P)
  have hs (n : ℕ) : u (n + 1) ≫ t n = u n := by
    have h := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((strictAugmentation l E T).app P)).naturality (homOfLE (Nat.le_succ n)).op
    change 𝟙 P ≫ u n = u (n + 1) ≫ t n at h
    simpa only [Category.id_comp] using h.symm
  have hz : Pi.lift u ≫ towerTransitionEndomorphism (K := fun n ↦ X.obj (op n)) t = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp,
      Category.comp_id, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, hs, sub_self,
      zero_comp]
  obtain ⟨b, hb, hu⟩ := strictPrincipalLevels l E T P
  apply AdicCompletion.quotientTowerComparison μ (fun n ↦ X.obj (op n)) t u hz
    (fun n ↦ (b n).inv) (fun _ ↦ inferInstance)
  · intro n
    apply (cancel_epi (b (n + 1)).hom).1
    apply (cancel_mono (b n).hom).1
    simp only [Category.assoc, Category.comp_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
    exact (hb n).symm
  · intro n
    apply (cancel_mono (b n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hu n).symm

private def negativeCoconeIso {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    CochainComplex.mappingCocone φ ≅ CochainComplex.mappingCocone (-φ) :=
  (shiftFunctor _ (-1 : ℤ)).mapIso
    (coneIso φ (-φ) (Iso.refl K)
      (show L ≅ L from ⟨-𝟙 L, -𝟙 L, by simp, by simp⟩) (by simp))

private theorem negativeCoconeIso_lift {A : Type*} [Category A] [Abelian A]
    {P K L : CochainComplex A ℤ} (φ : K ⟶ L) (u : P ⟶ K) (hu : u ≫ φ = 0) :
    CochainComplex.mappingCocone.lift φ u 0 (by simp [hu]) ≫
        (negativeCoconeIso φ).hom =
      CochainComplex.mappingCocone.lift (-φ) u 0 (by simp [hu]) := by
  simpa only [negativeCoconeIso, Functor.mapIso_hom, coneIso, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    (AdicCompletion.zeroLift_natural A φ (-φ) (𝟙 K) (-𝟙 L) (by simp)
      (𝟙 P) u u hu (by simp [hu]) (by simp)).symm

-- Normalize the identity cone map before instantiating its objects with tower products.
private theorem zeroLift_comp
    {A : Type*} [Category A] [Abelian A]
    {C D K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (α : C ⟶ D) (u : C ⟶ K) (v : D ⟶ K)
    (hu : u ≫ φ = 0) (hv : v ≫ φ = 0) (hn : α ≫ v = u) :
    α ≫ CochainComplex.mappingCocone.lift φ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ u 0 (by simp [hu]) := by
  have h := AdicCompletion.zeroLift_natural A φ φ (𝟙 _) (𝟙 _) (by simp)
    α u v hu hv (by simpa only [Category.comp_id] using hn)
  simp only [CochainComplex.mappingCone.map_id, CategoryTheory.Functor.map_id] at h
  refine h.trans ?_
  apply HomologicalComplex.Hom.ext
  funext j
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  erw [Category.comp_id]

private theorem adjointRoosAugmentation (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (((constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex (.up ℤ)).homEquiv
        P ((strictRed l E T).obj P) ((strictAugmentation l E T).app P)) ≫
        ExactProductsRoos.comparison.app ((strictRed l E T).obj P) =
      strictRoosAugmentation l E T P ≫
        (negativeCoconeIso
          (ExactProductsRoos.difference.app ((strictRed l E T).obj P))).hom := by
  let A := AdicCompletion.Modules l E T
  let X := (strictRed l E T).obj P
  let α := (strictAugmentation l E T).app P
  let a := (constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex (.up ℤ)
  let h := a.homEquiv P X α
  have hi : h ≫ ExactProductsRoos.inclusion.app X = strictProductUnit l E T P := by
    apply Pi.hom_ext
    intro n
    have hπ : strictProductUnit l E T P ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n =
          ((ev l E T n).mapHomologicalComplex (.up ℤ)).map α := Pi.lift_comp_π _ n
    rw [hπ]
    change (h ≫ (Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n))
      (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))) ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n = _
    rw [Category.assoc, Pi.lift_comp_π]
    apply HomologicalComplex.Hom.ext
    funext j
    have he := (a.homEquiv P X).symm_apply_apply α
    rw [Adjunction.homEquiv_counit] at he
    exact congrArg (fun f ↦ (f.f j).app (op n)) he
  have hu := strictProductUnit_difference l E T P
  have hz := ExactProductsRoos.inclusion_difference X
  have hni : h ≫ ExactProductsRoos.comparison.app X =
      CochainComplex.mappingCocone.lift (-ExactProductsRoos.difference.app X)
        (strictProductUnit l E T P) 0 (by
          rw [Preadditive.comp_neg, hu, neg_zero]
          simp) := by
    exact zeroLift_comp (-ExactProductsRoos.difference.app X) h
      (strictProductUnit l E T P) (ExactProductsRoos.inclusion.app X)
      (by rw [Preadditive.comp_neg, hu, neg_zero])
      (by rw [Preadditive.comp_neg, hz, neg_zero]) hi
  exact hni.trans (negativeCoconeIso_lift
    (ExactProductsRoos.difference.app X) (strictProductUnit l E T P) hu).symm

private def coneEvaluationComparison (T : Scheme.{u}) (n : ℕ) :
    strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedNakayama.coneFunctor l E T (uniformizer l E ^ (n + 1)) := by
  let τ : 𝟭 (CochainComplex (AdicCompletion.Modules l E T) ℤ) ⟶ 𝟭 _ :=
    Functor.whiskerRight (complexPowerMap l E T)
      ((ev l E T n).mapHomologicalComplex (.up ℤ))
  let e : strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ≅ DerivedNakayama.UnitScalar.coneOf τ :=
    NatIso.ofComponents (fun P ↦ DerivedCategory.Q.mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        ((complexPowerMap l E T).app P) (ev l E T n))) (by
          intro P Q a
          change (DerivedCategory.Q (C := AdicCompletion.Modules l E T)).map _ ≫
              DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
          rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
          apply DerivedCategory.Q.congr_map
          exact ConeNaturality.mapCone_natural (ev l E T n)
            ((complexPowerMap l E T).app P) ((complexPowerMap l E T).app Q)
            (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map a)
            (((constant l E T).mapHomologicalComplex (.up ℤ)).map a)
            ((complexPowerMap l E T).naturality a).symm)
  refine e ≪≫ eqToIso ?_
  change DerivedNakayama.UnitScalar.coneOf
    (Functor.whiskerRight (complexPowerMap l E T)
      ((ev l E T n).mapHomologicalComplex (.up ℤ))) = _
  rw [evaluatedPowerMap]
  rfl

/-- Evaluation of the derived cone tower is naturally the actual finite reduction.
Source: blueprint Assertion 5, the two-term uniformizer resolution
(blueprint: proposition-proper-base-change-complete-integral).
Proof: exact evaluation carries the tower cone to the scalar cone. Scalar action
preserves powers. The coefficient resolution identifies that cone with derived tensor
by the finite coefficient module. The K-flat scalar comparison identifies this tensor
with restriction of the canonical derived scalar extension. Fully faithful
precomposition with localization descends the resulting natural isomorphism. -/
theorem reductionEvaluation (T : Scheme.{u}) (n : ℕ) :
    Nonempty (red l E T ⋙ dev l E T n ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n) := by
  obtain ⟨r, _, i, q, _, _, h⟩ :=
    (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.2
  obtain ⟨e, _⟩ := (h T (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).2
  obtain ⟨s⟩ := finiteScalarComparison l E T n
  let e' : DerivedCategory.Q ⋙ (red l E T ⋙ dev l E T n) ≅
      DerivedNakayama.coneFunctor l E T (uniformizer l E ^ (n + 1)) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (redFactors l E T) (dev l E T n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (strictRed l E T) (ev l E T n).mapDerivedCategoryFactors ≪≫
      coneEvaluationComparison l E T n
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ))
    (DerivedCategory (AdicCompletion.Modules l E T))).preimageIso
      (e' ≪≫ e.some.symm ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q s)⟩

private theorem cochainAdjunctionUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex A ℤ) :
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        UnboundedExactTower.cochainUnit G ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  change (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    (F.mapDerivedCategoryFactors.hom.app P) = _
  apply (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    F.mapDerivedCategory.map_comp, Category.assoc]
  erw [UnboundedExactTower.cochain_counit a ((F.mapHomologicalComplex (.up ℤ)).obj P)]
  erw [← Category.assoc, F.mapDerivedCategoryFactors.hom.naturality,
    Category.assoc, ← DerivedCategory.Q.map_comp]
  have ht := (a.mapHomologicalComplex (.up ℤ)).left_triangle_components P
  rw [ht, (DerivedCategory.Q (C := B)).map_id
    ((F.mapHomologicalComplex (.up ℤ)).obj P)]
  exact (Category.comp_id _).symm

private theorem augmentation_fac (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (augmentation l E T).app (DerivedCategory.Q.obj P) ≫ (redFactors l E T).hom.app P =
      (constant l E T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((strictAugmentation l E T).app P) := by
  simp only [augmentation, Localization.liftNatTrans_app, Functor.whiskerRight_app]
  change (_ ≫ DerivedCategory.Q.map ((strictAugmentation l E T).app P) ≫
    (redFactors l E T).inv.app P) ≫ (redFactors l E T).hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp only [Localization.Lifting.iso]
  exact congrArg (fun g ↦ (constant l E T).mapDerivedCategoryFactors.hom.app P ≫ g)
    (Category.comp_id (DerivedCategory.Q.map ((strictAugmentation l E T).app P)))

private def cochainDerivedUnit {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive] :
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (G.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B)).inv ≫
    Functor.whiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) G.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom G.rightDerivedFunctor

private theorem roosComparisonNormalized (T : Scheme.{u}) :
    ∃ e : ExactProductsRoos.fibre ⋙
        (DerivedCategory.Q (C := AdicCompletion.Modules l E T)) ≅
      (DerivedCategory.Q (C := Tow l E T)) ⋙ rlim l E T,
      ∀ I : CochainComplex (Tow l E T) ℤ,
        DerivedCategory.Q.map (ExactProductsRoos.comparison.app I) ≫ e.hom.app I =
          UnboundedExactTower.cochainUnit (inverseLimit l E T) I := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso (rlim l E T)
    (cochainDerivedUnit (inverseLimit l E T))
    (fun I hI ↦ by
      let := hI
      exact UnboundedExactTower.cochainUnit_isIso (G := inverseLimit l E T) I)
  exact ⟨e, fun I ↦ NatTrans.congr_app he I⟩

/-- On complexes the specified completion unit is the derived ordinary adjoint
of the degree-zero cone inclusion.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral).
Proof: apply the factorization equation of the localized augmentation, the derived
adjunction unit formula, and naturality of the total right derived cochain comparison. -/
private theorem kappa_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (kappa l E T).app (DerivedCategory.Q.obj P) ≫
        (rlim l E T).map ((redFactors l E T).hom.app P) =
      DerivedCategory.Q.map
          (((constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex
            (.up ℤ)).homEquiv P ((strictRed l E T).obj P)
              ((strictAugmentation l E T).app P)) ≫
        UnboundedExactTower.cochainUnit (inverseLimit l E T) ((strictRed l E T).obj P) := by
  dsimp only [kappa, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, ← (rlim l E T).map_comp, augmentation_fac,
    (rlim l E T).map_comp, ← Category.assoc]
  erw [cochainAdjunctionUnit (constLimAdj : constant l E T ⊣ inverseLimit l E T)]
  rw [Category.assoc]
  erw [← (cochainDerivedUnit (inverseLimit l E T)).naturality
    ((strictAugmentation l E T).app P)]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_unit]
  rfl

private theorem principalCompletionComparison (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ b : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (principalScalar l E T P)) ≅
      (completion l E T).obj (DerivedCategory.Q.obj P),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
          (principalScalar l E T P)) ≫ b.hom =
        (kappa l E T).app (DerivedCategory.Q.obj P) := by
  obtain ⟨a, ha⟩ := principalPositiveRoos l E T P
  obtain ⟨e, he⟩ := roosComparisonNormalized l E T
  let X := (strictRed l E T).obj P
  let z := DerivedCategory.Q.mapIso
    (negativeCoconeIso (ExactProductsRoos.difference.app X))
  let r := (rlim l E T).mapIso ((redFactors l E T).app P)
  let b := a ≪≫ z ≪≫ e.app X ≪≫ r.symm
  refine ⟨b, ?_⟩
  apply (cancel_mono r.hom).1
  dsimp only [b, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, ha]
  change (DerivedCategory.Q.map (strictRoosAugmentation l E T P) ≫
    DerivedCategory.Q.map (negativeCoconeIso (ExactProductsRoos.difference.app X)).hom) ≫
      e.hom.app X = _
  rw [← DerivedCategory.Q.map_comp, ← adjointRoosAugmentation,
    DerivedCategory.Q.map_comp, Category.assoc, he]
  exact (kappa_on_complex l E T P).symm

/-- The quotient Roos complex represents the specified completion, preserving its unit.
Source: blueprint Notation 4, Stacks Tags 099B, 0A0E and 0941
(blueprint: proposition-proper-base-change-complete-integral).
Proof: evaluate the strict reduction cone tower and identify it, with its transitions
and degree-zero inclusions, with the principal power-cone tower. Exact products give
its Roos comparison. Change the sign of the second product to match the normalized
right-derived-limit comparison. The ordinary constant/limit adjoint of the strict
inclusion followed by that comparison is exactly kappa. Finally the K-flat principal
cone-to-quotient comparison identifies its strict augmentation with the quotient unit. -/
theorem completionComparison_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P) :
    ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
        (completion l E T).obj (DerivedCategory.Q.obj P),
      DerivedCategory.Q.map (AdicCompletion.augmentation l E T P) ≫ ε.hom =
        (kappa l E T).app (DerivedCategory.Q.obj P) := by
  obtain ⟨c, hc⟩ := AdicCompletion.internal_quotient_principal_cone_comparison l E T
    (uniformizer l E) (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.1 P hP
  obtain ⟨b, hb⟩ := principalCompletionComparison l E T P
  refine ⟨c.symm ≪≫ b, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, ← hc, Category.assoc, Iso.hom_inv_id_assoc]
  exact hb

/-- Every K-flat representative has the normalized comparison required by Notation 4.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral).
Proof: compose the complex comparison with the image of the representative isomorphism.
Naturality of kappa cancels that representative on the specified completion map. -/
theorem completionComparison (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T))
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ M) :
    ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
        (completion l E T).obj M,
      AdicCompletion.completionMap l E T M P e ≫ ε.hom = (kappa l E T).app M := by
  obtain ⟨a, ha⟩ := completionComparison_on_complex l E T P hP
  refine ⟨a ≪≫ (completion l E T).mapIso e, ?_⟩
  change (e.inv ≫ DerivedCategory.Q.map (AdicCompletion.augmentation l E T P)) ≫
    (a.hom ≫ (completion l E T).map e.hom) = _
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map _), ha,
    ← (kappa l E T).naturality e.hom]
  simp

private theorem existsKFlatRepresentative (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    ∃ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  obtain ⟨P, q, hq, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat
    (DerivedCategory.Q.objPreimage M)
  let := hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

/-- Completeness is equivalent to invertibility of the specified completion unit.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral).
Proof: choose a K-flat representative and use the normalized quotient Roos comparison.
The existing representative-independent completeness criterion applies to its unit. -/
theorem isDerivedComplete_iff (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsDerivedComplete l E T M ↔ IsIso ((kappa l E T).app M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := existsKFlatRepresentative l E T M
  obtain ⟨ε, hε⟩ := completionComparison l E T M P hP e
  rw [AdicCompletion.isDerivedComplete_iff l E T M P hP e, ← hε]
  exact (isIso_comp_right_iff (AdicCompletion.completionMap l E T M P e) ε.hom).symm

/-- The output of completion is derived complete for every input.
Source: blueprint Assertion 6 and Stacks Tag 099B
(blueprint: proposition-proper-base-change-complete-integral).
Proof: on a K-flat representative the completion is isomorphic to the quotient Roos
output, whose completeness is already proved by the singleton Koszul reflector.
Transport the witnessing K-flat representative along this isomorphism. -/
theorem completion_isDerivedComplete (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsDerivedComplete l E T ((completion l E T).obj M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := existsKFlatRepresentative l E T M
  obtain ⟨ε, _⟩ := completionComparison l E T M P hP e
  obtain ⟨R, hR, ⟨r⟩, hr⟩ := AdicCompletion.isDerivedComplete_roos l E T P hP
  exact ⟨R, hR, ⟨r ≪≫ ε⟩, hr⟩

private theorem scalarSource_reduction_zero (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    IsZero ((DerivedNakayama.reductionFunctor l E T (n + 1)).obj
      ((rlim l E T).obj (DerivedCategory.Q.obj
        (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P)))) := by
  let A := AdicCompletion.Modules l E T
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let r : CatCenter A := End.of (scalar l E T)
  let X := ((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P
  let V := ∏ᶜ (fun _ : ℕ ↦ P)
  let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ r • 𝟙 P)
  let b : V ⟶ V := Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ P) (n + 1))
  have hscalar (C : CochainComplex A ℤ) :
      r • 𝟙 C = DerivedNakayama.scalarOnComplex l E T (uniformizer l E) C := by
    apply HomologicalComplex.Hom.ext
    funext j
    change (scalar l E T).app (C.X j) ≫ 𝟙 _ = (scalar l E T).app (C.X j)
    exact Category.comp_id _
  have ht (n : ℕ) : X.asFunctor.map (homOfLE (Nat.le_succ n)).op = r • 𝟙 P := by
    rw [hscalar]
    apply HomologicalComplex.Hom.ext
    funext j
    change ((Functor.ofOpSequence
      (X := fun _ : ℕ ↦ 𝟭 A) (fun _ ↦ scalar l E T)).map
        (homOfLE (Nat.le_succ n)).op).app (P.X j) = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  have hd : ExactProductsRoos.difference.app X = 𝟙 V - b ≫ a := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, Pi.lift_comp_π, ht]
    change Pi.π (fun _ : ℕ ↦ P) n - Pi.π (fun _ : ℕ ↦ P) (n + 1) ≫ (r • 𝟙 P) =
      𝟙 V ≫ Pi.π (fun _ : ℕ ↦ P) n - b ≫ a ≫ Pi.π (fun _ : ℕ ↦ P) n
    simp only [Category.id_comp, a, b, Pi.map_π, Pi.lift_comp_π_assoc]
  have hq : QuasiIso
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E)
        (ExactProductsRoos.fibre.obj X)) := by
    rw [← hscalar]
    change QuasiIso (r • 𝟙 (CochainComplex.mappingCocone
      (-ExactProductsRoos.difference.app X)))
    rw [hd]
    exact CochainComplex.scalarTowerProductFibre_scalar_quasiIso P r
  let F := ExactProductsRoos.fibre.obj X
  have hi : IsIso (DerivedCategory.Q.map (principalScalar l E T F).asHom) := by
    let := hq
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E) F)))
  have hip : IsIso (DerivedCategory.Q.map
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ (n + 1)) F)) := by
    rw [scalarOnComplex_pow]
    change IsIso (((DerivedCategory.Q.mapEnd F) (principalScalar l E T F ^ (n + 1))).asHom)
    rw [map_pow]
    exact (isUnit_iff_isIso _).1 (((isUnit_iff_isIso _).2 hi).pow (n + 1))
  have hz := (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ (n + 1)) F))).isZero₃_of_isIso₁
    (DerivedCategory.mappingCone_triangle_distinguished _) hip
  obtain ⟨r₀, _, i, q, _, _, h⟩ :=
    (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.2
  obtain ⟨e⟩ := (h T (n + 1) (Nat.succ_pos n)).2.1
  have hzF : IsZero ((DerivedNakayama.reductionFunctor l E T (n + 1)).obj
      (DerivedCategory.Q.obj F)) := hz.of_iso (e.app F)
  obtain ⟨c⟩ := rlim_roos l E T
  exact hzF.of_iso
    ((DerivedNakayama.reductionFunctor l E T (n + 1)).mapIso (c.app X))

private theorem finiteReduction_kappa_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    IsIso ((DerivedNakayama.reductionFunctor l E T (n + 1)).map
      ((kappa l E T).app (DerivedCategory.Q.obj P))) := by
  let F := DerivedNakayama.reductionFunctor l E T (n + 1)
  let K := (DerivedCategory.singleFunctor (AdicCompletion.Modules l E T) 0).obj
    ((DerivedNakayama.pullback l E T).obj (DerivedNakayama.quotientModule l E (n + 1)))
  let : F.CommShift ℤ := DerivedCategory.commShiftTensorRight
    (C := AdicCompletion.Modules l E T) K
  let : F.IsTriangulated := DerivedCategory.isTriangulated_tensorRight
    (C := AdicCompletion.Modules l E T) K
  let c := (complexPowerMap l E T).app P
  have htri := F.map_distinguished _ ((rlim l E T).map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished c))
  have hz := scalarSource_reduction_zero l E T P n
  have hi : IsIso (F.map ((rlim l E T).map
      (DerivedCategory.Q.map ((strictAugmentation l E T).app P)))) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂
      (F.mapTriangle.obj ((rlim l E T).mapTriangle.obj
        (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle c)))) htri).1 hz
  have haug : IsIso (F.map ((rlim l E T).map
      ((augmentation l E T).app (DerivedCategory.Q.obj P)))) := by
    apply (isIso_comp_right_iff _ (F.map ((rlim l E T).map
      ((redFactors l E T).hom.app P)))).1
    rw [← F.map_comp, ← (rlim l E T).map_comp, augmentation_fac,
      (rlim l E T).map_comp, F.map_comp]
    infer_instance
  have := constantLimit_unit_isIso l E T (DerivedCategory.Q.obj P)
  change IsIso (F.map ((constantLimitAdjunction l E T).unit.app _ ≫
    (rlim l E T).map ((augmentation l E T).app _)))
  rw [F.map_comp]
  infer_instance

/-- Finite reduction inverts the specified completion unit.
Source: blueprint Assertion 6, Stacks Tags 0941 and 099B
(blueprint: proposition-proper-base-change-complete-integral).
Proof: the uniformizer is invertible on the derived limit of the scalar source tower:
its inverse is the index shift up to homotopy on the Roos fibre. Every quotient-power
reduction of that limit is therefore zero, by the uniformizer cone resolution. Apply
reduction and derived inverse limit to the source-constant-cone triangle. Its first
term vanishes, so its second arrow is invertible. This arrow, preceded by the
invertible constant-limit unit, is precisely kappa. Finally use exact conservative
restriction of quotient coefficients and invariance under the choice of complex. -/
theorem finiteReduction_kappa (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) (n : ℕ) :
    IsIso ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M)) := by
  let P := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  have hi := finiteReduction_kappa_complex l E T P n
  have hM : IsIso ((DerivedNakayama.reductionFunctor l E T (n + 1)).map
      ((kappa l E T).app M)) := by
    apply (isIso_comp_left_iff
      ((DerivedNakayama.reductionFunctor l E T (n + 1)).map e.hom) _).1
    have hn : e.hom ≫ (kappa l E T).app M =
        (kappa l E T).app (DerivedCategory.Q.obj P) ≫ (completion l E T).map e.hom :=
      (kappa l E T).naturality e.hom
    rw [← CategoryTheory.Functor.map_comp, hn, CategoryTheory.Functor.map_comp]
    infer_instance
  obtain ⟨c⟩ := finiteScalarComparison l E T n
  have hres : IsIso ((AdicCompletion.restrict l E T n).map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))) :=
    (NatIso.isIso_map_iff c ((kappa l E T).app M)).1 hM
  let G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (AdicCompletion.finiteRing l E T n) ⥤ AdicCompletion.Modules l E T :=
    Mod.comap (AdicCompletion.quotient l E T n)
  let : IsIso (G.mapDerivedCategory.map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))) := hres
  apply (DerivedCategory.isIso_iff _ _).2
  intro j
  let hj : IsIso (G.map ((DerivedCategory.homologyFunctor _ j).map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M)))) :=
    (NatIso.isIso_map_iff (G.mapDerivedCategoryHomologyFunctorIso j) _).2 (by
      change IsIso ((DerivedCategory.homologyFunctor (AdicCompletion.Modules l E T) j).map
        (G.mapDerivedCategory.map
          ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))))
      infer_instance)
  exact isIso_of_reflects_iso _ G

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale
