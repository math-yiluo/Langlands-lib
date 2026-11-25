/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding

/-!
# Constructibility and restriction to constant scalars

## References

* Stacks Project, Tags 093I, 09AJ and 099Y, using global finite partitions

## Implementation details

The intrinsic constructibility predicate requires a positive number of strata; a
fixed-coefficient partition with zero strata (which forces the scheme to be empty) is replaced
by the one-stratum identity partition.
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

namespace ConstantScalarComparison

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (A : Type (u + 1)) [CommRing A] (R : Sheaf J RingCat.{u + 1})
  (a : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)

private noncomputable def restriction : SheafOfModules.{u + 1} R ⥤
    Sheaf J (ModuleCat.{u + 1} A) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars a).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} A :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars a).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def restrictionFullyFaithful [Presheaf.IsLocallySurjective J a] :
    (restriction J A R a).FullyFaithful where
  preimage {M N} φ :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective a N.isSheaf).symm
        { app := φ.hom.app
          naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

variable [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} A)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} A)]

private noncomputable def constantPresheaf (M : ModuleCat.{u + 1} A) :
    PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj _ := M
  map _ := 𝟙 M

private noncomputable def constantComparisonHom (M : ModuleCat.{u + 1} A) :
    (constantSheaf J (ModuleCat.{u + 1} A)).obj M ⟶
      (restriction J A R a).obj
        ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app (constantPresheaf A M)
  exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }

private theorem constantComparisonHom_isIso (M : ModuleCat.{u + 1} A) :
    IsIso (constantComparisonHom J A R a M) := by
  let N := (restriction J A R a).obj
    ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M))
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app
    (constantPresheaf A M)
  let η' : (Functor.const Cᵒᵖ).obj M ⟶ N.obj :=
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }
  have hηi : Presheaf.IsLocallyInjective J η' := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hηs : Presheaf.IsLocallySurjective J η' := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hf : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      (constantComparisonHom J A R a M).hom = η' := by
    exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj M) N).apply_symm_apply η'
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J η' hf
  · change Presheaf.IsLocallySurjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf

end ConstantScalarComparison

private theorem localConstancy_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    IsLocallyConstantProEtaleModuleSheaf T B F ↔
      IsLocallyConstantProEtaleFixedModuleSheaf T (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) := by
  let A := ULift.{u + 1, u} B
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B)
  have h (U : T.ProEt) :
      Presheaf.IsLocallyInjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) ∧
      Presheaf.IsLocallySurjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) :=
    proEtaleConstantRingUnit_over_locallyBijective T B U
  constructor
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨E.mapIso e ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology T).over (U i)) A (R.over (U i)) a M)).symm⟩⟩
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a).preimageIso
        (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
          ((ProEt.topology T).over (U i)) A (R.over (U i)) a M))⟩⟩

private theorem finite_stalk_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) ↔
      Finite (proEtaleGeometricFixedModuleStalk x (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F)) := by
  let D := proEtaleGeometricStalkDiagram x ((proEtaleModuleRestriction T B).obj F)
  let e := CategoryTheory.preservesColimitIso
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) D
  constructor
  · intro h
    have : Finite (↑(Limits.colimit (D ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})) :
          Type (u + 1)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom)).symm
  · intro h
    have : Finite ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
        AddCommGrpCat.{u + 1}).obj (Limits.colimit D)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom))

private theorem finiteLocal_iff (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) ↔
      IsLocallyConstantProEtaleModuleSheaf T B F ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
          Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) := by
  constructor
  · rintro ⟨ι, W, g, hg, hM⟩
    have hl := ProEtale.finiteModels_over (ULift.{u + 1, u} B) _ ⟨ι, W, g, hg, fun i ↦
      (hM i).imp fun _ ⟨_, e⟩ ↦ ⟨Module.finite_of_finite (ULift.{u + 1, u} B), e⟩⟩
    refine ⟨(localConstancy_iff T B F).mpr ?_, fun Ω _ _ x ↦ ?_⟩
    · obtain ⟨I, U, f, hf, he⟩ := hl
      exact ⟨I, U, f, hf, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
    · exact (finite_stalk_iff T B F Ω x).mpr
        (ProEtale.finite_geometricStalk_of_finite_models (ULift.{u + 1, u} B) _
          ⟨ι, W, g, hg, fun i ↦ (hM i).imp fun _ ⟨_, e⟩ ↦
            ⟨Module.finite_of_finite (ULift.{u + 1, u} B), e⟩⟩ Ω x)
  · rintro ⟨hl, hs⟩
    obtain ⟨ι, W, g, hg, hM⟩ := finite_models_of_fixed_lisse T (ULift.{u + 1, u} B) _
      ⟨(localConstancy_iff T B F).mp hl,
        fun Ω _ _ x ↦ (finite_stalk_iff T B F Ω x).mp (hs Ω x)⟩
    exact ⟨ι, W, g, hg, fun i ↦ (hM i).imp fun _ ⟨_, e⟩ ↦ ⟨Module.Finite.of_finite, e⟩⟩

private theorem empty_finiteLocal (T : Scheme.{u}) [IsEmpty T]
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    ProEtale.IsFiniteLocallyConstant A F := by
  refine ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim, ?_,
    fun i ↦ i.down.elim⟩
  have he : Presieve.ofArrows (fun i : ULift.{u + 1} Empty ↦ i.down.elim)
      (fun i ↦ i.down.elim) = (⊥ : Presieve T) := by
    funext U f
    apply propext
    constructor
    · rintro ⟨i⟩
      exact i.down.elim
    · exact False.elim
  rw [he]
  exact bot_mem_propQCPrecoverage T

private def identityStratification (T : Scheme.{u}) : Stratification T where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  isConstructible_stratum _ := Topology.IsConstructible.univ
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim _ _)).elim
  domain _ := T
  immersion _ := 𝟙 T
  range_immersion _ := Set.range_id

private theorem positive_stratification (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (h : ProEtale.IsConstructible A F) :
    ∃ S : Stratification T, 0 < S.n ∧ ∀ i : Fin S.n,
      ProEtale.IsFiniteLocallyConstant A ((ProEtale.upperStar _ (S.immersion i)).obj F) := by
  obtain ⟨S, hS⟩ := h
  by_cases hn : 0 < S.n
  · exact ⟨S, hn, hS⟩
  have hz : S.n = 0 := Nat.eq_zero_of_not_pos hn
  have : IsEmpty T := ⟨fun x ↦ by
    have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact Fin.elim0 (hz ▸ i)⟩
  exact ⟨identityStratification T, Nat.zero_lt_one,
    fun i ↦ empty_finiteLocal T A _⟩

/-- The intrinsic and fixed-coefficient constructibility predicates agree under
restriction to constant scalars. -/
theorem proEtaleModuleRestriction_constructible_iff (T : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    IsConstructibleProEtaleModuleSheaf T B F ↔
      ProEtale.IsConstructible (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) := by
  constructor
  · rintro ⟨S, hn, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (S.immersion i) B F
    exact ProEtale.isFiniteLocallyConstant_of_iso e
      ((finiteLocal_iff (S.domain i) B _).mpr (hS i))
  · intro h
    obtain ⟨S, hn, hS⟩ := positive_stratification T (ULift.{u + 1, u} B) _ h
    refine ⟨S, hn, fun i ↦ ?_⟩
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (S.immersion i) B F
    exact (finiteLocal_iff (S.domain i) B _).mp
      (ProEtale.isFiniteLocallyConstant_of_iso e.symm (hS i))

end AlgebraicGeometry.Scheme
