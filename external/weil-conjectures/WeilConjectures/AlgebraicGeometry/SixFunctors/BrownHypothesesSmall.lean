/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentiallySmall
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.CategoryTheory.SixFunctors.WeakSerreBoundedThick
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHomologyEssentiallySmall
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Order.CompletePartialOrder

/-!
# Thick and essentially small constructible finite-Tor complexes
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem ordinary_constructible_iff (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A X M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ (hC i.down).imp fun _ hP ↦
        ⟨by have := hP.1; exact Module.Finite.of_finite, hP.2⟩⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    let D := C.restrictIndexOfSmall.{u}
    exact ⟨D, fun i ↦ (h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)).imp
      fun _ hP ↦ ⟨by have := hP.1; exact Module.finite_of_finite (ULift.{u + 1} A), hP.2⟩⟩

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem bounded_retract_inverseImage
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts :=
  ⟨fun e h ↦ P.prop_of_retract (e.map F) h⟩

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem small_bounded_constant_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] :
    ObjectProperty.EssentiallySmall.{u + 1} (constantModelBoundedConstructible Λ X) := by
  have : ObjectProperty.EssentiallySmall.{u + 1} (IsConstantModelConstructible Λ X) := by
    rw [show IsConstantModelConstructible Λ X = IsFiniteConstantStratified Λ X by
      funext M
      exact ite_eq_left ⟨inferInstance, inferInstance⟩]
    exact stratifiedModelsSmall Λ X
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  exact DerivedCategory.bounded_homologyProperty_essentiallySmall _

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem constant_heart_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ObjectProperty.ContainsZero (IsConstantModelConstructible Λ X) := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : Zero C := HasZeroObject.zero' C
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨0, isZero_zero _, ?_⟩
  rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  refine ⟨S, fun a ↦ ?_⟩
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a) :=
    .singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _)
  let P := cokernel (𝟙 (Mod.finiteFree Λ 0))
  refine ⟨U, fun i ↦ ⟨P, ⟨0, 0, 𝟙 _, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩⟩
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    unfold upperStarFromPoint
    infer_instance
  exact ((CondensedRing.upperStar Λ (U.f i)).map_isZero
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint (U.X i)).mapMod Λ).map_isZero
        (isZero_cokernel_of_epi (𝟙 (Mod.finiteFree Λ 0))))

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem thick_of_heart_closure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (f : M ⟶ N),
      IsConstantModelConstructible Λ X M → IsConstantModelConstructible Λ X N →
      IsConstantModelConstructible Λ X (kernel f) ∧
        IsConstantModelConstructible Λ X (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), S.ShortExact →
      IsConstantModelConstructible Λ X S.X₁ → IsConstantModelConstructible Λ X S.X₃ →
      IsConstantModelConstructible Λ X S.X₂) :
    (constantModelBoundedConstructible Λ X).IsTriangulated ∧
      (constantModelBoundedConstructible Λ X).IsStableUnderRetracts := by
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  have : P.ContainsZero := constant_heart_zero Λ X
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso h)
      (hk _ _ f hMN.1 hMN.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso h)
      (hk _ _ f hMN.1 hMN.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ he _ h h₁ h₃⟩
  have h := weakSerre_bounded_homology_thick P
  have heq : constantModelBoundedConstructible Λ X =
      DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded := by
    exact inf_comm _ _
  rw [heq]
  exact ⟨h.1, h.2.1⟩

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem thick_coefficient_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : (constantModelBoundedConstructible Λ X).IsTriangulated ∧
      (constantModelBoundedConstructible Λ X).IsStableUnderRetracts) :
    (constantModelBoundedConstructible Λ' X).IsTriangulated ∧
      (constantModelBoundedConstructible Λ' X).IsStableUnderRetracts := by
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comap ((upperStarFromPoint X).map φ)
  have hp : constantModelBoundedConstructible Λ' X =
      (constantModelBoundedConstructible Λ X).inverseImage F.mapDerivedCategory := by
    funext K
    apply propext
    constructor
    · rintro ⟨hb, hc⟩
      refine ⟨F.bounded_mapDerivedCategory_obj hb, fun n ↦ ?_⟩
      exact (constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
        ((constantModel_comap_iff φ X _).mpr (hc n)))
    · rintro ⟨hb, hc⟩
      refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj hb, fun n ↦ ?_⟩
      apply (constantModel_comap_iff φ X _).mp
      exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (hc n)
  have := h.1
  have := h.2
  rw [hp]
  exact ⟨inferInstance, bounded_retract_inverseImage _ _⟩

set_option synthInstance.maxSize 2048 in
open scoped CategoryTheory.Obj in
private theorem finite_bounded_thick (A : Type u) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X
      ).IsTriangulated ∧
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X
      ).IsStableUnderRetracts := by
  classical
  let B := ULift.{u + 1} A
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :=
    IsConstructible B
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ isConstructible_of_iso e h⟩
  have : P.ContainsZero := by
    let Z := (HasZeroObject.zero (C := Scheme.pbcModules X
      (Scheme.adicLisseConstantRing X B))).choose
    have hz := (HasZeroObject.zero (C := Scheme.pbcModules X
      (Scheme.adicLisseConstantRing X B))).choose_spec
    let F := Scheme.CoefficientSerre.proEtaleModuleRestriction X B
    exact ⟨F.obj Z, F.map_isZero hz,
      (Scheme.CoefficientSerre.coefficient_constructible_iff X B Z).mp
        (Scheme.coefficientConstructible_of_isZero X B Z hz)⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso h)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X B _ _ f hMN.1 hMN.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hMN⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso h)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X B _ _ f hMN.1 hMN.2).2⟩
  have : P.IsClosedUnderExtensions :=
    ⟨fun h h₁ h₃ ↦ Scheme.CoefficientSerre.fixed_extension X B _ h h₁ h₃⟩
  let Q : ObjectProperty (DerivedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))) :=
    DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have ht := weakSerre_bounded_homology_thick P
  have : Q.IsTriangulated := by simpa only [Q, inf_comm] using ht.1
  have : Q.IsStableUnderRetracts := by simpa only [Q, inf_comm] using ht.2.1
  let e := Classical.choice (FiniteDiscreteOrdinary.encoding_exists A X)
  let F := (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory
  have hp : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X =
      Q.inverseImage F := by
    funext K
    apply propext
    refine ((FiniteDiscreteOrdinary.encoding_constructibility A X e).2 K).trans ?_
    exact and_congr_right fun _ ↦ forall_congr' fun n ↦ ordinary_constructible_iff A X _
  have : F.IsTriangulated :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
  rw [hp]
  exact ⟨inferInstance, bounded_retract_inverseImage _ _⟩

/-- For a Noetherian scheme and one of the six admissible condensed coefficient rings,
the bounded constructible finite-Tor complexes form a thick essentially small subcategory.
The alternatives in `_hΛ` are finite discrete `A` killed by an `l`-power, `ℤ_[l]`,
`𝒪_E`, `ℚ_[l]`, `E`, and the finite-subextension-valued condensed `ℚ̄_l`.
-/
theorem det_brown_hypotheses_small
    (l : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (l ^ n : A) = 0)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[l])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj l E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[l])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj l)))
    (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] :
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsTriangulated ∧
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsStableUnderRetracts ∧
    ObjectProperty.EssentiallySmall.{u + 1}
      (constantModelBoundedConstructible Λ X ⊓
        (fun K => DerivedCategory.finiteTorAmplitude _ K)) := by
  classical
  have : IsNoetherian X := {}
  have hint (F : PadicAlgCl.FiniteIntermediateField l) :
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj l F) X
        ).IsTriangulated ∧
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj l F) X
        ).IsStableUnderRetracts := by
    obtain ⟨hk, he⟩ := isConstantModelConstructible_serre_padicIntegers X l F
    exact thick_of_heart_closure _ X hk he
  have hfield := constantModelBoundedConstructible_field_triangulated l X
  have field (F : PadicAlgCl.FiniteIntermediateField l) :
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
        ).IsTriangulated ∧
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
        ).IsStableUnderRetracts :=
    ⟨(hfield.1 F).2.1, (hfield.1 F).2.2⟩
  obtain ⟨_, _, _, _, _, _, _, _, q, z, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} l
  let F₀ : PadicAlgCl.FiniteIntermediateField l := ⟨⊥, inferInstance⟩
  have hbc : (constantModelBoundedConstructible Λ X).IsTriangulated ∧
      (constantModelBoundedConstructible Λ X).IsStableUnderRetracts := by
    rcases _hΛ with h | h | h | h | h | h <;> obtain ⟨e⟩ := h
    · exact thick_coefficient_iso e.symm X (finite_bounded_thick A X)
    · exact thick_coefficient_iso (e ≪≫ z).symm X (hint F₀)
    · exact thick_coefficient_iso e.symm X (hint E)
    · exact thick_coefficient_iso (e ≪≫ q).symm X (field F₀)
    · exact thick_coefficient_iso e.symm X (field E)
    · exact thick_coefficient_iso e.symm X ⟨hfield.2.2.1, hfield.2.2.2⟩
  have hw := constantModelConstructibleFiniteTor_wellDefined Λ X
  have := hbc.1
  have := hbc.2
  have := hw.2.1
  have := hw.2.2.2.1
  have := hw.2.2.2.2.2.2.2.1
  have := hw.2.2.2.2.2.2.2.2
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact ⟨fun e h ↦
      ⟨(constantModelBoundedConstructible Λ X).prop_of_retract e h.1,
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_retract e h.2⟩⟩
  · have := small_bounded_constant_models Λ X
    exact ObjectProperty.EssentiallySmall.of_le (fun _ h ↦ h.1)

end AlgebraicGeometry.ProEtale

end
