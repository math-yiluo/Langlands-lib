import Langlands.Geometry.Building.UnramifiedFixedResidueRootModelStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedRootIntersectionReduction
import Langlands.BruhatTits.IntegralModels.QuotientRootCoefficientDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedQuotientBaseChange
import Langlands.BruhatTits.IntegralModels.UnramifiedNearbyParabolicComparisons
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusClause
import Langlands.BruhatTits.IntegralModels.UnramifiedRootIntegrality
import Langlands.BruhatTits.IntegralModels.CommonTorusQuotientMaximality
import Langlands.Geometry.Building.UnramifiedRootRadicalPositivity
import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionReduction
import Langlands.Geometry.Building.RootValueTorusFieldRestriction

/-! # Proof of fixed-point residue-root models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

section Recovered

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom]

private instance residueRootExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local instance residueRootIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance residueRootIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance residueRootIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  haveI : IsLocalHom (algebraMap F (inertiaFixedField F)) :=
    isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

variable
  (hG : IsConnectedReductive G)
  (L : RelativeComponentModelData ↥𝒪[F] F G)
  (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : UnramifiedComponentModelRecovery L E)
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} [Mono iS.hom.hom.left] {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hS : IsSplitTorus S.toGrp)
  (hopp : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (x : D.Apartment)
  (hfull : E.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      D.pointwiseFixer (D.apartmentMap '' ({x} : Set D.Apartment)))

include hG e hiT C hDC hfull

omit [Smooth G.X.hom] in
set_option maxHeartbeats 2000000 in
/-- The full integral points of the base change of the recovered lower model
are the upper full fixer of the point. -/
theorem baseChange_full_integralPoints_of_recovery :
    (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC).pointwiseFixer
          ((MaximalUnramified.buildingDataOfApartment hG hiT D C hDC).apartmentMap ''
            ({x} : Set D.Apartment)) := by
  have h := e.full_integralPoints_eq
  rw [hfull] at h
  exact h

omit [Smooth G.X.hom] in
/-- The base change of the recovered lower model has the root-fixer
intersections of the point. -/
theorem baseChange_hasRootFixerIntersections :
    HasRootFixerIntersections (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
      ({x} : Set D.Apartment) (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) :=
  fun b => rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) {x}
    (baseChange_full_integralPoints_of_recovery hG L E e hiT D C hDC x hfull) b

/-- The prescribed upper torus as a closed split torus of the neutral model of
the base change of the recovered lower model. -/
def baseChangeApartmentTorus :
    IntegralSplitTorusData
      (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).neutral
      (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC).i :=
  (unramifiedIntegralSplitTorusData (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).full {x}
    (baseChange_full_integralPoints_of_recovery hG L E e hiT D C hDC x hfull)).factorNeutral
      (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F))

omit [Smooth G.X.hom] in
/-- The inclusion of the prescribed upper torus is a closed subgroup. -/
theorem baseChangeApartmentTorus_isClosedSubgroup :
    IsClosedSubgroup (baseChangeApartmentTorus hG L E e hiT D C hDC x hfull).inclusion :=
  (unramifiedIntegralSplitTorusData (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).full {x}
    (baseChange_full_integralPoints_of_recovery hG L E e hiT D C hDC x hfull)).factorNeutral_isClosedSubgroup
      (L.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
      (unramifiedIntegralSplitTorusData_isClosedSubgroup _ _ _ _)

omit [Mono iS.hom.hom.left] in
set_option maxHeartbeats 1000000 in
include hf in
/-- **Strictly positive restricted depth reduces into the radical.** -/
theorem mem_positivePoints_of_pos_restrictedDepth
    (Q₀ : SpecialFibreQuotientData L) (hQ₀ : Q₀.IsReductiveQuotient)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hpos : 0 < torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g) :
    g ∈ Q₀.positivePoints := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let C' := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  let E'' := L.baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  have hinter := baseChange_hasRootFixerIntersections hG L E e hiT D C hDC x hfull
  let A'' := baseChangeApartmentTorus hG L E e hiT D C hDC x hfull
  have hQ'' := Q₀.isReductiveQuotient_unramifiedBaseChange hQ₀
  rw [Q₀.mem_positivePoints_iff_unramifiedBaseChange hQ₀]
  have hfactor : CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, CategoryTheory.Functor.map_comp]
    rfl
  generalize hv : torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = v
    at hpos
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ (r : WithTop ℝ) ≤ v := by
    induction v using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_top⟩
    | coe t => exact ⟨t, WithTop.coe_pos.mp hpos, le_rfl⟩
  have hgf : g ∈ rootFiltration iS (torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)) a r :=
    ⟨hg, hv ▸ hr⟩
  rw [rootFiltration_torusFieldRestrictedRootFunctionFamily iS hS hiT.isSplitSubtorus.1 hopp
    (D.isRootDatumValuation_of_mem x.mem) _ hfactor a ha r] at hgf
  have hle : torusRestrictedRootDepthSubgroup (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
      (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a) r ≤
        (Q₀.unramifiedBaseChange).positivePoints := by
    refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m => iSup_le fun hm =>
      iSup_le fun _ => ?_
    intro u hu
    have hmr : ((0 : ℝ) : WithTop ℝ) < ((m * r : ℝ) : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr (mul_pos (Nat.cast_pos.mpr hm) hr0)
    have hu0 : ((0 : ℝ) : WithTop ℝ) < x.val χ u := hmr.trans_le hu.2
    have hufix : u ∈ C'.apartment.rootFixer χ {x} := by
      rw [C'.apartment.rootFixer_singleton]
      exact ⟨hu.1, le_of_lt hu0⟩
    have huint : u ∈ E''.neutral.integralPoints := by
      rw [← hinter ⟨χ, hχ⟩] at hufix
      exact hufix.2
    exact (mem_positivePoints_iff_of_rootFixerIntersections hinter (Set.singleton_nonempty x)
      A''.toIntegralTorusData A''.isSplit _ hQ'' ⟨χ, hχ⟩ hu.1 huint).mpr
        ⟨x, rfl, KPApartmentData.mem_filtrationPlus.mpr ⟨hu.1, hu0⟩⟩
  exact hle hgf

omit [Smooth G.X.hom] [Mono iS.hom.hom.left] in
set_option maxHeartbeats 4000000 in
include hf in
/-- **Upper affine roots vanishing at the point give roots of the reductive
quotient.** The relative root is the restriction of the derivative of the upper
affine root, and its root form is exactly the pulled-back derivative. -/
theorem exists_quotient_root_of_vanishing_affineRoot
    (T₀ : IntegralTorusData L S iS) (hT₀ : IsSplitTorus T₀.torus.toGrp)
    (Q₀ : SpecialFibreQuotientData L) (hQ₀ : Q₀.IsReductiveQuotient)
    (ψ : D.affineRoots) (hψx : ψ.val x = 0)
    (hne : ψ.val.linear.comp (torusFieldTranslationMap F (inertiaFixedField F) f iT hS) ≠ 0) :
    ∃ (b : relativeRoots
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
      (a : relativeRoots iS),
      ψ.val.linear = rootForm
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) b ∧
        (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫ b.val =
          characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S a.val ∧
        T₀.characterSpecialization hT₀ a ∈
          relativeRoots (T₀.specialFibreInclusion ≫ Q₀.projection) := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have := unramifiedResidue_isAlgebraic (F := F)
  have := unramifiedResidue_isSeparable (F := F)
  let : LocallyOfFiniteType Q₀.quotient.X.hom := by
    have : Smooth Q₀.quotient.X.hom := hQ₀.2.2.smooth
    infer_instance
  have hinter := baseChange_hasRootFixerIntersections hG L E e hiT D C hDC x hfull
  let A'' := baseChangeApartmentTorus hG L E e hiT D C hDC x hfull
  have hA''c := baseChangeApartmentTorus_isClosedSubgroup hG L E e hiT D C hDC x hfull
  have hQ' : (Q₀.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).IsReductiveQuotient :=
    Q₀.isReductiveQuotient_baseChange _ _ hQ₀
  obtain ⟨b, hblin, hbroot⟩ :=
    exists_quotient_root_of_incidentAffineRoot_of_rootFixerIntersections hinter
      A''.toIntegralTorusData A''.isSplit _ hQ' ψ.property hψx
  have hf' : CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (Spec.algebraMap F (inertiaFixedField F))).map iS := by
    rw [← hf, CategoryTheory.Functor.map_comp]
    rfl
  obtain ⟨ρ, hρ, hρg⟩ := exists_torusHom_of_baseChange (fixedFieldIntegers F)
    (inertiaFixedField F) T₀ (CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    hT₀ A'' hA''c hf'
  let ψb := (A''.toIntegralTorusData.genericCharacterEquiv A''.isSplit).symm b.val
  have hψb : A''.toIntegralTorusData.genericCharacter ψb = b.val :=
    (A''.toIntegralTorusData.genericCharacterEquiv A''.isSplit).apply_symm_apply b.val
  let m := (characterLattice.baseChangeEquiv (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    T₀.torus hT₀).symm (ρ ≫ ψb)
  have hm : characterLattice.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      T₀.torus m = ρ ≫ ψb :=
    (characterLattice.baseChangeEquiv (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      T₀.torus hT₀).apply_symm_apply _
  have hgen := baseChange_genericCharacter_eq_of_baseChangeComparisonGenericMap
    (fixedFieldIntegers F) (inertiaFixedField F) T₀ A''.toIntegralTorusData
    (CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    ρ hρg m ψb hm
  rw [hψb] at hgen
  have hres : (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫
      b.val = characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S
        (T₀.genericCharacter m) := hgen.symm
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hne
    have ha0 : T₀.genericCharacter m = 0 := by
      rw [hm0]
      exact AddEquiv.map_zero (T₀.genericCharacterEquiv hT₀)
    rw [ha0] at hres
    rw [hblin]
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply]
    change eval ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      b.val (descentCocharacterMap F (inertiaFixedField F) f hS v) = 0
    rw [eval_descentCocharacterMap_of_comp_eq hS f b.val 0 hres v]
    simp [eval_eq_pair]
  have hψroot : A''.toIntegralTorusData.specialCharacterEquiv A''.isSplit ψb ∈
      roots (A''.toIntegralTorusData.specialFibreInclusion ≫
        (Q₀.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).projection) := by
    have h := hbroot
    rw [← hψb, IntegralTorusData.characterSpecialization_genericCharacter] at h
    exact h
  have hroot := T₀.specialCharacter_mem_roots_of_baseChange (fixedFieldIntegers F)
    (inertiaFixedField F) hT₀ Q₀ A''.toIntegralTorusData A''.isSplit ρ hρ m ψb hm hm0 hψroot
  have hroot' : T₀.characterSpecialization hT₀ (T₀.genericCharacter m) ∈
      relativeRoots (T₀.specialFibreInclusion ≫ Q₀.projection) := by
    rw [IntegralTorusData.characterSpecialization_genericCharacter]
    exact hroot
  have ha : T₀.genericCharacter m ∈ relativeRoots iS :=
    (T₀.mem_relativeRoots_characterSpecialization_iff hT₀ _).mp
      (Q₀.relativeRoots_subset_specialFibre hQ₀ T₀ hT₀ hroot')
  exact ⟨b, ⟨T₀.genericCharacter m, ha⟩, hblin, hres, hroot'⟩

end Recovered

set_option maxHeartbeats 20000000 in
/-- **Fixed-point residue-root models.** At every Galois-fixed point of the
upper apartment, the recovered singleton fixer model, its closed split integral
torus and the actual reductive quotient of its special fibre satisfy all six
clauses of `UnramifiedFixedResidueRootModelStatement`. -/
theorem unramifiedFixedResidueRootModel :
    UnramifiedFixedResidueRootModelStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
      mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ P Q x hx
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  obtain ⟨L, E, e, hfull, hnear⟩ :=
    unramifiedFixedRecoveredParabolicModels F G hG S iS hiS T iT f hf hiT hE D C hDC x hx
  obtain ⟨T₀, hT₀⟩ := exists_closedSplitIntegralTorus_of_fullRecovery D C
    hiS hf hDC L E e ({x} : Set D.Apartment) hfull
  obtain ⟨Q₀, hQ₀⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient L
  have hclause := T₀.satisfiesTorusClause_of_generic hG hiS hT₀
  refine ⟨L, T₀, hT₀.1, Q₀, hT₀.2, hclause.2, hQ₀, ?_, ?_, ?_⟩
  · let : Smooth Q₀.radical.X.hom := hQ₀.1.smooth
    let : ConnectedSpace Q₀.radical.X.left := hQ₀.1.connectedSpace
    let : Smooth Q₀.quotient.X.hom := hQ₀.2.2.smooth
    let : IsAffineHom L.neutral.specialFibre.X.hom := by
      change IsAffineHom (CategoryTheory.Limits.pullback.snd L.neutral.group.X.hom
        (IntegralModel.residueBaseMap ↥𝒪[F]))
      infer_instance
    let : LocallyOfFiniteType L.neutral.specialFibre.X.hom := by
      change LocallyOfFiniteType
        (CategoryTheory.Limits.pullback.snd L.neutral.group.X.hom
          (IntegralModel.residueBaseMap ↥𝒪[F]))
      infer_instance
    exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
      Q₀.radicalInclusion hQ₀.1.isClosedSubgroup hQ₀.1.isUnipotent
      Q₀.projection hQ₀.2.1 T₀.specialFibreInclusion).mpr hclause.2
  · intro a ha g hg
    refine ⟨mem_neutral_integralPoints_iff_nonnegative_restrictedDepth L E e hGK hiT D f hf
      hiS.isSplitSubtorus.1 hE x hfull C hDC ha hg, fun hgpos => ?_, fun hpos => ?_⟩
    · exact D.strictPositive_of_mem_positivePoints_of_parabolicRootComparisons
        f hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE hnear Q₀ hQ₀.1 ha hg hgpos
    · have heq : φ x = torusFieldRestrictedRootFunctionFamily
          (k := F) (K := inertiaFixedField F) hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
          (D.isRootDatumValuation_of_mem x.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := rfl
      rw [heq] at hpos
      have h := mem_positivePoints_of_pos_restrictedDepth hG L E e hiT D C hDC f hf
        hiS.isSplitSubtorus.1 hE x hfull Q₀ hQ₀ ha hg
      exact h hpos
  · intro ψ hψx hne
    obtain ⟨b, a, hblin, hres, hroot⟩ := exists_quotient_root_of_vanishing_affineRoot
      (S := S) (T := T) (iS := iS) (iT := iT) hG L E
      e hiT D C hDC f hf hiS.isSplitSubtorus.1 x hfull T₀ hT₀.1 Q₀ hQ₀ ψ hψx hne
    refine ⟨a, hroot, 1, one_ne_zero, ?_⟩
    rw [one_smul, hblin]
    exact (rootForm_comp_torusFieldTranslationMap_of_comp_eq hiS.isSplitSubtorus.1 f iS iT b
      a hres).symm

end Langlands.Geometry.Building
