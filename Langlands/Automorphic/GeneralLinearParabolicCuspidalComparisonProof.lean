import Langlands.Automorphic.GeneralLinearParabolicCuspidalComparisonStatement
import Langlands.Automorphic.GeneralLinearParabolicCuspidalInclusion
import Langlands.Automorphic.GroupSchemeConstantTermConjugation
import Langlands.Automorphic.GroupSchemeConstantTermFundamentalDomain
import Langlands.Automorphic.GroupSchemeDynamicParabolicRadical
import Langlands.Global.GeneralLinearBlockSemidirectPeriod
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal

/-! # All-proper and standard maximal-block GL cuspidality agree -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

section Reduction

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "RF" => CommRingCat.of F

local instance glParabolicComparisonIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance glParabolicComparisonSmooth : Smooth (GLG).X.hom :=
  smoothStatement (Fin n) (CommRingCat.of F)

local instance glParabolicComparisonClosed (e : Fin n → ℤ) :
    IsClosed (adelicPoints F GLG (blockUnipotent (Fin n) RF e) :
      Set (AdelicGroupPoints F GLG)) :=
  GeneralLinearBlockSemidirect.isClosed_adelicPoints_blockUnipotent F e

omit [NumberField F] in
/-- Weights with no strict increase give the whole group as block parabolic. -/
theorem blockParabolic_eq_top_of_forall_le {e : Fin n → ℤ} (he : ∀ i j, e j ≤ e i) :
    blockParabolic (Fin n) RF e = ⊤ :=
  SubgroupFunctor.ext fun _ => Subgroup.ext fun _ =>
    iff_of_true ((mem_blockParabolic e).mpr fun i j hij => absurd hij (not_lt.mpr (he i j)))
      (Subgroup.mem_top _)

omit [NumberField F] in
/-- The radical of every proper rational parabolic of `GL_n` is the inverse image of a block
unipotent subgroup functor, for a weight with a strict increase, under a rational inner
automorphism. -/
theorem exists_properRationalParabolicRadicals_eq_comap (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive GLG) (P : ProperRationalParabolic GLG) :
    ∃ (g : Over.mk (𝟙 (Spec RF)) ⟶ (GLG).X) (e : Fin n → ℤ), (∃ i j, e i < e j) ∧
      properRationalParabolicRadicals hPD hG P =
        (blockUnipotent (Fin n) RF e).comap ((GLG).innerIso g).hom := by
  obtain ⟨χ, hχ⟩ := P.val.property.exists_dynamicCocharacter hPD hG
  obtain ⟨g, e, hge⟩ := exists_innerIso_comp_eq_diagonalCocharacter F χ
  refine ⟨g, e, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply P.property
    rw [← hχ, Dynamic.parabolic_eq_comap_of_iso χ ((GLG).innerIso g), hge,
      parabolic_diagonalCocharacter, blockParabolic_eq_top_of_forall_le hcon,
      SubgroupFunctor.comap_top]
  · rw [properRationalParabolicRadicals,
      rationalParabolicRadical_eq_dynamic hPD hG χ P.val hχ.symm,
      Dynamic.unipotent_eq_comap_of_iso χ ((GLG).innerIso g), hge, unipotent_diagonalCocharacter]

/-- A function with vanishing standard maximal-block constant terms has vanishing constant
terms along every block unipotent subgroup functor whose weight has a strict increase. -/
theorem forall_constantTerm_blockUnipotent_eq_zero [CompactSpace (AdeleQuotient F)]
    {f : ContinuousRationalFunctions F GLG}
    (hf : f ∈ generalLinearStandardBlockVanishingSubrepresentation F n)
    {e : Fin n → ℤ} {i j : Fin n} (hij : e i < e j)
    [CompactSpace (RationalQuotient F GLG (blockUnipotent (Fin n) RF e))]
    (y : AdelicGroupPoints F GLG) :
    constantTerm F GLG (blockUnipotent (Fin n) RF e)
      (normalizedRationalQuotientHaarMeasure F GLG (blockUnipotent (Fin n) RF e)) f y = 0 := by
  have hw : ∀ k l, e k ≤ e l → thresholdWeight e (e i) k ≤ thresholdWeight e (e i) l :=
    fun _ _ hkl => thresholdWeight_le_of_le e (e i) hkl
  obtain ⟨a, b, h, τ, ha, hb, hτ⟩ := exists_perm_thresholdWeight_eq_twoBlockWeight e (e i)
  have hstd : ∀ y, constantTerm F GLG (GeneralLinearBlockUnipotent.subgroup F h)
      (normalizedRationalQuotientHaarMeasure F GLG
        (GeneralLinearBlockUnipotent.subgroup F h)) f y = 0 :=
    ((hasVanishingConstantTerm_generalLinearBlock_intrinsic_iff F h f).mpr
      ((mem_generalLinearStandardBlockVanishingSubrepresentation_iff F n f).mp hf a b h
        (ha.mpr ⟨j, hij⟩) (hb.mpr ⟨i, le_rfl⟩))).2
  have hthr : ∀ y, constantTerm F GLG (blockUnipotent (Fin n) RF (thresholdWeight e (e i)))
      (normalizedRationalQuotientHaarMeasure F GLG
        (blockUnipotent (Fin n) RF (thresholdWeight e (e i)))) f y = 0 :=
    (forall_constantTerm_eq_zero_comap_innerIso_iff F GLG (permPoint RF τ.symm)
      (GeneralLinearBlockUnipotent.subgroup F h) _
      (blockUnipotent_eq_comap_innerIso_permPoint hτ) f).mp hstd
  have := GeneralLinearBlockSemidirect.thresholdRationalQuotientCompactSpace F e (e i)
  have := rationalQuotientHaarMeasure_isFiniteMeasure F GLG (blockUnipotent (Fin n) RF e)
  have := rationalQuotientHaarMeasure_isFiniteMeasure F GLG
    (blockUnipotent (Fin n) RF (thresholdWeight e (e i)))
  rw [normalizedConstantTerm_eq_zero_iff_fundamentalDomainIntegral_eq_zero,
    fundamentalDomainConstantTerm]
  refine GeneralLinearBlockSemidirect.integral_fundamentalDomain_eq_zero F hw
    (fun x => evaluate F GLG f ((x : AdelicGroupPoints F GLG) * y))
    (f.property.comp (continuous_subtype_val.mul continuous_const)) ?_ fun m => ?_
  · rintro _ ⟨q, rfl⟩ x
    change f.val.val ((AdelicGroupPoints.rational F GLG q.val *
      (x : AdelicGroupPoints F GLG)) * y) = _
    rw [mul_assoc]
    exact f.val.property q.val _
  · have hm := (normalizedConstantTerm_eq_zero_iff_fundamentalDomainIntegral_eq_zero F GLG _ f
      ((m : AdelicGroupPoints F GLG) * y)).mp (hthr _)
    dsimp only [fundamentalDomainConstantTerm] at hm
    refine Eq.trans ?_ hm
    congr 1
    funext z
    exact congrArg (evaluate F GLG f)
      (mul_assoc (z : AdelicGroupPoints F GLG) (m : AdelicGroupPoints F GLG) y)

/-- Normalized vanishing along the radicals of all proper rational parabolics of `GL_n` is the
same as vanishing of the original standard maximal-block constant terms. -/
theorem generalLinearParabolicCuspidalComparison :
    GeneralLinearParabolicCuspidalComparisonStatement.{u} := by
  intro F _ _ n hPD hG _
  refine le_antisymm (normalizedGeneralLinearParabolicCuspidal_le_standardBlock F n hPD hG) ?_
  intro f hf
  rw [mem_normalizedParabolicCuspidalSubrepresentation_iff]
  intro P
  obtain ⟨g, e, ⟨i, j, hij⟩, hU⟩ := exists_properRationalParabolicRadicals_eq_comap hPD hG P
  have hV : blockUnipotent (Fin n) (CommRingCat.of F) e =
      (properRationalParabolicRadicals hPD hG P).comap
        ((GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).innerIso g).symm.hom := by
    rw [hU, ← SubgroupFunctor.comap_comp, Iso.symm_hom, Iso.inv_hom_id, SubgroupFunctor.comap_id]
  have : CompactSpace (RationalQuotient F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      (blockUnipotent (Fin n) (CommRingCat.of F) e)) := by
    rw [hV]
    exact rationalQuotientCompactSpace_comap F _ _
  exact (forall_constantTerm_eq_zero_comap_innerIso_iff F _ g _ _ hU f).mp
    (forall_constantTerm_blockUnipotent_eq_zero hf hij)

end Reduction

example : GeneralLinearParabolicCuspidalComparisonStatement.{u} :=
  generalLinearParabolicCuspidalComparison

end Langlands.Automorphic.GroupSchemeFunctions
