import Langlands.Global.RankinSelberg.ProjectionPeriod
import Langlands.Global.GeneralLinearBlockSemidirectPeriod
import Langlands.Global.RankinSelberg.UnfoldingOrdinary

/-! # Column-by-column character coefficients along block unipotent subgroups of `GL_n` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite Set Topology
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.GeneralLinearBlockSemidirect

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F] {n : Type} [Fintype n] [DecidableEq n]

local notation "GLG" => Langlands.GroupScheme.GeneralLinear.groupScheme n (CommRingCat.of F)
local notation "RF" => CommRingCat.of F

local instance columnsIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme n (CommRingCat.of F)

local instance columnsSmooth : Smooth (GLG).X.hom :=
  smoothStatement n (CommRingCat.of F)

local instance columnsClosed (e : n → ℤ) :
    IsClosed (adelicPoints F GLG (blockUnipotent n RF e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance columnsLeviClosed (e w : n → ℤ) :
    IsClosed (adelicPoints F GLG (leviUnipotent n RF e w) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_leviUnipotent F e w

local instance columnsLocallyCompact (e : n → ℤ) :
    LocallyCompactSpace (adelicPoints F GLG (blockUnipotent n RF e)) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace

local instance columnsLeviLocallyCompact (e w : n → ℤ) :
    LocallyCompactSpace (adelicPoints F GLG (leviUnipotent n RF e w)) :=
  (isClosed_adelicPoints_leviUnipotent F e w).locallyCompactSpace

variable {e w : n → ℤ} (hw : ∀ i j, e i ≤ e j → w i ≤ w j)

include hw in
/-- Normalized periods over the block unipotent quotient of `e` are iterated normalized
periods: first over the coarser block unipotent quotient of `w`, then over the block Levi
part. -/
theorem normalizedPeriod_eq_iterated
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF e))]
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF w))]
    (φ : adelicPoints F GLG (blockUnipotent n RF e) → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ r ∈ rationalSubgroup F GLG (blockUnipotent n RF e), ∀ x, φ (r * x) = φ x) :
    ((Measure.haar : Measure (adelicPoints F GLG (blockUnipotent n RF e)))
        (LeftCosetSpace.fundamentalDomain (rationalSubgroup F GLG (blockUnipotent n RF e))
          (isDiscrete_rationalSubgroup F GLG _))).toReal⁻¹ •
        ∫ x in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F GLG (blockUnipotent n RF e))
            (isDiscrete_rationalSubgroup F GLG _), φ x ∂Measure.haar =
      ((Measure.haar : Measure (adelicPoints F GLG (leviUnipotent n RF e w)))
        (LeftCosetSpace.fundamentalDomain (rationalSubgroup F GLG (leviUnipotent n RF e w))
          (isDiscrete_rationalSubgroup F GLG _))).toReal⁻¹ •
        ∫ m in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F GLG (leviUnipotent n RF e w))
            (isDiscrete_rationalSubgroup F GLG _),
          ((Measure.haar : Measure (adelicPoints F GLG (blockUnipotent n RF w)))
            (LeftCosetSpace.fundamentalDomain
              (rationalSubgroup F GLG (blockUnipotent n RF w))
              (isDiscrete_rationalSubgroup F GLG _))).toReal⁻¹ •
          ∫ y in LeftCosetSpace.fundamentalDomain
              (rationalSubgroup F GLG (blockUnipotent n RF w))
              (isDiscrete_rationalSubgroup F GLG _),
            φ (normalInclusion F hw y * leviInclusion F e w m) ∂Measure.haar
          ∂Measure.haar := by
  have := leviRationalQuotientCompactSpace F hw
  exact LeftCosetSpace.Semidirect.normalizedPeriod_eq_iterated_of_compact
    (normalInclusion F hw) (leviInclusion F e w) (leviProjection F hw)
    (leviProjection_leviInclusion F hw) (exists_normalInclusion_eq F hw)
    (leviProjection_normalInclusion F hw) (isEmbedding_normalInclusion F hw)
    (continuous_leviInclusion F) (continuous_leviProjection F hw)
    (rationalSubgroup F GLG (blockUnipotent n RF e)) (isDiscrete_rationalSubgroup F GLG _)
    (rationalSubgroup F GLG (leviUnipotent n RF e w)) (isDiscrete_rationalSubgroup F GLG _)
    (leviInclusion_mem_rationalSubgroup F) (leviProjection_mem_rationalSubgroup F hw)
    (rationalSubgroup F GLG (blockUnipotent n RF w)) (isDiscrete_rationalSubgroup F GLG _)
    (normalInclusion_mem_rationalSubgroup_iff F hw) φ hφ hφΓ

end Langlands.Global.GeneralLinearBlockSemidirect

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints GeneralLinearBlockSemidirect

section Normalizer

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance normalizerSubgroupLocallyCompactSpace :
    LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

/-- The mass normalizer is the inverse Haar mass of the chosen fundamental domain. -/
theorem quotientMassNormalizer_toReal :
    (quotientMassNormalizer F G U).toReal =
      ((Measure.haar : Measure (adelicPoints F G U))
        (LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
          (isDiscrete_rationalSubgroup F G U))).toReal⁻¹ := by
  rw [quotientMassNormalizer, rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure_apply _ _ _ MeasurableSet.univ, Set.preimage_univ,
    Set.univ_inter, ENNReal.toReal_inv]

end Normalizer

section Transitivity

variable (F : Type u) [Field F] [NumberField F] {n : Type} [Fintype n] [DecidableEq n]

local notation "GLG" => Langlands.GroupScheme.GeneralLinear.groupScheme n (CommRingCat.of F)
local notation "RF" => CommRingCat.of F

local instance transitivityIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme n (CommRingCat.of F)

local instance transitivitySmooth : Smooth (GLG).X.hom :=
  smoothStatement n (CommRingCat.of F)

local instance transitivityClosed (e : n → ℤ) :
    IsClosed (adelicPoints F GLG (blockUnipotent n RF e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance transitivityLeviClosed (e w : n → ℤ) :
    IsClosed (adelicPoints F GLG (leviUnipotent n RF e w) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_leviUnipotent F e w

local instance transitivityLocallyCompact (e : n → ℤ) :
    LocallyCompactSpace (adelicPoints F GLG (blockUnipotent n RF e)) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace

local instance transitivityLeviLocallyCompact (e w : n → ℤ) :
    LocallyCompactSpace (adelicPoints F GLG (leviUnipotent n RF e w)) :=
  (isClosed_adelicPoints_leviUnipotent F e w).locallyCompactSpace

variable {e w : n → ℤ} (hw : ∀ i j, e i ≤ e j → w i ≤ w j)

include hw in
/-- Transitivity of character coefficients: the coefficient along the block unipotent
subgroup of `e` is the normalized period over the block Levi part of the coefficient along
the coarser block unipotent subgroup of `w`, twisted by the character on the Levi part. -/
theorem subgroupCharacterCoefficient_eq_levi
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF e))]
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF w))]
    (χ : adelicPoints F GLG (blockUnipotent n RF e) → ℂ) (hχc : Continuous χ)
    (hχmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hχrat : ∀ k ∈ rationalSubgroup F GLG (blockUnipotent n RF e), χ k = 1)
    (f : AdelicGroupPoints F GLG → ℂ) (hfc : Continuous f)
    (hfΓ : ∀ k ∈ rationalSubgroup F GLG (blockUnipotent n RF e), ∀ x,
      f ((k : AdelicGroupPoints F GLG) * x) = f x)
    (x : AdelicGroupPoints F GLG) :
    subgroupCharacterCoefficient F GLG (blockUnipotent n RF e) χ f x =
      ((Measure.haar : Measure (adelicPoints F GLG (leviUnipotent n RF e w)))
        (LeftCosetSpace.fundamentalDomain (rationalSubgroup F GLG (leviUnipotent n RF e w))
          (isDiscrete_rationalSubgroup F GLG _))).toReal⁻¹ •
        ∫ m in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F GLG (leviUnipotent n RF e w))
            (isDiscrete_rationalSubgroup F GLG _),
          starRingEnd ℂ (χ (leviInclusion F e w m)) *
            subgroupCharacterCoefficient F GLG (blockUnipotent n RF w)
              (fun y => χ (normalInclusion F hw y)) f ((m : AdelicGroupPoints F GLG) * x)
          ∂Measure.haar := by
  have hχm : Measurable χ := hχc.measurable
  have hχΛ : ∀ (k : rationalSubgroup F GLG (blockUnipotent n RF e))
      (y : adelicPoints F GLG (blockUnipotent n RF e)), χ (k * y) = χ y := by
    intro k y
    rw [hχmul, hχrat k k.property, one_mul]
  have hf' : ∀ (k : rationalSubgroup F GLG (blockUnipotent n RF e))
      (y : AdelicGroupPoints F GLG),
      f (((k : adelicPoints F GLG (blockUnipotent n RF e)) : AdelicGroupPoints F GLG) * y) =
        f y := fun k y => hfΓ k k.property y
  have hχw : Continuous (fun y : adelicPoints F GLG (blockUnipotent n RF w) =>
      χ (normalInclusion F hw y)) :=
    hχc.comp (isEmbedding_normalInclusion F hw).continuous
  have hχΛw : ∀ (k : rationalSubgroup F GLG (blockUnipotent n RF w))
      (y : adelicPoints F GLG (blockUnipotent n RF w)),
      χ (normalInclusion F hw (k * y)) = χ (normalInclusion F hw y) := by
    intro k y
    rw [map_mul, hχmul, hχrat _ ((normalInclusion_mem_rationalSubgroup_iff F hw _).mpr
      k.property), one_mul]
  have hf'w : ∀ (k : rationalSubgroup F GLG (blockUnipotent n RF w))
      (y : AdelicGroupPoints F GLG),
      f (((k : adelicPoints F GLG (blockUnipotent n RF w)) : AdelicGroupPoints F GLG) * y) =
        f y := fun k y =>
    hfΓ (normalInclusion F hw k)
      ((normalInclusion_mem_rationalSubgroup_iff F hw _).mpr k.property) y
  rw [subgroupCharacterCoefficient_eq_setIntegral F GLG _ χ hχm hχΛ f hfc.measurable hf' x,
    quotientMassNormalizer_toReal]
  have hφ : Continuous (fun z : adelicPoints F GLG (blockUnipotent n RF e) =>
      f ((z : AdelicGroupPoints F GLG) * x) * starRingEnd ℂ (χ z)) :=
    (hfc.comp (continuous_subtype_val.mul continuous_const)).mul
      (Complex.continuous_conj.comp hχc)
  have hφΓ : ∀ k ∈ rationalSubgroup F GLG (blockUnipotent n RF e),
      ∀ z : adelicPoints F GLG (blockUnipotent n RF e),
      f (((k * z : adelicPoints F GLG (blockUnipotent n RF e)) : AdelicGroupPoints F GLG) * x) *
          starRingEnd ℂ (χ (k * z)) =
        f ((z : AdelicGroupPoints F GLG) * x) * starRingEnd ℂ (χ z) := by
    intro k hk z
    rw [Subgroup.coe_mul, mul_assoc, hfΓ k hk, hχmul, hχrat k hk, one_mul]
  rw [normalizedPeriod_eq_iterated F hw _ hφ hφΓ]
  congr 1
  refine setIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain _ _) ?_
  intro m _
  simp only
  rw [subgroupCharacterCoefficient_eq_setIntegral F GLG _ _ hχw.measurable hχΛw f
      hfc.measurable hf'w, quotientMassNormalizer_toReal, mul_smul_comm, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  have hco : ((normalInclusion F hw y * leviInclusion F e w m :
      adelicPoints F GLG (blockUnipotent n RF e)) : AdelicGroupPoints F GLG) =
      (y : AdelicGroupPoints F GLG) * (m : AdelicGroupPoints F GLG) := rfl
  rw [hco, mul_assoc, hχmul, map_mul]
  ring

end Transitivity

end Langlands.Global.RankinSelbergGlobal.Unfolding
