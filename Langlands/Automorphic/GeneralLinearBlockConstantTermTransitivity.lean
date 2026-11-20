import Langlands.Automorphic.GroupSchemeConstantTermFundamentalDomain
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.Automorphic.GroupSchemeDynamicParabolicRadical
import Langlands.Global.GeneralLinearBlockSemidirectPeriod
import Langlands.Global.LeftCosetSemidirectIntegral
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Transitivity of the normalized block constant terms of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints GeneralLinearBlockSemidirect

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "N(" e ")" => blockUnipotent (Fin n) RF e
local notation "U(" e "," w ")" => leviUnipotent (Fin n) RF e w

local instance : IsAffine (GLG).X.left := isAffine_groupScheme (Fin n) RF

local instance : Smooth (GLG).X.hom := smoothStatement (Fin n) RF

local instance (e : Fin n → ℤ) :
    IsClosed (adelicPoints F GLG N(e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance (e : Fin n → ℤ) : LocallyCompactSpace (adelicPoints F GLG N(e)) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace

local instance (e w : Fin n → ℤ) :
    LocallyCompactSpace (adelicPoints F GLG U(e,w)) :=
  (isClosed_adelicPoints_leviUnipotent F e w).locallyCompactSpace

/-- The rational quotient of every block unipotent radical of `GL_n` is compact. -/
theorem blockUnipotentRationalQuotientCompactSpace (e : Fin n → ℤ) :
    CompactSpace (RationalQuotient F GLG N(e)) := by
  rw [← unipotent_diagonalCocharacter]
  exact IsRationalParabolicRadical.compactSpace_rationalQuotient F GLG
    (isRationalParabolicRadical_dynamic parabolicDynamic
      (isConnectedReductive_generalLinear F (Fin n)) (diagonalCocharacter (Fin n) RF e))

local instance (e : Fin n → ℤ) : CompactSpace (RationalQuotient F GLG N(e)) :=
  blockUnipotentRationalQuotientCompactSpace F e

/-- Constant term of a continuous rational-invariant function on `GL_n(𝔸)`, using
the mass-one quotient measure for the block unipotent radical with weights `e`. -/
def normalizedBlockConstantTerm (e : Fin n → ℤ) (f : ContinuousRationalFunctions F GLG)
    (g : AdelicGroupPoints F GLG) : ℂ :=
  constantTerm F GLG N(e) (normalizedRationalQuotientHaarMeasure F GLG N(e)) f g

theorem normalizedBlockConstantTerm_eq_domain (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    normalizedBlockConstantTerm F e f g =
      LeftCosetSpace.normalizedFundamentalDomainIntegral (rationalSubgroup F GLG N(e))
        (isDiscrete_rationalSubgroup F GLG N(e))
        (fun x => evaluate F GLG f ((x : AdelicGroupPoints F GLG) * g)) := by
  rw [normalizedBlockConstantTerm, normalizedConstantTerm_eq_fundamentalDomainIntegral,
    LeftCosetSpace.normalizedFundamentalDomainIntegral, quotientMassNormalizer,
    rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure_univ, ENNReal.toReal_inv]

/-- For nested block parabolics, the refined constant term is the period of the
coarse constant term over the additional unipotent directions in the coarse Levi. -/
theorem normalizedBlockConstantTerm_eq_iterated {e w : Fin n → ℤ}
    (hw : ∀ i j, e i ≤ e j → w i ≤ w j)
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    normalizedBlockConstantTerm F e f g =
      LeftCosetSpace.normalizedFundamentalDomainIntegral (rationalSubgroup F GLG U(e,w))
        (isDiscrete_rationalSubgroup F GLG U(e,w)) (fun m =>
          normalizedBlockConstantTerm F w f ((m : AdelicGroupPoints F GLG) * g)) := by
  have := leviRationalQuotientCompactSpace F hw
  simp_rw [normalizedBlockConstantTerm_eq_domain]
  have h := LeftCosetSpace.Semidirect.normalizedFundamentalDomainIntegral_eq_iterated
    (normalInclusion F hw) (leviInclusion F e w) (leviProjection F hw)
    (leviProjection_leviInclusion F hw) (exists_normalInclusion_eq F hw)
    (leviProjection_normalInclusion F hw) (isEmbedding_normalInclusion F hw)
    (continuous_leviInclusion F) (continuous_leviProjection F hw)
    (rationalSubgroup F GLG N(e)) (isDiscrete_rationalSubgroup F GLG N(e))
    (rationalSubgroup F GLG U(e,w)) (isDiscrete_rationalSubgroup F GLG U(e,w))
    (leviInclusion_mem_rationalSubgroup F) (leviProjection_mem_rationalSubgroup F hw)
    (rationalSubgroup F GLG N(w)) (isDiscrete_rationalSubgroup F GLG N(w))
    (normalInclusion_mem_rationalSubgroup_iff F hw)
    (fun x => evaluate F GLG f ((x : AdelicGroupPoints F GLG) * g))
    (f.property.comp (continuous_subtype_val.mul continuous_const)) (by
      rintro _ ⟨q, rfl⟩ x
      change f.val.val ((AdelicGroupPoints.rational F GLG q.val *
        (x : AdelicGroupPoints F GLG)) * g) = _
      rw [mul_assoc]
      exact f.val.property q.val _)
  rw [h]
  congr 1
  funext m
  congr 1
  funext x
  exact congrArg (evaluate F GLG f)
    (mul_assoc (x : AdelicGroupPoints F GLG) (m : AdelicGroupPoints F GLG) g)

/-- Left translation by an adelic point of the radical leaves its normalized
constant term unchanged. -/
theorem normalizedBlockConstantTerm_unipotent_mul (e : Fin n → ℤ)
    (f : ContinuousRationalFunctions F GLG) (x : adelicPoints F GLG N(e))
    (g : AdelicGroupPoints F GLG) :
    normalizedBlockConstantTerm F e f ((x : AdelicGroupPoints F GLG) * g) =
      normalizedBlockConstantTerm F e f g := by
  let := rationalQuotientBorelSpace F GLG N(e)
  exact constantTerm_subgroup_mul F GLG N(e) (normalizedRationalQuotientHaarMeasure F GLG N(e))
    f x (measurePreserving_rightTranslate_of_compactRationalQuotient F GLG N(e) x) g

end Langlands.Automorphic.GroupSchemeFunctions
