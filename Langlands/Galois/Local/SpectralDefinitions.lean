import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Valuation.RamificationGroup

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

def spectralValuation : Valuation L ℝ≥0 where
  toFun x := ⟨spectralNorm K L x, spectralNorm_nonneg x⟩
  map_zero' := NNReal.eq <| spectralNorm_zero
  map_one' := NNReal.eq <| spectralNorm_one
  map_mul' x y := NNReal.eq <| spectralAlgNorm_mul x y
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

instance spectralValuation_extends :
    (NormedField.valuation (K := K)).HasExtension (spectralValuation K L) where
  val_isEquiv_comap x y := by
    change ‖x‖₊ ≤ ‖y‖₊ ↔
      spectralValuation K L (algebraMap K L x) ≤
        spectralValuation K L (algebraMap K L y)
    change ‖x‖ ≤ ‖y‖ ↔
      spectralNorm K L (algebraMap K L x) ≤ spectralNorm K L (algebraMap K L y)
    simp only [spectralNorm_extends]

abbrev baseIntegers := (NormedField.valuation (K := K)).valuationSubring
abbrev extensionIntegers := (spectralValuation K L).valuationSubring

def integerAut (σ : Gal(L/K)) :
    extensionIntegers K L ≃ₐ[baseIntegers K] extensionIntegers K L where
  toFun x := ⟨σ x, by
    change spectralNorm K L (σ x) ≤ 1
    exact (spectralNorm_eq_of_equiv (K := K) σ (x : L)).symm.le.trans x.property⟩
  invFun x := ⟨σ.symm x, by
    change spectralNorm K L (σ.symm x) ≤ 1
    exact (spectralNorm_eq_of_equiv (K := K) σ.symm (x : L)).symm.le.trans x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (σ.map_mul x y)
  map_add' x y := Subtype.ext (σ.map_add x y)
  commutes' x := Subtype.ext (σ.commutes x)

def residueHom : Gal(L/K) →*
    Gal(ResidueField (extensionIntegers K L)/ResidueField (baseIntegers K)) where
  toFun σ := ResidueField.mapAlgEquiv' (integerAut K L σ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl

def inertia : Subgroup Gal(L/K) := (residueHom K L).ker

instance inertia_normal : (inertia K L).Normal := MonoidHom.normal_ker _

open scoped Pointwise in
def decompositionHom : Gal(L/K) →* (extensionIntegers K L).decompositionSubgroup K where
  toFun σ := ⟨σ, by
    change σ • extensionIntegers K L = extensionIntegers K L
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change spectralNorm K L (σ.symm x) ≤ 1 ↔ spectralNorm K L x ≤ 1
    rw [← spectralNorm_eq_of_equiv σ.symm x]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Langlands.LocalGalois
