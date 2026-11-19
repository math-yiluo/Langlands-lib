import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Residue maps across compatible local bases -/

noncomputable section

open IsLocalRing Langlands.LocalGalois Langlands.LocalGalois.Separable ValuativeRel
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]

local instance spectralResidueBaseNormedField : NontriviallyNormedField K := localNormedField K
local instance spectralResidueUpperNormedField : NontriviallyNormedField L := localNormedField L
local instance spectralResidueBaseUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance spectralResidueUpperUltrametric : IsUltrametricDist L := localNormedField_ultrametric L
local instance spectralResidueBaseComplete : CompleteSpace K := localNormedField_complete K
local instance spectralResidueUpperComplete : CompleteSpace L := localNormedField_complete L

private theorem norm_algebraMap_le_iff (a b : K) :
    ‖algebraMap K L a‖ ≤ ‖algebraMap K L b‖ ↔ ‖a‖ ≤ ‖b‖ := by
  rw [localNormedField_le L, localNormedField_le K,
    ← (valuation L).vle_iff_le, ← (valuation K).vle_iff_le]
  exact ValuativeExtension.vle_iff_vle a b

private def spectralBaseIntegerMap : baseIntegers K →+* baseIntegers L :=
  (algebraMap K L).restrict (baseIntegers K).toSubring (baseIntegers L).toSubring fun a ha => by
    change ‖algebraMap K L a‖ ≤ 1
    change ‖a‖ ≤ 1 at ha
    simpa only [map_one, norm_one] using (norm_algebraMap_le_iff K L a 1).mpr
      (by simpa only [norm_one] using ha)

private instance spectralBaseIntegerMap_isLocalHom : IsLocalHom (spectralBaseIntegerMap K L) where
  map_nonunit x hx := by
    rw [Separable.isUnit_iff_eq_one] at hx ⊢
    have hnorm : ‖algebraMap K L (x : K)‖ = 1 := congrArg NNReal.toReal hx
    apply NNReal.eq
    change ‖(x : K)‖ = 1
    refine le_antisymm x.property ?_
    simpa only [norm_one] using (norm_algebraMap_le_iff K L 1 x).mp (by
      simp only [map_one, norm_one, hnorm, le_rfl])

/-- The map between spectral base residue fields induced by the compatible
embedding of local fields. -/
def spectralBaseResidueMap :
    ResidueField (baseIntegers K) →+* ResidueField (baseIntegers L) :=
  ResidueField.map (spectralBaseIntegerMap K L)

/-- The dimension of the actual spectral base residue extension. -/
def spectralResidueDegree : ℕ :=
  letI := (spectralBaseResidueMap K L).toAlgebra
  Module.finrank (ResidueField (baseIntegers K)) (ResidueField (baseIntegers L))

theorem spectralResidueDegree_pos : 0 < spectralResidueDegree K L := by
  let : Finite (ResidueField (baseIntegers L)) := localResidue_finite L
  let := (spectralBaseResidueMap K L).toAlgebra
  exact Module.finrank_pos

/-- The upper residue cardinality is the lower cardinality raised to the
residue degree. -/
theorem spectralBaseResidue_card :
    Nat.card (ResidueField (baseIntegers L)) =
      Nat.card (ResidueField (baseIntegers K)) ^ spectralResidueDegree K L := by
  let : Finite (ResidueField (baseIntegers L)) := localResidue_finite L
  let := (spectralBaseResidueMap K L).toAlgebra
  exact Module.natCard_eq_pow_finrank

/-- The residue degree also computes the intrinsic residue dimension. -/
theorem spectralResidueDegree_eq_finrank [Algebra 𝓀[K] 𝓀[L]] :
    spectralResidueDegree K L = Module.finrank 𝓀[K] 𝓀[L] := by
  let : Finite (ResidueField (baseIntegers K)) := localResidue_finite K
  let : Finite (ResidueField (baseIntegers L)) := localResidue_finite L
  have hK := Nat.card_congr (localResidueEquiv K).toEquiv
  have hL := Nat.card_congr (localResidueEquiv L).toEquiv
  have h := spectralBaseResidue_card K L
  rw [hK, hL, Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])] at h
  exact Nat.pow_right_injective Finite.one_lt_card h.symm

section Algebraic

variable (X Y : Type u) [Field X] [Field Y]
    [Algebra K X] [Algebra.IsAlgebraic K X]
    [Algebra L Y] [Algebra.IsAlgebraic L Y]
    [Algebra K Y] [IsScalarTower K L Y] (f : X →ₐ[K] Y)

/-- Integral elements map to integral elements when the two algebraic
extensions are taken over compatible local bases. -/
def spectralExtensionIntegerMap : extensionIntegers K X →+* extensionIntegers L Y :=
  f.toRingHom.restrict (extensionIntegers K X).toSubring
    (extensionIntegers L Y).toSubring fun z hz => by
      apply (integral_iff_mem_spectralIntegers L Y (f z)).mp
      apply IsIntegral.map_of_comp_eq (spectralBaseIntegerMap K L) f.toRingHom
      · ext a
        change algebraMap L Y (algebraMap K L (a : K)) = f (algebraMap K X (a : K))
        rw [← IsScalarTower.algebraMap_apply K L Y, f.commutes]
      · exact (integral_iff_mem_spectralIntegers K X z).mpr hz

@[simp]
theorem spectralExtensionIntegerMap_coe (x : extensionIntegers K X) :
    (spectralExtensionIntegerMap K L X Y f x : Y) = f (x : X) := rfl

set_option backward.isDefEq.respectTransparency false in
instance spectralExtensionIntegerMap_isLocalHom :
    IsLocalHom (spectralExtensionIntegerMap K L X Y f) where
  map_nonunit x hx := by
    by_contra hxu
    have hxlt : spectralValuation K X (x : X) < 1 :=
      lt_of_le_of_ne x.property fun h => hxu ((Separable.isUnit_iff_eq_one _ _).mpr h)
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_nnnorm_lt_one K
    have haX : spectralValuation K X (algebraMap K X a) = ‖a‖₊ :=
      NNReal.eq (spectralNorm_extends a)
    have haL : ‖algebraMap K L a‖₊ < 1 := by
      apply lt_of_not_ge
      intro h
      exact (not_le_of_gt ha1) (by
        have h' : ‖(1 : K)‖ ≤ ‖a‖ := (norm_algebraMap_le_iff K L 1 a).mp (by
          simpa only [map_one, norm_one] using (show 1 ≤ ‖algebraMap K L a‖ from h))
        exact NNReal.coe_le_coe.mp (show (1 : ℝ) ≤ ‖a‖ by simpa only [norm_one] using h'))
    let p : extensionIntegers K X := ⟨algebraMap K X a, by
      change spectralValuation K X (algebraMap K X a) ≤ 1
      exact haX.symm ▸ ha1.le⟩
    let g := spectralExtensionIntegerMap K L X Y f
    have hpY : spectralValuation L Y (g p : Y) < 1 := by
      change spectralNorm L Y (f (algebraMap K X a)) < 1
      rw [f.commutes, IsScalarTower.algebraMap_apply K L Y, spectralNorm_extends]
      exact haL
    have hpX : 0 < spectralValuation K X (p : X) := haX.symm ▸ ha0
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpX hxlt
    let y : extensionIntegers K X := ⟨(x : X) ^ n / p, by
      rw [Valuation.mem_valuationSubring_iff, map_div₀, map_pow, div_le_one₀ hpX]
      exact hn.le⟩
    have hfactor : x ^ n = p * y := by
      apply Subtype.ext
      exact (mul_div_cancel₀ _ (fun h => hpX.ne' (by rw [h, map_zero]))).symm
    have hpz : residue _ (g p) = 0 :=
      (residue_eq_zero_iff _).mpr ((mem_maximalIdeal_iff_lt _ _).mpr hpY)
    have hpow := congrArg (fun z => residue _ (g z)) hfactor
    simp only [map_pow, map_mul, hpz, zero_mul] at hpow
    exact ((residue_ne_zero_iff_isUnit _).mpr hx) (eq_zero_of_pow_eq_zero hpow)

/-- The induced injective residue field map for algebraic extensions over
compatible local bases. -/
def spectralExtensionResidueMap :
    ResidueField (extensionIntegers K X) →+* ResidueField (extensionIntegers L Y) :=
  ResidueField.map (spectralExtensionIntegerMap K L X Y f)

@[simp]
theorem spectralExtensionResidueMap_residue (x : extensionIntegers K X) :
    spectralExtensionResidueMap K L X Y f (residue _ x) =
      residue _ (spectralExtensionIntegerMap K L X Y f x) := rfl

end Algebraic

end Langlands.ClassFieldTheory.Local
