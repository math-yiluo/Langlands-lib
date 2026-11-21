import Langlands.Global.RankinSelberg.RealGodementCanonicalCoefficient

/-! # The canonical Jacquet map on spectral Godement generators -/

noncomputable section

open Langlands.Analysis Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet PrincipalSeriesExtension RealGodementProfiles RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "K" => unitaryCompact ℝ (t + 2)
local notation "P" => (Fin (t + 1) → ℂ)
local notation "P'" => (Fin (t + 2) → ℂ)
local notation "L'" => (Fin (t + 2) → Fin 2)

/-- The linear extension of the fixed compact frame into the upper K-finite standard space. -/
def spectralFrameKFiniteLift (p : L') (W : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W) (z : P') :
    spectralFrameSpace p W →ₗ[ℂ] Automorphic.realStandardKFinite (t + 2) (characterList p z) := by
  let L : spectralFrameSpace p W →ₗ[ℂ] (H → ℂ) := {
    toFun := fun f => standardSection z (frameProfile f.val)
    map_add' := fun x y => (extensionLinear _).map_add (frameProfile x.val) (frameProfile y.val)
    map_smul' := fun c x => (extensionLinear _).map_smul c (frameProfile x.val) }
  exact L.codRestrict _ fun f => standardSection_mem (isCompactProfile_frameProfile hW f.property) z

@[simp] theorem compactSectionRestriction_spectralFrameKFiniteLift (p : L')
    (W : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W) (z : P') (f : spectralFrameSpace p W) :
    compactSectionRestriction (spectralFrameKFiniteLift p W hW z f).val = f.val :=
  compactSectionRestriction_standardSection_frameProfile z f.val

section Columns

variable (D : RealQuotientMeasureData t) {p : Fin (t + 2) → Fin 2}
variable {W : Submodule ℂ (unitaryCompact ℝ (t + 2) → ℂ)} [FiniteDimensional ℂ W]
variable (hW : ∀ f ∈ W, ∀ q : unitaryCompact ℝ (t + 2),
  (fun k : unitaryCompact ℝ (t + 2) => f (q * k)) ∈ W)

/-- The compact restriction of a spectral Godement generator as a vector of the fixed frame. -/
def SpectralSectionFamily.frameVector (C : SpectralSectionFamily D.groupHaar p W) (z : P') :
    spectralFrameSpace p W := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := (realMatrixHaar_symmetries D.groupHaar).1
  exact ⟨C.column z, C.column_mem hW z⟩

theorem SpectralSectionFamily.spectralFrameKFiniteLift_frameVector
    (C : SpectralSectionFamily D.groupHaar p W) (z : P') :
    (spectralFrameKFiniteLift p W hW z (C.frameVector D hW z)).val = C.upperSection z := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := (realMatrixHaar_symmetries D.groupHaar).1
  exact (C.section_eq_standardSection hW z).symm

private theorem differentiable_canonicalFrameEvaluation (a : ℝˣ)
    (C : SpectralSectionFamily D.groupHaar p W) (g : H) :
    Differentiable ℂ (fun z : P' => canonicalJacquetMap a p z
      (spectralFrameKFiniteLift p W hW z (C.frameVector D hW z)) g) := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let A := spectralFrameSpace p W
  let : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le inf_le_left
  let k := Module.finrank ℂ A
  let b := Module.finBasis ℂ A
  let J (z : P') := (canonicalJacquetMap a p z).comp (spectralFrameKFiniteLift p W hW z)
  let C₀ := C.frameVector D hW
  have hCoord (i : Fin k) : Differentiable ℂ (fun z => b.equivFun (C₀ z) i) := by
    obtain ⟨n, x, c, hx⟩ := InductionStages.exists_eval_sum A (b.coord i)
    have he : (fun z => b.equivFun (C₀ z) i) = fun z => ∑ j : Fin n, c j * C.upperSection z (x j).val :=
      funext fun z => hx (C₀ z)
    rw [he]
    exact Differentiable.fun_sum fun j _ => (C.differentiable_section (x j).val).const_mul _
  have hValue (i : Fin k) : Differentiable ℂ (fun z => J z (b i) g) := by
    let φ := frameProfile (b i).val
    have hφ : IsCompactProfile p φ := isCompactProfile_frameProfile hW (b i).property
    have he (z : P') : J z (b i) = canonicalJacquetFamily a hφ z :=
      canonicalJacquetMap_standardSection a hφ z
    simp only [he]
    exact (canonicalJacquetFamily_properties a hφ).2.2.1 [] g
  have he (z : P') : J z (C₀ z) g = ∑ i, b.equivFun (C₀ z) i * J z (b i) g := by
    conv_lhs => rw [← b.sum_repr (C₀ z)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply]
  change Differentiable ℂ (fun z => J z (C₀ z) g)
  simp only [he]
  exact Differentiable.fun_sum fun i _ => (hCoord i).mul (hValue i)

private def smallerExponents (z : P') : P := fun i => z i.succ

private theorem differentiable_smallerExponents : Differentiable ℂ (smallerExponents (t := t)) :=
  differentiable_pi.mpr fun i => (ContinuousLinearMap.proj i.succ : P' →L[ℂ] ℂ).differentiable

private theorem smallerExponents_mem_chamber {z : P'} (hz : z ∈ realSpectralChamber (t + 1)) :
    smallerExponents z ∈ realSpectralChamber t := by
  intro i
  change (z i.succ.succ).re < (z i.castSucc.succ).re
  have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simpa only [he] using hz i.succ

private theorem growth_smallerExponents (F : P → G → ℂ) (hF : HasLocallyUniformDerivativeGrowth univ F) :
    HasLocallyUniformDerivativeGrowth univ (fun z : P' => F (smallerExponents z)) := by
  intro z _
  obtain ⟨δ, hδ, N, hN⟩ := hF (smallerExponents z) (mem_univ _)
  have hNear : ∀ᶠ q in 𝓝 z, smallerExponents q ∈ ball (smallerExponents z) δ :=
    differentiable_smallerExponents.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hδ)
  obtain ⟨ε, hε, hBall⟩ := Metric.eventually_nhds_iff_ball.mp hNear
  exact ⟨ε, hε, N, fun Xs => by
    obtain ⟨C, hC, h⟩ := hN Xs
    exact ⟨C, hC, fun q hq => h (smallerExponents q) (hBall q hq)⟩⟩

/-- For each fixed compact Godement generator the upper canonical evaluation is
the first-column value of the canonical lower coefficient at every exponent vector. -/
def RealGodementCanonicalColumnStatement (t : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin (t + 2) → Fin 2)
    (W : Submodule ℂ (unitaryCompact ℝ (t + 2) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ k : unitaryCompact ℝ (t + 2),
      (fun q : unitaryCompact ℝ (t + 2) => f (k * q)) ∈ W)
    (C : SpectralSectionFamily D.groupHaar p W) (z : Fin (t + 2) → ℂ)
    (g : Langlands.GeneralLinear (t + 2) ℝ),
    canonicalJacquetMap a p z (spectralFrameKFiniteLift p W hW z (C.frameVector D hW z)) g =
      godementLeadingFamily D a C.test
        (canonicalJacquetFamily a C.lower_profile (fun i => z i.succ)) (p 0) g (z 0)

theorem realGodementCanonicalColumn : RealGodementCanonicalColumnStatement t := by
  intro D a p W _ hW C z g
  let L (q : P') := canonicalJacquetMap a p q
    (spectralFrameKFiniteLift p W hW q (C.frameVector D hW q)) g
  let V := canonicalJacquetFamily a C.lower_profile
  let R (q : P') := godementLeadingFamily D a C.test (V (smallerExponents q)) (p 0) g (q 0)
  have hL : Differentiable ℂ L := differentiable_canonicalFrameEvaluation D hW a C g
  have hV := canonicalJacquetFamily_properties a C.lower_profile
  have hR : Differentiable ℂ R := differentiableOn_univ.mp (realGodementSpectralColumn D a C.test
    (p 0) univ isOpen_univ (fun q => V (smallerExponents q)) (fun q : P' => q 0)
    (fun q _ Xs => hV.1 (smallerExponents q) Xs)
    (fun h => ((hV.2.2.1 [] h).comp differentiable_smallerExponents).differentiableOn)
    (ContinuousLinearMap.proj 0 : P' →L[ℂ] ℂ).differentiable.differentiableOn
    (growth_smallerExponents V hV.2.1) g)
  change L z = R z
  apply congrFun (eq_of_differentiable_eqOn_open hL hR (isOpen_realSpectralChamber _)
    (realSpectralChamber_nonempty _) ?_) z
  intro q hq
  have hsmall := smallerExponents_mem_chamber hq
  let ds := characterList (fun i : Fin (t + 1) => p i.succ) (smallerExponents q)
  have hDom : IsStrictlyDominant (realPositionExponent ds) t := isStrictlyDominant_characterList _ hsmall
  have hLead : (realPositionExponent ds 0).re < (q 0).re := by
    rw [show realPositionExponent ds 0 = smallerExponents q 0 from realPositionExponent_characterList _ _ 0]
    exact hq (0 : Fin (t + 1))
  let f : principalSeries ℝ (t + 1) (realPositionCharacter ds) :=
    ⟨C.lowerSection q, (standardSection_mem C.lower_profile (smallerExponents q)).1.1⟩
  change canonicalJacquetMap a p q (spectralFrameKFiniteLift p W hW q (C.frameVector D hW q)) g =
    godementLeadingFamily D a C.test (canonicalJacquetFamily a C.lower_profile (smallerExponents q))
      (p 0) g (q 0)
  rw [canonicalJacquetMap_agrees a p hq, C.spectralFrameKFiniteLift_frameVector D hW,
    canonicalJacquetFamily_agrees a C.lower_profile hsmall]
  exact ((realGodementSmoothLeading t D a (p 0) ds f hDom C.support C.support_compact
    C.support_fullRank C.test C.test_zero g).2 (q 0) hLead).symm

end Columns

end Langlands.Global.RankinSelbergGlobal.RealGodement
