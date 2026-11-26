import Langlands.Global.AdelicCuspidalPairingConvolution
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicNormOneCuspidalDecay

/-! # Integrable bounds for actual norm-one Levi cusp tests -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "A₁" => normOneSubgroup F M
local notation "Γ" => rationalNormOneSubgroup F M
local notation "Q" => NormOneRationalQuotient F M
local notation "dM" => normOneRationalQuotientHaarMeasure F M
local notation "j" => (fam.l J ≫ fam.p J)
local notation "ι" => AdelicGroupPoints.map F M G j
local notation "H" => adelicHeight F G rho

/-- A cusp test has bounded weighted values on suitable representatives of every
norm-one Levi class, for each nonnegative real exponent of the ambient height. -/
def HasWeightedLeviTestBound (ψ : AdelicGroupPoints F M → ℂ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Q, ∃ m : A₁,
    LeftCosetSpace.mk Γ m = q ∧ H (ι m.val) ^ r * ‖ψ m.val‖ ≤ B

/-- At a maximal infinite Levi compact, the actual Levi cusp tests satisfy all
the weighted bounds on norm-one representatives. -/
theorem IsLeviCuspForm.hasWeightedLeviTestBound
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hK : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf J))
    (hN : 0 < N) (hρ : IsClosedSubgroup rho) {ψ : AdelicGroupPoints F M → ℂ}
    (hψ : fam.IsLeviCuspForm Kinf rho J ψ) :
    fam.HasWeightedLeviTestBound J rho ψ := by
  have hM := (fam.isCompatible J).levi.isConnectedReductive
  let : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
  have hρM : IsClosedSubgroup (j ≫ rho) :=
    ((fam.isCompatible J).levi.isClosedSubgroup.comp
      (fam.isCompatible J).parabolic.isClosedSubgroup).comp hρ
  have hdecay := hasRapidDecayOnNormOneRepresentatives_of_cuspidal
    (j ≫ rho) hM hN hρM (fam.leviSmooth J) hK hψ.1 hψ.2
  intro r _
  obtain ⟨n, hn⟩ := exists_nat_ge r
  obtain ⟨B, hB, hrep⟩ := hdecay n
  refine ⟨B, hB, fun q => ?_⟩
  obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  obtain ⟨x, hx⟩ := hrep m
  let y : Γ := ⟨rationalNormOne F M x, ⟨x, rfl⟩⟩
  refine ⟨y.val * m, LeftCosetSpace.mk_subgroup_mul Γ y m, ?_⟩
  change H (ι (rational F M x * m.val)) ^ r * ‖ψ (rational F M x * m.val)‖ ≤ B
  let z := rational F M x * m.val
  have hh : adelicHeight F M (j ≫ rho) z = H (ι z) := by
    unfold adelicHeight
    congr 1
  change H (ι z) ^ r * ‖ψ z‖ ≤ B
  have hpowers : H (ι z) ^ r ≤ H (ι z) ^ n := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hN (ι z)) hn
  calc
    _ ≤ H (ι z) ^ n * ‖ψ z‖ := mul_le_mul_of_nonneg_right hpowers (norm_nonneg _)
    _ = ‖ψ z‖ * adelicHeight F M (j ≫ rho) z ^ n := by rw [hh, mul_comm]
    _ ≤ B := hx

/-- A weighted representative bound controls a moderate function
in the Levi pairing, uniformly for compact right translations. -/
theorem HasWeightedLeviTestBound.compactPairingMajorant
    (hN : 0 < N) {ψ : AdelicGroupPoints F M → ℂ} (hψ : fam.HasWeightedLeviTestBound J rho ψ)
    (hψinv : IsLeftInvariantUnder F M (rationalSubgroup F M) ψ) {f : A → ℂ}
    (hf : HasModerateGrowthFunction F G rho f)
    (hfinv : IsLeftInvariantUnder F G (rationalImage F j) f)
    (g : A) {C : Set A} (hC : IsCompact C) :
    fam.HasCompactLeviPairingMajorant J f ψ g C := by
  obtain ⟨B, r, hB, hr, hfg⟩ := (hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hf
  obtain ⟨D, _, hrep⟩ := hψ r hr
  obtain ⟨E, hE⟩ := ((hC.image (continuous_adelicHeight F G rho hN)).bddAbove)
  let L := H g * max 1 E
  have hpos (a : A) : 0 ≤ H a := zero_le_one.trans (one_le_adelicHeight F G rho hN a)
  have hL : 0 ≤ L := mul_nonneg (hpos g) (zero_le_one.trans (le_max_left _ _))
  have hgt (t : A) (ht : t ∈ C) : H (g * t) ≤ L :=
    (adelicHeight_mul_le F G rho hN g t).trans (mul_le_mul_of_nonneg_left
      ((hE ⟨t, ht, rfl⟩).trans (le_max_right _ _)) (hpos g))
  let : IsFiniteMeasure dM :=
    connectedReductiveFiniteVolume F M (fam.isCompatible J).levi.isConnectedReductive
  refine ⟨fun _ => B * L ^ r * D, integrable_const _, Filter.Eventually.of_forall (fun q => ?_)⟩
  obtain ⟨m, hm, hbound⟩ := hrep q
  intro t ht
  rw [← hm, fam.leviPairingIntegrand_mk_of_leviInvariant J
    (fun x a => hfinv _ ⟨x, rfl⟩ a) hψinv, norm_mul, Complex.norm_conj]
  have hmultiplicative : H (ι m.val * (g * t)) ^ r ≤ H (ι m.val) ^ r * L ^ r := by
    rw [← Real.mul_rpow (hpos _) hL]
    apply Real.rpow_le_rpow (hpos _) _ hr
    exact (adelicHeight_mul_le F G rho hN _ _).trans
      (mul_le_mul_of_nonneg_left (hgt t ht) (hpos _))
  calc
    _ ≤ (B * H (ι m.val * (g * t)) ^ r) * ‖ψ m.val‖ :=
      mul_le_mul_of_nonneg_right (hfg _) (norm_nonneg _)
    _ ≤ (B * (H (ι m.val) ^ r * L ^ r)) * ‖ψ m.val‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmultiplicative hB) (norm_nonneg _)
    _ = (B * L ^ r) * (H (ι m.val) ^ r * ‖ψ m.val‖) := by ring
    _ ≤ B * L ^ r * D := mul_le_mul_of_nonneg_left hbound
      (mul_nonneg hB (Real.rpow_nonneg hL _))

/-- The pairing of a convolved moderate function against an actual cusp form
is absolutely integrable and equals the convolution of the scalar pairings. -/
theorem leviPairing_rightConvolution_of_cuspForm
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hK : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf J))
    (hN : 0 < N) (hρ : IsClosedSubgroup rho) {h f : A → ℂ} (hh : Continuous h)
    (hcomp : HasCompactSupport h) (hfc : Continuous f)
    (hf : HasModerateGrowthFunction F G rho f) (hfinv : IsLeftInvariantUnder F G (rationalImage F j) f)
    {ψ : AdelicGroupPoints F M → ℂ} (hψ : fam.IsLeviCuspForm Kinf rho J ψ) (g : A) :
    Integrable (fam.leviPairingIntegrand J (rightConvolution F G h f) g ψ) dM ∧
      fam.leviPairing J (rightConvolution F G h f) g ψ =
        rightConvolution F G h (fun x => fam.leviPairing J f x ψ) g := by
  apply fam.leviPairing_rightConvolution_of_compactMajorant J hh hcomp hfc hψ.1.2.1.1
    (fun x a => hfinv _ ⟨x, rfl⟩ a) hψ.1.1 g
  exact HasWeightedLeviTestBound.compactPairingMajorant fam J rho hN
    (IsLeviCuspForm.hasWeightedLeviTestBound fam J rho hK hN hρ hψ) hψ.1.1 hf hfinv
      g hcomp.isCompact

/-- Right convolution by a continuous compactly supported kernel preserves the
cuspidal annihilator on moderate functions invariant under the rational Levi. -/
theorem InCuspidalAnnihilator.rightConvolution_of_moderate
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hK : Langlands.CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf J))
    (hN : 0 < N) (hρ : IsClosedSubgroup rho) {h f : A → ℂ} (hh : Continuous h)
    (hcomp : HasCompactSupport h) (hfc : Continuous f)
    (hf : HasModerateGrowthFunction F G rho f) (hfinv : IsLeftInvariantUnder F G (rationalImage F j) f)
    (hkill : fam.InCuspidalAnnihilator Kinf rho J f) :
    fam.InCuspidalAnnihilator Kinf rho J (rightConvolution F G h f) := by
  apply InCuspidalAnnihilator.rightConvolution_of_compactMajorants fam J rho Kinf hh hcomp hfc
    (fun x a => hfinv _ ⟨x, rfl⟩ a) hkill
  intro ψ hψ g
  exact HasWeightedLeviTestBound.compactPairingMajorant fam J rho hN
    (IsLeviCuspForm.hasWeightedLeviTestBound fam J rho hK hN hρ hψ) hψ.1.1 hf hfinv
      g hcomp.isCompact

end Langlands.Global.StandardParabolicFamily
