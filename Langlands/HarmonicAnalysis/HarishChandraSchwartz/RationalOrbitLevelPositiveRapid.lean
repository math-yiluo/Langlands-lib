import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitLevelPositiveDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiHalfModulusComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientRapidDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.BoundedCartanPacketControl

/-! # Full-height rapid decay for the actual positive constant term -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I

set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)

set_option hygiene false in
local notation "closedP" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "factorization" => factorization_subtype
  (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "hnorm" => RationalPointFamily.continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "hprojection" => continuous_projection_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I) decomp
set_option hygiene false in
local notation "coordinates" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
set_option hygiene false in
local notation "J" => Fin (rationalImageRank (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)))

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

variable (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)
  (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I'))))

set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture decomp K π.obj
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel νM π coordinates decomp closedU K closedP hKc
  hnorm hprojection factorization
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections νM π coordinates decomp closedU K closedP
  hKc hnorm hprojection factorization
set_option hygiene false in
local notation "inputSeminorms" => OrbitSectionLevel.seminormFamily νM π coordinates decomp closedU K
  closedP hKc hnorm hprojection factorization
set_option hygiene false in
local notation "J'" => RationalPointFamily.rootSet i ν I'
set_option hygiene false in
local notation "incM" => minimalLeviInclusion hG hi hν J'
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "positiveTerm" => rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
set_option hygiene false in
local notation "leviXi" => fun m => rationalLeviXi hKc hMK (incM m)
set_option hygiene false in
local notation "modulus" => fun m => standardHalfModulus i ν J' (incM m)

variable (N : Seminorm ℝ (RealTorusSpace.V S)) {n : ℕ} [Nonempty (Fin n)]
  (ρ : MatrixRepresentation G (Fin n))

/-- A finite derivative estimate for the half-modulus-scaled positive term,
with the ambient Xi and the full matrix height at every real order. -/
def RationalOrbitLevelPositiveRapid : Prop :=
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ δ > 0, ∀ r : ℝ,
    ∃ t : Finset (List J × Module.Dual ℂ Picture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (ω : Oπ) (m : standardLeviPoints i ν ∅),
        m ∈ rationalPositivePartRegion hG hi hν N J' δ →
        ‖(modulus) m * positiveTerm (includeLevel H q) ω (incM m)‖ ≤
          (c : ℝ) * (t.sup (inputSeminorms H)) q *
            (rationalXi hKc hPK m * (1 + rationalHeight (F := F) ρ m) ^ (-r))

/-- At a fixed level the exponential estimate implies rapid decay at every
real order, by the actual chamber height and spherical comparisons. -/
theorem rationalOrbitLevelPositiveRapid_of_exponential
    {K₀ : Subgroup (rationalPoints G)} (hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K₀)
    (hcover : StandardLeviCartanCovering F i ν ∅ K₀)
    (hN : ∀ v, N v = 0 → v = 0)
    (hdecay : RationalOrbitLevelPositiveDecay hG hi hν I hKc hPK π C hC mu hsq I' hA N leviXi) :
    RationalOrbitLevelPositiveRapid hG hi hν I hKc hPK π C hC mu hsq I' hA N ρ := by
  classical
  obtain ⟨B, hB, hXi⟩ := hasRationalLeviXiHalfModulusComparison_of_basis hG hi hν
    (RationalPointFamily.rootSet_subset i ν I') K.isOpen hKc hPK hMK hK₀ hbasis hcover
  obtain ⟨D₀, hD₀, hheight⟩ := hasMinimalLeviHeightComparison_of_cartanCovering
    hG hi hν hK₀ hcover N hN ρ
  let D := max 1 D₀
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  intro H hHK δ hδ r
  let s := max r 0
  obtain ⟨ε, hε, t, c, hb⟩ := hdecay H hHK δ hδ
  obtain ⟨E, hE, hExp⟩ := exists_exp_neg_le_rpow hε s
  let c₀ : ℝ≥0 := c * ⟨B, hB.le⟩ * ⟨E, hE⟩
  let S₀ := t.sup (inputSeminorms H)
  let P : ℝ → Seminorm ℂ (SectionLevel H) := fun _ => c₀ • S₀
  have hP (q : SectionLevel H) : P s q = (c₀ : ℝ) * S₀ q := rfl
  refine ⟨t, Real.toNNReal (D ^ s) * c₀, fun q ω m hm => ?_⟩
  let τ (m : standardLeviPoints i ν ∅) := N (rationalMinimalH0 hG hi hν m)
  let ξ (m : standardLeviPoints i ν ∅) := rationalXi hKc hPK m
  let σ (m : standardLeviPoints i ν ∅) := rationalHeight (F := F) ρ m
  let f (q : SectionLevel H) (m : standardLeviPoints i ν ∅) :=
    (modulus) m * positiveTerm (includeLevel H q) ω (incM m)
  have hτ : 0 ≤ τ m := apply_nonneg N _
  have hξ : 0 ≤ ξ m := rationalXi_nonneg hKc hPK _
  have hσ : 0 ≤ σ m := rationalHeight_nonneg ρ _
  have hcS : 0 ≤ (c : ℝ) * S₀ q := mul_nonneg c.coe_nonneg (apply_nonneg _ _)
  have hcompare : 1 + σ m ≤ D * (1 + τ m) := (hheight m).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hpoint : ‖f q m‖ ≤ P s q * ξ m * (1 + τ m) ^ (-s) := by
    calc
      ‖f q m‖ = ‖(modulus) m‖ * ‖positiveTerm (includeLevel H q) ω (incM m)‖ := norm_mul _ _
      _ ≤ ‖(modulus) m‖ * ((c : ℝ) * S₀ q * ((leviXi) m * Real.exp (-(ε * τ m)))) :=
        mul_le_mul_of_nonneg_left (hb q ω m hm) (norm_nonneg _)
      _ = ((c : ℝ) * S₀ q) * ((‖(modulus) m‖ * (leviXi) m) * Real.exp (-(ε * τ m))) := by ring
      _ ≤ ((c : ℝ) * S₀ q) * ((B * ξ m) * Real.exp (-(ε * τ m))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hXi m hm.1) (Real.exp_nonneg _)) hcS
      _ ≤ ((c : ℝ) * S₀ q) * ((B * ξ m) * (E * (1 + τ m) ^ (-s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hExp (τ m) hτ)
          (mul_nonneg hB.le hξ)) hcS
      _ = _ := by
        rw [hP]
        change _ = ((c : ℝ) * B * E) * S₀ q * ξ m * (1 + τ m) ^ (-s)
        ring
  have hb' := norm_le_heightComparisonSeminorm P f ξ σ τ hD r q m hξ hσ hτ hcompare hpoint
  rw [heightComparisonSeminorm_apply P hD0 r q, hP] at hb'
  simpa only [f, ξ, σ, s, NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hD0 _),
    ← mul_assoc] using hb'

end Langlands.HarishChandraSchwartz
