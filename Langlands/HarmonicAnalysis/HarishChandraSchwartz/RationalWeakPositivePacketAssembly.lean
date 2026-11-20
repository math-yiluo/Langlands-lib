import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitLevelConstantTermThreshold
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitLevelPositiveRapid

/-! # Assembling the normalized packet from its weak and positive terms -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory
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
local notation "modulus" => fun m => standardHalfModulus i ν J' (incM m)

variable (N : Seminorm ℝ (RealTorusSpace.V S)) {n : ℕ} [Nonempty (Fin n)]
  (ρ : MatrixRepresentation G (Fin n))

variable [Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  (rhoX : Measure (unitaryUnramifiedCharacters νM)) (w : Oπ → ℂ)

set_option hygiene false in
local notation "dO" => discreteSeriesOrbitMeasure νM C hC mu (discreteSeriesClass C hC mu π hsq) rhoX
set_option hygiene false in
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
set_option hygiene false in
local notation "fullTerm" => rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
set_option hygiene false in
local notation "coefficient" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq
set_option hygiene false in
local notation "packet" => rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq rhoX w
set_option hygiene false in
local notation "kernel[" r ", " m "]" => rationalXi hKc hPK m * (1 + rationalHeight (F := F) ρ m) ^ (-r)

/-- The remaining weighted weak integral estimate includes its pointwise
integrability and the original finite seminorms at every fixed level. -/
def RationalOrbitLevelWeakPacketRapid : Prop :=
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ r : ℝ,
    ∃ t : Finset (List J × Module.Dual ℂ Picture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (m : standardLeviPoints i ν ∅),
        m ∈ rationalMinimalClosedChamber hG hi hν →
        Integrable (fun ω => w ω * weakTerm (includeLevel H q) ω (incM m)) dO ∧
        ‖(modulus) m * ∫ ω, w ω * weakTerm (includeLevel H q) ω (incM m) ∂dO‖ ≤
          (c : ℝ) * (t.sup (inputSeminorms H)) q * kernel[r, m]

/-- The actual norm bound on the intersection of the two regions of the
selected parabolic, with one threshold at the given section level. -/
def RationalOrbitLevelProperPacketRapid : Prop :=
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ δ > 0, ∀ r : ℝ,
    ∃ t > 0, ∃ F₀ : Finset (List J × Module.Dual ℂ Picture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (m : standardLeviPoints i ν ∅),
        m ∈ rationalConstantTermThresholdRegion hG hi hν J' t →
        m ∈ rationalPositivePartRegion hG hi hν N J' δ →
        ‖packet (includeLevel H q) m‖ ≤ (c : ℝ) * (F₀.sup (inputSeminorms H)) q * kernel[r, m]

/-- On the threshold region the actual weighted coefficient decomposes into
integrable weak and positive terms. The two full-height estimates give the
original packet bound with the union of their finite sets of seminorms. -/
theorem rationalOrbitLevelProperPacketRapid_of_weak_positive
    (hw : Integrable w dO)
    (hpacketInt : ∀ (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
      (g : rationalPoints G), Integrable (fun ω => w ω * coefficient ψ ω g) dO)
    (hthreshold : RationalOrbitLevelConstantTermThreshold hG hi hν I hKc hPK π C hC mu hsq I' hA)
    (hpositive : RationalOrbitLevelPositiveRapid hG hi hν I hKc hPK π C hC mu hsq I' hA N ρ)
    (hweak : RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' hA ρ rhoX w) :
    RationalOrbitLevelProperPacketRapid hG hi hν I hKc hPK π C hC mu hsq I' N ρ rhoX w := by
  classical
  intro H hHK δ hδ r
  obtain ⟨t, ht, hCT⟩ := hthreshold H hHK
  obtain ⟨p, cp, hpos⟩ := hpositive H hHK δ hδ r
  obtain ⟨a, ca, hweak⟩ := hweak H hHK r
  let d : ℝ≥0 := ⟨∫ ω, ‖w ω‖ ∂dO, integral_nonneg fun ω => norm_nonneg (w ω)⟩
  let F₀ := a ∪ p
  let c := ca + cp * d
  refine ⟨t, ht, F₀, c, fun q m hm hregion => ?_⟩
  let ψ := includeLevel H q
  let E : Oπ → ℂ := fun ω => w ω * coefficient ψ ω m
  let A : Oπ → ℂ := fun ω => w ω * weakTerm ψ ω (incM m)
  let B : Oπ → ℂ := fun ω => w ω * ((modulus) m * positiveTerm ψ ω (incM m))
  let D : Oπ → ℂ := fun ω => (modulus) m * A ω
  have hE : Integrable E dO := hpacketInt ψ m
  obtain ⟨hAint, hAnorm⟩ := hweak q m hm.1
  have hD : Integrable D dO := hAint.const_mul ((modulus) m)
  have hsplit (ω : Oπ) : E ω = D ω + B ω := by
    have eCT := hCT q ω m hm
    have eParts := congrFun (rationalOrbitWeakConstantTerm_add_positive hG hi hν I hKc hPK
      π C hC mu hsq I' hA ψ ω) (incM m)
    calc
      E ω = w ω * ((modulus) m * fullTerm ψ ω (incM m)) := congrArg (w ω * ·) eCT
      _ = w ω * ((modulus) m * (weakTerm ψ ω (incM m) + positiveTerm ψ ω (incM m))) :=
        congrArg (fun z : ℂ => w ω * ((modulus) m * z)) eParts.symm
      _ = D ω + B ω := by dsimp [D, A, B]; ring
  have hB : Integrable B dO := (hE.sub hD).congr (Filter.Eventually.of_forall fun ω => by
    change E ω - D ω = B ω
    rw [hsplit, add_sub_cancel_left])
  have hpacket : packet ψ m = (∫ ω, D ω ∂dO) + ∫ ω, B ω ∂dO := by
    rw [rationalInducedOrbitWavePacket_apply]
    exact (integral_congr_ae (Filter.Eventually.of_forall hsplit)).trans (integral_add hD hB)
  have hDnorm : ‖∫ ω, D ω ∂dO‖ ≤ (ca : ℝ) * (a.sup (inputSeminorms H)) q * kernel[r, m] := by
    rw [show D = (fun ω => (modulus) m * A ω) from rfl, integral_const_mul]
    exact hAnorm
  let P : ℝ := (cp : ℝ) * (p.sup (inputSeminorms H)) q * kernel[r, m]
  have hBnorm : ‖∫ ω, B ω ∂dO‖ ≤ P * (d : ℝ) := by
    calc
      ‖∫ ω, B ω ∂dO‖ ≤ ∫ ω, ‖w ω‖ * P ∂dO := by
        refine norm_integral_le_of_norm_le (hw.norm.mul_const P) (Filter.Eventually.of_forall fun ω => ?_)
        exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hpos q ω m hregion) (norm_nonneg _))
      _ = _ := by rw [integral_mul_const, mul_comm]; rfl
  have hk0 : 0 ≤ kernel[r, m] := mul_nonneg (rationalXi_nonneg hKc hPK _)
    (Real.rpow_nonneg (by linarith [rationalHeight_nonneg ρ (m : rationalPoints G)]) _)
  have haF : a.sup (inputSeminorms H) ≤ F₀.sup (inputSeminorms H) :=
    Finset.sup_mono Finset.subset_union_left
  have hpF : p.sup (inputSeminorms H) ≤ F₀.sup (inputSeminorms H) :=
    Finset.sup_mono Finset.subset_union_right
  change ‖packet ψ m‖ ≤ _
  rw [hpacket]
  refine (norm_add_le _ _).trans ((add_le_add hDnorm hBnorm).trans ?_)
  calc
    _ ≤ (ca : ℝ) * (F₀.sup (inputSeminorms H)) q * kernel[r, m] +
        ((cp : ℝ) * (F₀.sup (inputSeminorms H)) q * kernel[r, m]) * (d : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (haF q) ca.coe_nonneg) hk0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpF q) cp.coe_nonneg) hk0) d.coe_nonneg)
    _ = _ := by
      change _ = ((ca : ℝ) + (cp : ℝ) * (d : ℝ)) * (F₀.sup (inputSeminorms H)) q * kernel[r, m]
      ring

end Langlands.HarishChandraSchwartz
