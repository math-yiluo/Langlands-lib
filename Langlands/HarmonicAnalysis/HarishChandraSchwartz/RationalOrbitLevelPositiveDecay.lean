import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelFiberBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCompactConstantTerm

/-! # Uniform level bounds for actual positive constant terms -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
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
  [hStab : Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ)
  {K₀ : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K₀ B)
  (hmem : ∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K')

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
local notation "Fixed" H => orbitSectionFixedCoefficients decomp K π H
set_option hygiene false in
local notation "fixedRestriction" => orbitSectionLevelFixedRestriction decomp K π νM coordinates
  closedU closedP hKc hnorm hprojection factorization
set_option hygiene false in
local notation "J'" => RationalPointFamily.rootSet i ν I'
set_option hygiene false in
local notation "incM" => minimalLeviInclusion hG hi hν J'
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "paramOrbit" => discreteSeriesOrbitMap C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "positiveTerm" => rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA
set_option hygiene false in
local notation "compactPositive" => rationalOrbitCompactPositiveConstantTerm hG hi hν I hKc hPK
  π C hC mu hsq I' hA hζ hB hmem

variable (N : Seminorm ℝ (RealTorusSpace.V S)) (W : standardLeviPoints i ν ∅ → ℝ)

/-- The positive term has a common exponential rate at each original section
level, with a finite supremum of original derivative seminorms. -/
def RationalOrbitLevelPositiveDecay : Prop :=
  ∀ (H : OpenSubgroup (rationalPoints G)), H ≤ K → ∀ δ > 0,
    ∃ ε > 0, ∃ t : Finset (List J × Module.Dual ℂ Picture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (ω : Oπ) (m : standardLeviPoints i ν ∅),
        m ∈ rationalPositivePartRegion hG hi hν N J' δ →
        ‖positiveTerm (includeLevel H q) ω (incM m)‖ ≤
          (c : ℝ) * (t.sup (inputSeminorms H)) q *
            (W m * Real.exp (-(ε * N (rationalMinimalH0 hG hi hν m))))

include hStab hζ hB hmem in
/-- Per-section VI.2.3 bounds imply one rate and a finite seminorm control
at each fixed input level. -/
theorem rationalOrbitLevelPositiveDecay_of_perSection (hW : ∀ m, 0 ≤ W m)
    (hdecay : ∀ ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
      HasRationalPositivePartDecay hG hi hν N J'
        (fun (ω : Oπ) m => positiveTerm ψ ω (incM m)) W) :
    RationalOrbitLevelPositiveDecay hG hi hν I hKc hPK π C hC mu hsq I' hA N W := by
  classical
  unfold HasRationalPositivePartDecay at hdecay
  intro H hHK δ hδ
  let := Finite.of_injective _ (unitaryClassStabilizerEquivDiscreteSeries νM π C hC mu hsq).injective
  let hcofinal : CompactOpenCofinal 𝐌 := compactOpenCofinal_of_isClosed
    (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
  let := finiteDimensional_orbitSectionFixedCoefficients decomp K π hKc hcofinal H hHK
  let b := Module.finBasis ℂ (Fixed H)
  let region := rationalPositivePartRegion hG hi hν N J' δ
  let height (m : standardLeviPoints i ν ∅) := N (rationalMinimalH0 hG hi hν m)
  let L (z : J → Circle) (m : standardLeviPoints i ν ∅) : (Fixed H) →ₗ[ℂ] ℂ :=
    ((LinearMap.proj (incM m)).comp (compactPositive z)).comp (Fixed H).subtype
  have hL (q : SectionLevel H) (z : J → Circle) (m : standardLeviPoints i ν ∅) :
      L z m (fixedRestriction H hHK q z) =
        positiveTerm (includeLevel H q) (paramOrbit ((coordinates).symm z)) (incM m) :=
    congrFun (rationalOrbitCompactPositiveConstantTerm_restriction hG hi hν I hKc hPK
      π C hC mu hsq I' hA hζ hB hmem (includeLevel H q) z) (incM m)
  have hsection (q : SectionLevel H) : ∃ ε > 0, ∃ c : ℝ≥0,
      ∀ z m, m ∈ region → ‖L z m (fixedRestriction H hHK q z)‖ ≤
        (c : ℝ) * W m * Real.exp (-(ε * height m)) := by
    let ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π := includeLevel H q
    have hp := hdecay ψ δ hδ
    let ε := hp.choose
    have hε := hp.choose_spec
    let c := hε.2.choose
    have hc := hε.2.choose_spec
    refine ⟨ε, hε.1, ⟨c, hc.1.le⟩, fun z m hm => ?_⟩
    exact (congrArg norm (hL q z m)).le.trans (hc.2 (paramOrbit ((coordinates).symm z)) m hm)
  have hgen := exists_finite_orbitSectionLevel_fiber_generators decomp closedU closedP K hKc
    factorization νM π hnorm hprojection coordinates H hHK b
  obtain ⟨ε, hε, c, hb⟩ := exists_uniform_fiber_basis_exponential_bound decomp closedU closedP K hKc
    factorization νM π hnorm hprojection coordinates H hHK b hgen L region W height
    (fun m _ => hW m) (fun m _ => apply_nonneg N _) hsection
  obtain ⟨t, d, hd⟩ := exists_levelFamily_bound_of_fixedBasis decomp closedU closedP K hKc factorization
    νM π hnorm hprojection coordinates H hHK b region (fun m => W m * Real.exp (-(ε * height m)))
    L c (fun i z m hm => (hb i z m hm).trans_eq (mul_assoc _ _ _))
  refine ⟨ε, hε, t, d, fun q ω m hm => ?_⟩
  obtain ⟨χ, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu νM
    (discreteSeriesClass C hC mu π hsq)).surjective ω
  let z := (coordinates) χ
  have he : (coordinates).symm z = χ := (coordinates).symm_apply_apply χ
  have hf : L z m (fixedRestriction H hHK q z) =
      positiveTerm (includeLevel H q) (paramOrbit χ) (incM m) :=
    (hL q z m).trans (congrArg (fun χ' => positiveTerm (includeLevel H q) (paramOrbit χ') (incM m)) he)
  exact (congrArg norm hf).ge.trans (hd q z m hm)

end Langlands.HarishChandraSchwartz
