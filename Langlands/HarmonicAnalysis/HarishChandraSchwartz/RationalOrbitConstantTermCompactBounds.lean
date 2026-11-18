import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermPointwiseBound

/-! # Compact weighted bounds for the actual full orbit constant terms -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

/-- Common invariance under one open subgroup upgrades fixed-point family
bounds to compact weighted bounds against every positive continuous weight.
The family parameter requires no topology. -/
theorem hasUniformWeightedCompactBounds_of_pointwise_uniformRightInvariant
    {κ M : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    {F : κ → M → ℂ} {B : M → ℝ}
    (U : OpenSubgroup M)
    (hinv : ∀ ω m k, k ∈ U → F ω (m * k) = F ω m)
    (hpoint : HasUniformPointwiseNormBounds F)
    (hB : Continuous B) (hBpos : ∀ m, 0 < B m) :
    HasUniformWeightedCompactBounds F B := by
  classical
  choose c hc0 hc using hpoint
  intro Q hQ
  let V : M → Set M := fun m => {g | m⁻¹ * g ∈ U}
  have hV : ∀ m, IsOpen (V m) :=
    fun m => U.isOpen.preimage (continuous_const.mul continuous_id)
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover V hV (fun g _ =>
    Set.mem_iUnion.mpr ⟨g, by simp only [V, Set.mem_ofPred_eq, inv_mul_cancel, OneMemClass.one_mem]⟩)
  let b : ℝ := 1 + ∑ m ∈ s, c m
  have hb0 : 0 < b := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun m _ => (hc0 m).le)
  have hb : ∀ ω g, g ∈ Q → ‖F ω g‖ ≤ b := by
    intro ω g hg
    obtain ⟨m, hm, hgm⟩ := Set.mem_iUnion₂.mp (hs hg)
    have hfg : F ω g = F ω m := by
      simpa only [mul_inv_cancel_left] using hinv ω m (m⁻¹ * g) hgm
    calc
      ‖F ω g‖ ≤ c m := by rw [hfg]; exact hc m ω
      _ ≤ ∑ x ∈ s, c x := Finset.single_le_sum (fun x _ => (hc0 x).le) hm
      _ ≤ b := le_add_of_nonneg_left zero_le_one
  have hw : Continuous (fun g => (1 : ℝ) / B g) :=
    continuous_const.div hB (fun g => (hBpos g).ne')
  obtain ⟨A, hA⟩ := hQ.bddAbove_image hw.continuousOn
  refine ⟨b * max A 1, mul_pos hb0 (zero_lt_one.trans_le (le_max_right _ _)), fun ω g hg => ?_⟩
  have hwg : 1 ≤ max A 1 * B g :=
    (div_le_iff₀ (hBpos g)).mp ((hA ⟨g, hg, rfl⟩).trans (le_max_left _ _))
  exact (hb ω g hg).trans (by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hwg hb0.le)

end Langlands.HarishChandraSchwartz

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- Uniform compact bounds for the chosen full orbit constant terms, weighted
by the actual target Levi Xi. -/
abbrev HasRationalOrbitConstantTermCompactBounds
    (hM' : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))))
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) : Prop :=
  HasUniformWeightedCompactBounds
    (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ)
    (rationalLeviXi hKc hM')

include hζ hB hmem in
/-- The actual full chosen orbit constant terms satisfy uniform compact
bounds against the original actual Levi Xi, using only their original
structural data. No parameter-continuity premise for these constant terms
is imposed. -/
theorem rationalOrbitConstantTerm_uniformWeightedCompactBounds
    (hM' : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))))
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    HasRationalOrbitConstantTermCompactBounds hG hi hν I J hKc hPK hA π C hC mu hsq hM' Φ := by
  obtain ⟨U, hU⟩ := rationalOrbitConstantTerm_hasUniformRightInvariance
    hG hi hν I hKc hPK π C hC mu hsq J hA hζ Φ
  exact hasUniformWeightedCompactBounds_of_pointwise_uniformRightInvariant U hU
    (rationalOrbitConstantTerm_pointwise_bound
      hG hi hν I J hKc hPK hA hζ hB hmem π C hC mu hsq Φ)
    (continuous_rationalLeviXi hG hi hν (RationalPointFamily.rootSet_subset i ν J)
      K.isOpen hKc hM')
    (rationalLeviXi_pos K.isOpen hKc hG hi hν (RationalPointFamily.rootSet_subset i ν J) hM')

end Langlands.HarishChandraSchwartz
