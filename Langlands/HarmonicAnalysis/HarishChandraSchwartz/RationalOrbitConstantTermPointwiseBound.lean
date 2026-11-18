import Langlands.Representation.Jacquet.StandardInducedTranslatedRay
import Langlands.Representation.Jacquet.StandardUnitaryConstantTermTailBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitUniformAnnihilators

/-! # Uniform fixed-point bounds for the actual full orbit constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- At each point there is a positive norm bound for the entire family. -/
abbrev HasUniformPointwiseNormBounds {κ M : Type*} (f : κ → M → ℂ) : Prop :=
  ∀ m, ∃ c > 0, ∀ ω, ‖f ω m‖ ≤ c

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

include hKc hPK hmem hζ hB in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Shared bi-invariance and fixed-point bounds for the original unitary
coefficient functions imply fixed-point bounds for their actual chosen full
constant terms. No parameter continuity of the constant terms is required. -/
theorem exists_standardUnitaryConstantTerm_pointwise_bound
    {κ : Type*}
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible)
    (ψ : κ → unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I))
    (hψ : ∀ ω m, ‖((ψ ω).val m : ℂ)‖ = 1)
    (t : ∀ ω, CoefficientTensor (standardUnramifiedInducedObject hG hi hν I τ (ψ ω)))
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G)))
    (hinv : ∀ ω (k l : H) g,
      coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ (ψ ω)) (t ω)
        ((k : rationalPoints G) * g * (l : rationalPoints G)) =
      coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ (ψ ω)) (t ω) g)
    (hpoint : ∀ g : rationalPoints G, ∃ c : ℝ, ∀ ω,
      ‖coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ (ψ ω)) (t ω) g‖ ≤ c)
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)) :
    ∃ c > 0, ∀ ω,
      ‖standardConstantTerm hA
        (fun g => coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ (ψ ω))
          (t ω) g) m‖ ≤ c := by
  classical
  let Vψ := fun ω => standardUnramifiedInducedObject hG hi hν I τ (ψ ω)
  let CT := fun ω => standardConstantTerm hA (fun g => coefficientTensorMap (Vψ ω) (t ω) g)
  let aM := (hA.centralStrictElement i ν hi hζ :
    standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))
  obtain ⟨a, _, ha⟩ := (hA.strictElement_spec i ν hi hζ).2.1
  have haM : standardComponentHom hA a = aM := Subtype.ext ha
  obtain ⟨L, hLB, hLH⟩ := hB.2.mem_iff.mp H.mem_nhds_one
  let Lop := basisOpenSubgroup hB hLB
  have hLc : IsCompact (Lop : Set (rationalPoints G)) := (hB.1 L hLB).2.2.2
  have hCTinv : ∀ ω
      (k : Lop.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
        continuous_subtype_val) (y : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)),
      CT ω (y * k) = CT ω y := by
    intro ω k y
    exact standardConstantTerm_mul_right_eq_of_invariance hA hi hζ hH
      (fun g z hz => by
        simpa only [OneMemClass.coe_one, one_mul] using hinv ω (1 : H) ⟨z, hz⟩ g)
      y k (hLH k.property)
  obtain ⟨D, hD, htail⟩ := exists_standardUnitaryConstantTerm_tail_bound
    hG hi hν I J hA hKc hPK τ hτirr hτadm Lop hLc (hmem L hLB) hB hmem a
  let Hm := H ⊓ Jacquet.conjOpenSubgroup (m : rationalPoints G)⁻¹ H
  obtain ⟨L', hL'B, hL'Hm⟩ := hB.2.mem_iff.mp Hm.mem_nhds_one
  let L'op := basisOpenSubgroup hB hL'B
  let r := standardInducedFixedOrder hG hi hν I τ L'op
  have htranslated : ∀ ω (n : ℕ), r ≤ n →
      coefficientTensorMap (Vψ ω) (t ω)
        ((m * aM ^ n : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)) :
          rationalPoints G) =
      standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) (m * aM ^ n) *
        CT ω (m * aM ^ n) := by
    intro ω n hn
    apply standardUnramifiedConstantTerm_mul_ray_threshold hG hi hν I J hKc hPK
      hA hζ hB hmem τ hτadm hL'B (ψ ω) (t ω) m ?_ hn
    exact biInvariant_mul_left_of_le_conj (hinv ω) (m : rationalPoints G)
      (fun z hz => (hL'Hm hz).1) (fun z hz => (hL'Hm hz).2)
  choose c hc using hpoint
  let d := standardInducedFixedOrder hG hi hν I τ Lop
  let b : ℕ → ℝ := fun n =>
    c ((m * aM ^ (r + n) : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)) :
      rationalPoints G) /
    ‖standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) (m * aM ^ (r + n))‖
  have hfuture : ∀ ω n, ‖CT ω (m * aM ^ (r + n))‖ ≤ b n := by
    intro ω n
    apply (le_div_iff₀
      (norm_pos_iff.mpr (standardHalfModulus_ne_zero (m * aM ^ (r + n))))).mpr
    have heq := htranslated ω (r + n) (Nat.le_add_right r n)
    have hb := hc ((m * aM ^ (r + n) :
      standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)) : rationalPoints G) ω
    rw [heq, norm_mul] at hb
    exact (mul_comm _ _).trans_le hb
  let bound := D ^ r * ∑ n ∈ Finset.range (r * (d * d) + 1), b n
  refine ⟨max bound 1, zero_lt_one.trans_le (le_max_right _ _), fun ω => ?_⟩
  have h := htail (ψ ω) (hψ ω) (t ω) (hCTinv ω) r m
  rw [haM] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun n _ => hfuture ω n) (pow_nonneg hD.le _)).trans (le_max_left _ _))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

include hζ hB hmem in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- At every fixed actual Levi point, the chosen full constant terms of
the original induced orbit section have a common positive bound over the
entire unitary orbit. This follows from continuity of the original orbit
coefficients and does not assume continuity of their constant terms. -/
theorem rationalOrbitConstantTerm_pointwise_bound
    (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    HasUniformPointwiseNormBounds
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ) := by
  intro m
  classical
  let νM := RationalPointFamily.leviRationalNormCharacters i ν I
  let : CompactSpace (unitaryUnramifiedCharacters νM) :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  let := compactSpace_discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
  choose χ hχ using fun ω : 𝒪 =>
    unitaryOrbitTwistRepresentative_surjective νM π C hC mu hsq ω
  let ψ := fun ω => unitaryUnramifiedInclusion νM (χ ω)
  have hψ : ∀ ω m, ‖((ψ ω).val m : ℂ)‖ = 1 := fun ω => (χ ω).property.2
  let R := fun ω => unitaryOrbitTwistRepresentative νM π (χ ω)
  have hrep (ω : 𝒪) : unitaryOrbitRepresentativeDiscreteSeriesOrbit νM π C hC mu hsq (R ω) = ω :=
    hχ ω
  have hf (ω : 𝒪) :
      rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ ω =
        rationalInducedCoefficientMap hG hi hν I hKc hPK
          (R ω).val.obj (R ω).val.property.2 (Φ.val (R ω)) := by
    have hh := rationalInducedOrbitCoefficientMap_representative
      hG hi hν I hKc hPK π C hC mu hsq Φ (R ω)
    rw [hrep ω] at hh
    exact hh
  have ht : ∀ ω : 𝒪,
      ∃ t : CoefficientTensor (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω)),
        coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I π.obj (ψ ω)) t =
          rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ ω := by
    intro ω
    have hrange :
        rationalInducedCoefficientMap hG hi hν I hKc hPK
            (R ω).val.obj (R ω).val.property.2 (Φ.val (R ω)) ∈
          LinearMap.range (normalizedCoefficientMap
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
            (R ω).val.obj) := by
      rw [← range_rationalInducedCoefficientMap hG hi hν I hKc hPK
        (R ω).val.obj (R ω).val.property.2]
      exact LinearMap.mem_range_self _ _
    obtain ⟨t, ht⟩ := hrange
    exact ⟨t, ht.trans (hf ω).symm⟩
  choose t ht using ht
  obtain ⟨H, _, hH, hfix⟩ :=
    rationalInducedOrbitCoefficientMap_hasUniformBiInvariance
      hG hi hν I hKc hPK π C hC mu hsq Φ
  have hpoint : ∀ g : rationalPoints G, ∃ c : ℝ, ∀ ω : 𝒪,
      ‖rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq Φ ω g‖ ≤ c := by
    intro g
    obtain ⟨c, hc⟩ := isCompact_univ.bddAbove_image
      ((continuous_rationalInducedOrbitCoefficientMap
        hG hi hν I hKc hPK π C hC mu hsq Φ g).norm.continuousOn)
    exact ⟨c, fun ω => hc ⟨ω, Set.mem_univ _, rfl⟩⟩
  obtain ⟨c, hc, hb⟩ := exists_standardUnitaryConstantTerm_pointwise_bound
    hG hi hν I J hKc hPK hA hζ hB hmem π.obj π.property.1 π.property.2 ψ hψ t H hH
    (fun ω k l g => by rw [ht ω]; exact hfix ω k l g)
    (fun g => by
      obtain ⟨c, hc⟩ := hpoint g
      exact ⟨c, fun ω => by rw [ht ω]; exact hc ω⟩) m
  refine ⟨c, hc, fun ω => ?_⟩
  have h := hb ω
  simpa only [ht ω, rationalOrbitConstantTerm] using h

end Langlands.HarishChandraSchwartz
