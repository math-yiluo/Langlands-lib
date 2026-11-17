import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientRapidDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCellHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLowerBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection
import Langlands.Representation.Aubert.General.RationalCompactTranslateCoefficientBoundProof
import Langlands.Representation.Aubert.General.RationalFiniteChamberCartanCoverProof
import Langlands.Representation.Aubert.General.RationalCartanJointDetection
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.Representation.Exponents.CasselmanSufficiencyReduction
import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly
import Langlands.Representation.Exponents.CasselmanUniverseLift
import Langlands.Representation.Plancherel.CentralSubgroupComparisonProof
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.Algebra.FiniteChamberLatticeProof
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics

/-! # Proof of Waldspurger's Corollary III.1.2 on actual rational points -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section AbstractDecay

variable {X : Type*} [Group X] {Ξ σ : X → ℝ}

/-- **Geometric decay in a parameter controlling `σ` gives rapid decay.** If for every `g ∈ N`
there is `m ∈ ℕ` with `‖f g‖ ≤ C Ξ(g) q^m` (fixed `0 < q < 1`) and `1 + σ(g) ≤ c (1 + m)`, then
`f` decreases rapidly on `N`. -/
theorem isRapidlyDecreasingOn_of_geometric (hΞ : ∀ g, 0 ≤ Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    {N : Subgroup X} {f : X → ℂ} {q C c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (h : ∀ g ∈ N, ∃ m : ℕ, ‖f g‖ ≤ C * Ξ g * q ^ m ∧ 1 + σ g ≤ c * (1 + m)) :
    IsRapidlyDecreasingOn Ξ σ N f := by
  classical
  choose! m hm using h
  intro r
  have hε : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  refine exists_rpow_bound_of_exp_bound (S := (N : Set X)) (H := fun g => (m g : ℝ))
    (fun x _ => hΞ x) (fun x _ => hσ x) ⟨c, fun x hx => ?_⟩ {()} (fun _ => (N : Set X))
    (fun x hx => by simpa using hx) (fun _ _ => ⟨-Real.log q, hε, C, fun x hx => ?_⟩) r
  · rw [Real.norm_natCast]
    exact (hm x hx).2
  · have hexp : Real.exp (-(-Real.log q * ‖(m x : ℝ)‖)) = q ^ m x := by
      rw [Real.norm_natCast, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
    rw [hexp]
    exact (hm x hx).1

/-- A lower bound for a bi-`K`-invariant function with uniform translation bounds on compact
translates: for a compact `K₀` and a finite set `F₁` there is `M` with
`Ξ(w) ≤ M Ξ(k₁ w t k₂)` for all `w`, `k₁, k₂ ∈ K₀` and `t ∈ F₁`. -/
theorem exists_le_mul_of_compact_translates [TopologicalSpace X] [IsTopologicalGroup X]
    {K K0 : Subgroup X} (hKo : IsOpen (K : Set X)) (hK0c : IsCompact (K0 : Set X))
    (hΞ : ∀ g, 0 ≤ Ξ g) (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hT : UniformTranslationBound Ξ) {F₁ : Set X} (hF₁ : F₁.Finite) :
    ∃ M : ℝ, ∀ w k₁ k₂ t : X, k₁ ∈ K0 → k₂ ∈ K0 → t ∈ F₁ → Ξ w ≤ M * Ξ (k₁ * w * t * k₂) := by
  classical
  obtain ⟨tt, htt⟩ := exists_finset_mul_mem_of_isCompact hKo hK0c
  choose Cf hCf using hT
  obtain ⟨M, hM⟩ := ((tt ×ˢ (tt ×ˢ hF₁.toFinset)).image fun p : X × (X × X) =>
    Cf p.1⁻¹ (p.2.1 * p.2.2⁻¹)).exists_le
  refine ⟨M, fun w k₁ k₂ t hk₁ hk₂ ht => ?_⟩
  obtain ⟨c₁, hc₁, hc₁'⟩ := htt k₁⁻¹ (K0.inv_mem hk₁)
  obtain ⟨c₂, hc₂, hc₂'⟩ := htt k₂ hk₂
  have hw : w = c₁⁻¹ * ((c₁ * k₁⁻¹) * (k₁ * w * t * k₂) * (c₂ * k₂)⁻¹) * (c₂ * t⁻¹) := by
    group
  have hb := hCf c₁⁻¹ (c₂ * t⁻¹) ((c₁ * k₁⁻¹) * (k₁ * w * t * k₂) * (c₂ * k₂)⁻¹)
  rw [← hw, hΞK _ hc₁' _ (K.inv_mem hc₂')] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right (hM _ (Finset.mem_image.mpr
    ⟨(c₁, c₂, t), ?_, rfl⟩)) (hΞ _))
  simp [hc₁, hc₂, ht]

/-- Finitely many reals below `1` have a common bound `q` with `0 < q < 1`. -/
theorem exists_lt_one_forall_le {Idx : Type*} [Finite Idx] (f : Idx → ℝ) (hf : ∀ a, f a < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ a, f a ≤ q := by
  rcases isEmpty_or_nonempty Idx with hI | hI
  · exact ⟨1 / 2, by norm_num, by norm_num, fun a => (IsEmpty.false a).elim⟩
  · obtain ⟨a₀, ha₀⟩ := Finite.exists_max f
    exact ⟨max (f a₀) (1 / 2), lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      max_lt (hf a₀) (by norm_num), fun a => (ha₀ a).trans (le_max_left _ _)⟩

end AbstractDecay

section Exponents

open Aubert.General Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance decayExponentsTopology : TopologicalSpace (rationalPoints G) := pointTopology

local instance decayExponentsIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The center of `G(F)` modulo the image `A_G(F)` of a split component is compact. -/
theorem compactSpace_center_quotient_splitComponent (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    CompactSpace (Subgroup.center (rationalPoints G) ⧸
      (rationalPoints.map s).range.subgroupOf (Subgroup.center (rationalPoints G))) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hc : CompactSpace (CentralPointQuotient s hs.isCentralSplitTorus.isCentral) :=
    centerSplitComponentCompactness F G hG T s hs
  let f : schemeCenterPoints G →* Subgroup.center (rationalPoints G) :=
    schemeCenterPointsToCenter G
  have hle : centralRationalPointImage s hs.isCentralSplitTorus.isCentral ≤
      ((rationalPoints.map s).range.subgroupOf (Subgroup.center (rationalPoints G))).comap f := by
    rintro z ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  let g := QuotientGroup.map _ _ f hle
  have hf : Continuous f := Continuous.subtype_mk continuous_subtype_val _
  have hg : Continuous g :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (QuotientGroup.continuous_mk.comp hf)
  refine Function.Surjective.compactSpace hg ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H w =>
    have hw : w.val ∈ schemeCenterPoints G := by
      rw [rationalCenterComparison F G hG]
      exact w.property
    exact ⟨QuotientGroup.mk ⟨w.val, hw⟩, rfl⟩

variable [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The uniformizer powers `ϖ^y` lie in the minimal standard parabolic `P₀(F)`. -/
theorem uniformizerPowers_mem_standardParabolicPoints
    {S : CommGroupScheme (Spec (CommRingCat.of F))} (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (y : cocharacterLattice S) :
    uniformizerPowers i (.ofAdd y) ∈ standardParabolicPoints i ν ∅ := by
  have h := map_mem_standardLeviPoints_empty (i := i) (ν := ν) (𝟙 S.toGrp)
    (Plancherel.RenardCartan.uniformizerSection S (.ofAdd y))
  rw [Category.id_comp] at h
  exact standardLevi_le_standardParabolic i ν ∅ _ h

/-- **Strict exponents from square integrability modulo `A_G(F)`.** For a representation of
`G(F)` that is square integrable modulo the image of a split component, the universe lift of
the representation has strict normalized Jacquet exponents along every actual standard
parabolic: square integrability modulo the full center (published comparison), the necessity
half of Casselman's criterion (published), and the standard torus tests (published). -/
theorem hasStrictNormalizedJacquetExponents_universeLift (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s)
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    [T2Space (rationalPoints G)] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
        HasStrictNormalizedJacquetExponents i ν
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν standardCocharacter
            hG hi hν)
          (fun I => isClosed_unipotent_of_isNonarchimedeanLocalField i ν I)
          (SmoothRep.universeLift.{u + 1} A) := by
  intro mu _ A hsq
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space F := BruhatTits.localField_t2Space F
  have : SecondCountableTopology (rationalPoints G) :=
    reductiveRationalPoint_secondCountable F G hG
  have hC := hs.isCentralSplitTorus.isCentral.range_le_center
  have hclosed : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) := by
    have h := RepresentedParabolic.isClosed_pointImage s hs.1.1.2
    convert h using 1
  have : CompactSpace (Subgroup.center (rationalPoints G) ⧸
      (rationalPoints.map s).range.subgroupOf (Subgroup.center (rationalPoints G))) :=
    compactSpace_center_quotient_splitComponent hG hs
  let : MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := borel _
  have : BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := ⟨rfl⟩
  let haar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := Measure.haar
  have : (rationalPoints.map s).range.Normal := (rationalPoints.map s).range.normal_of_le_center hC
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  have : BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := ⟨rfl⟩
  have hZ : IsSquareIntegrableModCenter A.representation haar :=
    ((Plancherel.centralSubgroupCoefficientLpComparison (rationalPoints G)
      (rationalPoints.map s).range hC hclosed mu haar A A.representation).2).mp hsq
  have hcone := RepresentedParabolic.arbitraryParabolicCasselmanNecessity F G hG haar A hZ
  have hgeom := fun I =>
    RepresentedParabolic.standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter
      hG hi hν I
  let D : ∀ I, RepresentedParabolic.StandardCasselmanPresentation i ν I := fun I =>
    RepresentedParabolic.standardCasselmanPresentationOfGeometry hG i hi ν hν
      standardCocharacter (genericMinimalParabolic F G hG S i hi ν hν) I (hgeom I).1
      (hgeom I).2.1 (hgeom I).2.2.1 (hgeom I).2.2.2
  have hU : ∀ I : Finset (SimpleRoot i ν),
      IsClosed (unipotent i ν I : Set (rationalPoints G)) :=
    fun I => isClosed_unipotent_of_isNonarchimedeanLocalField i ν I
  have hstrict := RepresentedParabolic.strictStandardExponents_of_positiveRepresented i ν D
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν standardCocharacter
      hG hi hν) hU (hasSelectedRootValuationLaw hG i hi ν) A hcone
  let e := SmoothRep.universeLiftEquiv.{u + 1} A
  intro I χ hχ t z hz ht
  apply hstrict I χ ?_ t z hz ht
  exact (isCentralExponent_normalizedJacquet_equiv_iff _ _ (hU I)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν I).levi_le_normalizer A
      (SmoothRep.universeLift.{u + 1} A) e χ).mpr hχ

/-- **Coefficient bound on compact translates from square integrability.** For a representation
`A` of `G(F)` square integrable modulo `A_G(F)`, the published coefficient bound on compact
translates of a finite ray lattice (applied to the universe lift of `A`, which has strict
normalized Jacquet exponents) gives, for each ray `x_a` central in `M_{J_a}`, a rate `r_a` with
`r_a² < δ₀(ϖ^{x_a})` and `|ℓ(π(k₁ ϖ^{Σ n_a x_a} t k₂) v)| ≤ C ∏ r_a^{n_a}`. -/
theorem exists_coefficient_bound_of_squareIntegrable (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) (_hmu : mu.IsHaarMeasure)
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ {K0 : Subgroup (rationalPoints G)}, SimultaneousStandardBasisAt i ν K0 →
      ∀ {I : Type u} [Fintype I] [DecidableEq I] (J : I → Finset (SimpleRoot i ν))
        (x : I → cocharacterLattice S),
        (∀ a β, β ∈ J a → simpleRootPairing i ν β (x a) = 0) →
        (∀ a β, β ∉ J a → 0 < simpleRootPairing i ν β (x a)) →
        (∀ a, ∃ β, β ∉ J a) →
        ∀ (S₁ S₂ F₀ : Set (rationalPoints G)), IsCompact S₁ → IsCompact S₂ → F₀.Finite →
        ∀ (φ : SmoothDual A.representation) (v : A),
          ∃ r : I → ℝ, (∀ a, 0 < r a ∧ r a ^ 2 < ((rationalMinimalModulus i ν
              ⟨uniformizerPowers i (.ofAdd (x a)),
                uniformizerPowers_mem_standardParabolicPoints i ν (x a)⟩ : ℝ≥0) : ℝ)) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ (n : I → ℕ), ∀ k₁ ∈ S₁, ∀ t ∈ F₀, ∀ k₂ ∈ S₂,
              ‖φ.val (A.representation
                (k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • x a)) * t * k₂) v)‖ ≤
                C * ∏ a, r a ^ n a := by
  intro mu hmu A hsq K0 hbasis I _ _ J x hzero hpos hout S₁ S₂ F₀ h₁ h₂ h₀ φ v
  have : LocallyCompactSpace (rationalPoints G) := rationalWeightsLocallyCompact
  have : NonarchimedeanGroup (rationalPoints G) := Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space F := BruhatTits.localField_t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hstrict := hasStrictNormalizedJacquetExponents_universeLift hG hi hν hs mu A hsq
  obtain ⟨z, hz, h⟩ := rationalCompactTranslateCoefficientBound.{u, uV, u} F G hG S i hi ν hν
    standardCocharacter (fun I => isClosed_unipotent_of_isNonarchimedeanLocalField i ν I)
    (SmoothRep.universeLift.{u + 1} A) ((SmoothRep.isAdmissible_universeLift_iff A).mpr hsq.1)
    hstrict K0 hbasis I J x hzero hpos hout
  obtain ⟨r, hr, C, hC, hb⟩ := h S₁ S₂ F₀ h₁ h₂ h₀
    (contragredientMap (SmoothRep.universeLiftEquiv.{u + 1} A).symm.toIntertwiningMap φ)
    (ULift.up v)
  refine ⟨r, fun a => ⟨(hr a).1, ?_⟩, C, hC, fun n k₁ hk₁ t ht k₂ hk₂ => hb n k₁ hk₁ t ht k₂ hk₂⟩
  have hp : uniformizerPowers i (.ofAdd (x a)) ∈ standardParabolicPoints i ν ∅ ⊓
      standardLeviPoints i ν (rootSet i ν (J a)) :=
    Subgroup.mem_inf.mpr ⟨uniformizerPowers_mem_standardParabolicPoints i ν (x a),
      uniformizerPowers_mem_levi i ν (J a) (x a)⟩
  have heq := rationalMinimalModulus_eq_standardUnipotentModulus_of_commute hG hi hν
    (rootSet_subset i ν (J a)) ⟨_, hp⟩ (fun m hm => by
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp (z a).2 ⟨m, hm⟩)
      simp only [Subgroup.coe_mul, hz a] at hc
      exact hc.symm)
  have hza : (z a : levi i ν (J a)) = ⟨_, (Subgroup.mem_inf.mp hp).2⟩ := Subtype.ext (hz a)
  have hΔ : (((HaarModulus.closedRestrictCharacter (unipotent i ν (J a))
      (isClosed_unipotent_of_isNonarchimedeanLocalField i ν (J a)) (levi i ν (J a))
      (levi_le_normalizer i ν (J a)) (z a : levi i ν (J a)) : ℝ≥0) : ℝ)) =
      ((rationalMinimalModulus i ν ⟨uniformizerPowers i (.ofAdd (x a)),
        uniformizerPowers_mem_standardParabolicPoints i ν (x a)⟩ : ℝ≥0) : ℝ) := by
    rw [hza]
    exact congrArg (fun w : ℝ≥0ˣ => ((w : ℝ≥0) : ℝ)) heq.symm
  have hpos' : (0 : ℝ) < ((rationalMinimalModulus i ν ⟨uniformizerPowers i (.ofAdd (x a)),
      uniformizerPowers_mem_standardParabolicPoints i ν (x a)⟩ : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have h2 := (hr a).2
  rw [hΔ] at h2
  have h3 := (mul_inv_lt_iff₀ hpos').mp h2
  linarith

end Exponents

section Rational

open Aubert.General Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hKo in
/-- `Ξ(a g) = Ξ(g)` for a central `a ∈ P₀(F)`: `δ₀(a) = 1` and `a` commutes with `K`. -/
theorem rationalXi_mul_of_mem_center {a : rationalPoints G}
    (haP : a ∈ standardParabolicPoints i ν ∅) (hac : a ∈ Subgroup.center (rationalPoints G))
    (g : rationalPoints G) : rationalXi hKc hPK (a * g) = rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact xi_mul_left_of_eq_one (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) haP
    (rationalMinimalModulus_eq_one_of_mem_center i ν ⟨a, haP⟩ hac)
    (fun k _ => Subgroup.mem_center_iff.mp hac k) g

include hKo in
/-- **Geometric decay along the chamber lattice.** Let `A` be square integrable modulo `A_G(F)`
and let `gen_a` (one for each simple root `a`) satisfy `⟨a, gen_a⟩ > 0` and `⟨b, gen_a⟩ = 0` for
`b ≠ a`. For every finite set `F₁` there are `0 < q < 1` and `C` with
`|ℓ(π(k₁ ϖ^{Σ n_a gen_a} t k₂) v)| ≤ C Ξ(k₁ ϖ^{Σ n_a gen_a} t k₂) q^{Σ n_a}` for all
`k₁, k₂ ∈ K0` and `t ∈ F₁`: the coefficient bound `C' ∏ r_a^{n_a}` with `r_a² < δ₀(ϖ^{gen_a})`,
the lower bound `δ₀(ϖ^y)^{1/2} ≤ C'' Ξ(ϖ^y)` on the closed positive chamber, and Lemma II.1.2 for
the compact translates. -/
theorem exists_geometric_coefficient_bound (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) [Fintype (SimpleRoot i ν)]
    (gen : SimpleRoot i ν → cocharacterLattice S)
    (hgenpos : ∀ α, 0 < simpleRootPairing i ν α (gen α))
    (hgenzero : ∀ α β, β ≠ α → simpleRootPairing i ν β (gen α) = 0)
    {F₁ : Set (rationalPoints G)} (hF₁ : F₁.Finite)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) (_hmu : mu.IsHaarMeasure)
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ (φ : SmoothDual A.representation) (v : A),
        ∃ q C : ℝ, 0 < q ∧ q < 1 ∧ ∀ (n : SimpleRoot i ν → ℕ), ∀ k₁ ∈ K0, ∀ t ∈ F₁, ∀ k₂ ∈ K0,
          ‖φ.val (A.representation
              (k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) * t * k₂) v)‖ ≤
            C * rationalXi hKc hPK
              (k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) * t * k₂) *
              q ^ (∑ a, n a) := by
  intro mu hmu A hsq φ v
  classical
  let J : SimpleRoot i ν → Finset (SimpleRoot i ν) := fun a => Finset.univ.erase a
  have hzero : ∀ a β, β ∈ J a → simpleRootPairing i ν β (gen a) = 0 := by
    intro a β hβ
    exact hgenzero a β (Finset.mem_erase.mp hβ).1
  have hpos : ∀ a β, β ∉ J a → 0 < simpleRootPairing i ν β (gen a) := by
    intro a β hβ
    have hβa : β = a := by simpa [J] using hβ
    subst β
    exact hgenpos a
  have hout : ∀ a, ∃ β, β ∉ J a := fun a => ⟨a, by simp [J]⟩
  have hgen_nonneg : ∀ a β, 0 ≤ simpleRootPairing i ν β (gen a) := by
    intro a β
    by_cases h : β = a
    · subst h
      exact (hgenpos β).le
    · exact (hgenzero a β h).ge
  -- the coefficient bound on compact translates
  obtain ⟨r, hr, Cc, hCc, hcoef⟩ := exists_coefficient_bound_of_squareIntegrable hG hi hν hs mu
    hmu A hsq hbasis J gen hzero hpos hout K0 K0 F₁ hK0c hK0c hF₁ φ v
  -- Lemma II.1.2 on the compact translates
  obtain ⟨M, hM⟩ := exists_le_mul_of_compact_translates hKo hK0c (rationalXi_nonneg hKc hPK)
    (fun k₁ hk₁ k₂ hk₂ g => rationalXi_mul_mul hKo hKc hPK hk₁ hk₂ g)
    (rationalXi_uniformTranslationBound hKo hKc hPK) hF₁
  -- the lower bound of Lemma II.1.1
  obtain ⟨B, hB, hBJ⟩ := id hbasis
  obtain ⟨-, A', q', hA', hmem⟩ := hBJ ∅ (Set.empty_subset _)
  obtain ⟨H, hHB, hHK⟩ := hB.2.mem_iff.mp (hKo.mem_nhds K.one_mem)
  obtain ⟨-, -, hHo, -⟩ := hB.1 H hHB
  obtain ⟨CL, hCL⟩ := exists_sqrt_rationalMinimalModulus_le_rationalXi hKo hKc
    (fun x hx => hHK hx) (hmem H hHB) hHo hPK
  -- the moduli along the lattice
  let δy : Multiplicative (cocharacterLattice S) →* ℝ≥0 :=
    (Units.coeHom ℝ≥0).comp ((rationalMinimalModulus i ν).comp
      ((uniformizerPowers i).codRestrict _
        (fun y => uniformizerPowers_mem_standardParabolicPoints i ν (Multiplicative.toAdd y))))
  let δs : Multiplicative (cocharacterLattice S) →* ℝ≥0 :=
    (NNReal.sqrtHom : ℝ≥0 →*₀ ℝ≥0).toMonoidHom.comp δy
  let sr : SimpleRoot i ν → ℝ := fun a => (δs (.ofAdd (gen a)) : ℝ)
  have hsr_pos : ∀ a, 0 < sr a := fun a => by
    have h0 : (0 : ℝ≥0) < δy (.ofAdd (gen a)) := pos_iff_ne_zero.mpr (Units.ne_zero _)
    exact NNReal.coe_pos.mpr (NNReal.sqrt_pos.mpr h0)
  have hrs : ∀ a, r a < sr a := by
    intro a
    change r a < ((NNReal.sqrt (δy (.ofAdd (gen a))) : ℝ≥0) : ℝ)
    rw [Real.coe_sqrt]
    exact (Real.lt_sqrt (hr a).1.le).mpr (hr a).2
  obtain ⟨qq, hqq0, hqq1, hqq⟩ := exists_lt_one_forall_le (fun a => r a / sr a)
    (fun a => (div_lt_one (hsr_pos a)).mpr (hrs a))
  refine ⟨qq, Cc * max CL 0 * max M 0, hqq0, hqq1, fun n k₁ hk₁ t ht k₂ hk₂ => ?_⟩
  have hwP := uniformizerPowers_mem_standardParabolicPoints i ν (∑ a, n a • gen a)
  have hprod : δs (.ofAdd (∑ a, n a • gen a)) = ∏ a, δs (.ofAdd (gen a)) ^ n a := by
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [ofAdd_nsmul, map_pow]
  have hδw : (NNReal.sqrt (rationalMinimalModulus i ν
      ⟨uniformizerPowers i (.ofAdd (∑ a, n a • gen a)), hwP⟩ : ℝ≥0) : ℝ) = ∏ a, sr a ^ n a := by
    have h1 : NNReal.sqrt (rationalMinimalModulus i ν
        ⟨uniformizerPowers i (.ofAdd (∑ a, n a • gen a)), hwP⟩ : ℝ≥0) =
        δs (.ofAdd (∑ a, n a • gen a)) := rfl
    rw [h1, hprod, NNReal.coe_prod]
    simp only [NNReal.coe_pow, sr]
  have hnonneg : ∀ β ∈ simpleRelativeRoots i ν,
      0 ≤ latticePairing S β (∑ a, n a • gen a) := by
    intro β hβ
    change 0 ≤ simpleRootPairing i ν ⟨β, hβ⟩ (∑ a, n a • gen a)
    rw [map_sum]
    exact Finset.sum_nonneg fun a _ => by
      rw [map_nsmul]
      exact nsmul_nonneg (hgen_nonneg a _) _
  have hchamber := (uniformizerPowers_mem_standardComponentChambers hi
    ⟨ν, isStandardCocharacter_empty_self i ν⟩ hA' (∑ a, n a • gen a) (by simp) hnonneg).2
  have hL := hCL _ hwP hchamber
  rw [hδw] at hL
  have hMw := hM (uniformizerPowers i (.ofAdd (∑ a, n a • gen a))) k₁ k₂ t hk₁ hk₂ ht
  set w := uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) with hw
  have hΞ0 := rationalXi_nonneg hKc hPK (k₁ * w * t * k₂)
  have hΞw0 := rationalXi_nonneg hKc hPK w
  have hprodle : ∏ a, r a ^ n a ≤ qq ^ (∑ a, n a) * ∏ a, sr a ^ n a := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun a _ => pow_nonneg (hr a).1.le _) fun a _ => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (hr a).1.le ?_ _
    have := hqq a
    rw [div_le_iff₀ (hsr_pos a)] at this
    linarith
  have hc := hcoef n k₁ hk₁ t ht k₂ hk₂
  have hXi : ∏ a, sr a ^ n a ≤ max CL 0 * (max M 0 * rationalXi hKc hPK (k₁ * w * t * k₂)) :=
    calc ∏ a, sr a ^ n a ≤ CL * rationalXi hKc hPK w := hL
      _ ≤ max CL 0 * rationalXi hKc hPK w :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hΞw0
      _ ≤ max CL 0 * (max M 0 * rationalXi hKc hPK (k₁ * w * t * k₂)) :=
        mul_le_mul_of_nonneg_left
          (hMw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΞ0)) (le_max_right _ _)
  calc ‖φ.val (A.representation (k₁ * w * t * k₂) v)‖ ≤ Cc * ∏ a, r a ^ n a := hc
    _ ≤ Cc * (qq ^ (∑ a, n a) * ∏ a, sr a ^ n a) := mul_le_mul_of_nonneg_left hprodle hCc.le
    _ ≤ Cc * (qq ^ (∑ a, n a) *
          (max CL 0 * (max M 0 * rationalXi hKc hPK (k₁ * w * t * k₂)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hXi (pow_nonneg hqq0.le _)) hCc.le
    _ = Cc * max CL 0 * max M 0 * rationalXi hKc hPK (k₁ * w * t * k₂) *
          qq ^ (∑ a, n a) := by ring

include hKo in
/-- **Corollary III.1.2 for one group.** Under the simultaneous standard basis and the finite
Cartan covering at a compact subgroup `K0`, the coefficients of every representation that is
square integrable modulo `A_G(F)` decrease rapidly on `G¹` for `Ξ = rationalXi` and
`σ = rationalHeight ρ`, for every matrix representation `ρ`. -/
theorem hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] (ρ : MatrixRepresentation G Idx)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
        HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
          (Plancherel.rationalCommonNormKernel G) A.representation := by
  intro mu hmu A hsq v φ
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (SimpleRoot i ν) := hfinite.fintype
  have hfull : levi i ν Finset.univ = ⊤ := levi_univ_eq_top i ν standardCocharacter hG hi hν
  have hexists (I : Finset (SimpleRoot i ν)) :
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
    (standardCocharacter F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
  have hstd (I : Finset (SimpleRoot i ν)) : ∃ ζ : cocharacterLattice S,
      (∀ β ∈ I, simpleRootPairing i ν β ζ = 0) ∧
        ∀ β ∉ I, 0 < simpleRootPairing i ν β ζ := by
    obtain ⟨ζ, hζ⟩ := hexists I
    exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
      fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
  have hcentral (x : cocharacterLattice S) (hx : ∀ α, simpleRootPairing i ν α x = 0) :
      uniformizerPowers i (.ofAdd x) ∈ Subgroup.center (rationalPoints G) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact commute_uniformizerPowers i ν hfinite Finset.univ (hexists _) x
      (fun β _ => hx β) g (by rw [hfull]; exact Subgroup.mem_top _)
  -- the chamber lattice: one generator per simple root, up to a finite set and the centre
  obtain ⟨gen, hgenpos, hgenzero, hgenR⟩ := finiteChamberLattice (SimpleRoot i ν)
    (cocharacterLattice S) (simpleRootPairing i ν) hstd
  obtain ⟨R, hRfin, hR⟩ := hgenR 0
  obtain ⟨F0, hF0⟩ := hcover
  let F₁ : Set (rationalPoints G) :=
    (fun p : cocharacterLattice S × centralizerPoints i =>
      uniformizerPowers i (.ofAdd p.1) * (p.2 : rationalPoints G)) ''
        (R ×ˢ (F0 : Set (centralizerPoints i)))
  have hF₁ : F₁.Finite := (hRfin.prod F0.finite_toSet).image _
  -- geometric decay of the coefficient and the height bound on the Cartan cells
  obtain ⟨q, C, hq0, hq1, hgeo⟩ := exists_geometric_coefficient_bound hKo hKc hPK hG hi hν
    hK0c hbasis gen hgenpos hgenzero hF₁ hs mu hmu A hsq φ v
  obtain ⟨Cσ, hCσ⟩ := exists_rationalHeight_le_of_mem_rationalCartanCell hG hi hν hK0c F0 ρ
  obtain ⟨-, c, -⟩ := hsq
  let D : ℝ := ∑ β : SimpleRoot i ν, ∑ r ∈ hRfin.toFinset, |(simpleRootPairing i ν β r : ℝ)|
  let E : ℝ :=
    ∑ β : SimpleRoot i ν, ∑ a : SimpleRoot i ν, |(simpleRootPairing i ν β (gen a) : ℝ)|
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine isRapidlyDecreasingOn_of_geometric (rationalXi_nonneg hKc hPK)
    (rationalHeight_nonneg ρ) (C := C) (c := 1 + max Cσ 0 * (1 + D + E)) hq0 hq1
    fun g hg => ?_
  obtain ⟨y, hy0, hy⟩ := exists_mem_rationalCartanCell hF0 g
  obtain ⟨r, hr, n, z, hz, hyeq⟩ := hR y (fun α => by rw [neg_zero]; exact hy0 α)
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, hgeq⟩ := id hy
  have hzc := hcentral z hz
  have hyw : uniformizerPowers i (.ofAdd y) = uniformizerPowers i (.ofAdd z) *
      (uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) * uniformizerPowers i (.ofAdd r)) := by
    rw [← map_mul, ← map_mul, ← ofAdd_add, ← ofAdd_add, hyeq]
    congr 2
    abel
  set Z := uniformizerPowers i (.ofAdd z) with hZ
  set W := uniformizerPowers i (.ofAdd (∑ a, n a • gen a)) with hW
  set Pr := uniformizerPowers i (.ofAdd r) with hPr
  have hgeq' : g = Z * (k₁ * W * (Pr * (f : rationalPoints G)) * k₂) := by
    have hcomm : k₁ * Z = Z * k₁ := Subgroup.mem_center_iff.mp hzc k₁
    rw [hgeq, hyw]
    calc k₁ * (Z * (W * Pr)) * (f : rationalPoints G) * k₂ =
        (k₁ * Z) * W * (Pr * (f : rationalPoints G)) * k₂ := by simp only [mul_assoc]
      _ = Z * (k₁ * W * (Pr * (f : rationalPoints G)) * k₂) := by
        rw [hcomm]
        simp only [mul_assoc]
  set g' := k₁ * W * (Pr * (f : rationalPoints G)) * k₂ with hg'
  have hcoef : ‖φ.val (A.representation g v)‖ = ‖φ.val (A.representation g' v)‖ := by
    rw [hgeq', map_mul, Module.End.mul_apply]
    have hact : A.representation Z (A.representation g' v) =
        (c.character ⟨Z, hzc⟩ : ℂ) • A.representation g' v := c.acts ⟨Z, hzc⟩ _
    rw [hact, map_smul, norm_smul, c.norm_eq_one, one_mul]
  have hXi : rationalXi hKc hPK g = rationalXi hKc hPK g' := by
    rw [hgeq']
    exact rationalXi_mul_of_mem_center hKo hKc hPK
      (uniformizerPowers_mem_standardParabolicPoints i ν z) hzc _
  have hgb := hgeo n k₁ hk₁ (Pr * (f : rationalPoints G))
    ⟨(r, f), Set.mk_mem_prod hr (Finset.mem_coe.mpr hf), rfl⟩ k₂ hk₂
  -- the pairings of `y` with the simple roots are bounded by `D + E Σ n_a`
  have hTb : ∀ β : SimpleRoot i ν,
      |(simpleRootPairing i ν β y : ℝ)| ≤ D + E * ((∑ a, n a : ℕ) : ℝ) := by
    intro β
    have hpair : (simpleRootPairing i ν β y : ℝ) = (simpleRootPairing i ν β r : ℝ) +
        ∑ a, (n a : ℝ) * (simpleRootPairing i ν β (gen a) : ℝ) := by
      rw [hyeq, map_add, map_add, hz β, add_zero, map_sum]
      simp only [map_nsmul, nsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast]
    have hD : |(simpleRootPairing i ν β r : ℝ)| ≤ D := by
      have h1 : |(simpleRootPairing i ν β r : ℝ)| ≤
          ∑ r' ∈ hRfin.toFinset, |(simpleRootPairing i ν β r' : ℝ)| :=
        Finset.single_le_sum (f := fun r' => |(simpleRootPairing i ν β r' : ℝ)|)
          (fun _ _ => abs_nonneg _) (hRfin.mem_toFinset.mpr hr)
      exact h1.trans (Finset.single_le_sum
        (f := fun β' => ∑ r' ∈ hRfin.toFinset, |(simpleRootPairing i ν β' r' : ℝ)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ β))
    have hE : |∑ a, (n a : ℝ) * (simpleRootPairing i ν β (gen a) : ℝ)| ≤
        E * ((∑ a, n a : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h2 : ∀ a, |(n a : ℝ) * (simpleRootPairing i ν β (gen a) : ℝ)| ≤
          ((∑ a, n a : ℕ) : ℝ) * |(simpleRootPairing i ν β (gen a) : ℝ)| := by
        intro a
        rw [abs_mul, Nat.abs_cast]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact_mod_cast Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      refine (Finset.sum_le_sum fun a _ => h2 a).trans ?_
      rw [← Finset.mul_sum, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact Finset.single_le_sum
        (f := fun β' => ∑ a, |(simpleRootPairing i ν β' (gen a) : ℝ)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ β)
    rw [hpair]
    exact (abs_add_le _ _).trans (add_le_add hD hE)
  have hσg := hCσ y (D + E * ((∑ a, n a : ℕ) : ℝ))
    (add_nonneg hD0 (mul_nonneg hE0 (Nat.cast_nonneg _))) hTb g hy hg
  refine ⟨∑ a, n a, ?_, ?_⟩
  · rw [hcoef, hXi]
    exact hgb
  · set m : ℝ := ((∑ a, n a : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hCm : 0 ≤ max Cσ 0 := le_max_right _ _
    have h1 : rationalHeight (F := F) ρ g ≤ max Cσ 0 * (1 + (D + E * m)) :=
      hσg.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by linarith [mul_nonneg hE0 hm0]))
    have h2 : 1 + (D + E * m) ≤ (1 + D + E) * (1 + m) := by
      nlinarith [mul_nonneg hD0 hm0]
    have h3 := mul_le_mul_of_nonneg_left h2 hCm
    nlinarith

end Rational

/-- **Waldspurger, Corollaire III.1.2** (printed p. 263) on actual rational points. -/
theorem rationalSquareIntegrableRapidDecay :
    RationalSquareIntegrableRapidDecayStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0 _ hK0c hbasis hcover K hKo hKc hPK N _ ρ _ T s hs
  exact hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable hKo hKc hPK hG hi hν hK0c hbasis
    hcover ρ hs

end Langlands.HarishChandraSchwartz
