import Langlands.Global.AdelicMinimalIwasawaFiniteWeight
import Langlands.Global.AdelicRelativeCuspidalRestrictionCompact
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicCentralPositiveHeightProof

/-! # Hilbert–Schmidt cuspidal restrictions on a weighted Iwasawa domain -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal ENNReal Pointwise

namespace Langlands.Global.StandardParabolicFamily

open Langlands.Analysis.OperatorIdeals Langlands.GroupScheme AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Geometry.Manifold RepresentationGrowth
  AdelicSiegelFactors PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
  (I : Type u) [Fintype I] (e : 𝓕.T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "B₀" => (Subtype.mk ∅ (empty_subset Δ) : Idx)
local notation "P₀" => Standard.parabolicScheme 𝓕.i 𝓕.ν ∅
local notation "p₀" => Standard.parabolicHom 𝓕.i 𝓕.ν ∅
local notation "t₀" => torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν
local notation "Z" => WeightedSiegel.DomainQuotient F p₀
local notation "height" => adelicHeight F G rho
local notation "A₀" => intrinsicSubgroup F 𝓕.T

private instance : IsClosedImmersion (p₀).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom 𝓕.i 𝓕.ν ∅

private instance : IsAffine (P₀).X.left := isAffine_of_isAffineHom (p₀).hom.hom.left

/-- The weighted relative boundary on the minimal-parabolic quotient has a
compact Hilbert–Schmidt restriction of a smooth relatively cuspidal family
of uniform moderate growth, for weights that dominate the log-coordinate norm. -/
def AdelicIwasawaCuspidalRestrictionStatement : Prop :=
  IsSiegelAlgebraicSetup F G 𝓕.T 𝓕.i 𝓕.ν T₀ j → 0 < N →
  ∀ (K : Subgroup A) (hK : IsIwasawaCompact p₀ K),
  ∃ (a : RealCharacterDual F P₀ → A₀) (c : ℝ),
    Continuous a ∧ 0 < c ∧
    (∀ h, characterLog F P₀ (positivePointMap F P₀ 𝓕.T t₀ (a h)) = h) ∧
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ∀ (P : Idx) (Zχ : Set (characterLattice 𝓕.T)), ratSpan (Δ ∪ Zχ) = ⊤ →
    ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
    ∀ (ell : RealCharacterDual F P₀ → ℝ) (S : Set Z), MeasurableSet S →
    ∀ (b₁ : ℝ),
    (∀ z ∈ S, c * ‖positiveLogCoordinates F I e (a (WeightedSiegel.domainHeight F p₀ hK z))‖ ≤
      2 * ell (WeightedSiegel.domainHeight F p₀ hK z) + b₁) →
    (∀ z ∈ S, let a₀ := a (WeightedSiegel.domainHeight F p₀ hK z)
      (∀ α ∈ Δ, b ≤ normCharacter F 𝓕.T α a₀) ∧
      (∀ χ ∈ Zχ, |logNormHom F 𝓕.T a₀.val χ| ≤ B) ∧
      (∀ α ∈ Δ \ P.val, |logNormHom F 𝓕.T a₀.val α| ≤ B)) →
    ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ev : A → E →L[ℂ] ℂ),
    (∀ q, Continuous (fun x => ev x q)) →
    (∀ q (y : Gf), ContMDiff IG IC ∞ (fun x : G∞ => ev (pair F G x y) q)) →
    (∀ q, ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, ev (r * x) q = ev x q) →
    (∀ q (u : AdelicGroupPoints F (𝓕.U P)), ∀ x,
      ev (map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) u * x) q = ev x q) →
    (∀ q, ∀ l ∈ L, ∀ x, ev (x * ofFinite F G l) q = ev x q) →
    (∀ q, 𝓕.IsCuspidalAlong P (fun x => ev x q)) →
    ∀ (R : ℝ), 0 ≤ R →
    (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q x, ‖adelicIteratedDirectionalValue hG s (fun y => ev y q) x‖ ≤ C * height x ^ R * ‖q‖) →
    let measure := WeightedSiegel.domainMeasure F p₀ hK ell S
    ∃ T : E →L[ℂ] Lp ℂ 2 measure, IsHilbertSchmidt T ∧ IsCompactOperator T ∧
      ∀ q : E, (T q : Z → ℂ) =ᵐ[measure] fun z => ev (Quotient.out z) q

theorem adelicIwasawaCuspidalRestriction :
    AdelicIwasawaCuspidalRestrictionStatement.{u, v} 𝓕 j I e hG rho := by
  intro hsetup hN K hK
  obtain ⟨a, Ω, ha, hΩ, hlog, hrep, c, hc, hFin⟩ :=
    adelicMinimalIwasawaFiniteWeight F 𝓕.i 𝓕.ν j I e hsetup K hK
  refine ⟨a, c, ha, hc, hlog, ?_⟩
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro P Zχ hSpan b B hB ell S hS b₁ hWeight hBoundary L hL E _ _ _ ev hf hfS hfR hfU hfL hCusp R hR hGrow
  let measure := WeightedSiegel.domainMeasure F p₀ hK ell S
  let : IsFiniteMeasure measure := hFin ell S hS b₁ hWeight
  let Γ := WeightedSiegel.parabolicPrincipalSubgroup F p₀
  have hEqRange : SubgroupFunctor.range p₀ = SubgroupFunctor.range (𝓕.p B₀) :=
    (Standard.isRepresentedBy_parabolicHom 𝓕.i 𝓕.ν ∅).2.trans (𝓕.isCompatible B₀).parabolic_eq.symm
  have hΓ : Γ = rationalImage F (𝓕.p B₀) := by
    change (rationalSubgroup F P₀).map (map F P₀ G p₀).toMonoidHom = _
    rw [← rationalImage_eq_map, rationalImage_eq_of_range_eq _ _ hEqRange]
  let Ω' := (fun p : normOneSubgroup F P₀ => map F P₀ G p₀ p) '' Ω
  have hΩ' : IsCompact Ω' := hΩ.image ((map F P₀ G p₀).continuous.comp continuous_subtype_val)
  have hΩ'P : Ω' ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) := by
    rintro _ ⟨z, -, rfl⟩
    have hz : map F P₀ G p₀ z ∈ (SubgroupFunctor.range p₀).carrier _ := ⟨z.val, rfl⟩
    rw [hEqRange] at hz
    exact hz
  let f₀ (z : Z) := Quotient.out z
  have hrep' (z : Z) := hrep (f₀ z)
  choose q₀ p hp k hk hpk using hrep'
  let rep (z : Z) := map F P₀ G p₀ (rational F P₀ (q₀ z)) * f₀ z
  have hq₀ (z : Z) : map F P₀ G p₀ (rational F P₀ (q₀ z)) ∈ Γ := ⟨_, ⟨q₀ z, rfl⟩, rfl⟩
  have hval (q : E) (z : Z) : ev (rep z) q = ev (f₀ z) q := hfR q _ (hΓ ▸ hq₀ z) _
  have hHeight (z : Z) : hK.height (f₀ z) = WeightedSiegel.domainHeight F p₀ hK z :=
    congrArg (WeightedSiegel.domainHeight F p₀ hK) (Quotient.out_eq z)
  have hRep (z : Z) : rep z = map F P₀ G p₀ (p z) *
      positivePointMap F G 𝓕.T 𝓕.i (a (WeightedSiegel.domainHeight F p₀ hK z)) * k z := by
    rw [← hHeight]
    exact hpk z
  let Yf := (finite F G '' Ω') * (finite F G '' (K : Set A))
  have hYf : IsCompact Yf := (hΩ'.image (finite F G).continuous).mul
    (hK.isCompact.image (finite F G).continuous)
  have hfin (z : Z) : finite F G (rep z) ∈ Yf := by
    rw [hRep, map_mul, map_mul, finite_positivePointMap F 𝓕.T 𝓕.i 𝓕.maximalSplit.1.1, mul_one]
    exact Set.mul_mem_mul ⟨_, ⟨p z, hp z, rfl⟩, rfl⟩ ⟨_, hk z, rfl⟩
  have hMeas (q : E) : AEStronglyMeasurable (fun z => ev (rep z) q) measure := by
    let lift := LeftCosetSpace.lift Γ (fun x => ev x q) (fun r x => hfR q r (hΓ ▸ r.2) x)
    have hcont : Continuous lift := LeftCosetSpace.continuous_lift Γ _ _ (hf q)
    have heq : (fun z => ev (rep z) q) = lift := by
      funext z
      exact (hval q z).trans (congrArg lift (Quotient.out_eq z))
    rw [heq]
    exact hcont.aestronglyMeasurable
  have hTS : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  have hSpan' : ratSpan (((fun α : characterLattice 𝓕.T => 𝟙 𝓕.T ≫ α) '' Δ) ∪ Zχ) = ⊤ := by
    simpa only [Category.id_comp, Set.image_id'] using hSpan
  have hAES : ∀ᵐ z ∂measure, z ∈ S :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hS)
  have hRepAe : ∀ᵐ z ∂measure, ∃ x ∈ Ω',
      ∃ a₀ ∈ weakSimpleRootChamber F 𝓕.T 𝓕.T (𝟙 𝓕.T) G 𝓕.i 𝓕.ν b,
      (∀ χ ∈ Zχ, |logNormHom F 𝓕.T a₀.val χ| ≤ B) ∧
      (∀ α ∈ Δ \ P.val, |logNormHom F 𝓕.T a₀.val (𝟙 𝓕.T ≫ α)| ≤ B) ∧
      ∃ y ∈ K, rep z = x * positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) a₀ * y ∧
        finite F G (rep z) ∈ Yf := by
    filter_upwards [hAES] with z hz
    let a₀ := a (WeightedSiegel.domainHeight F p₀ hK z)
    obtain ⟨hch, hZ, hOut⟩ := hBoundary z hz
    refine ⟨_, ⟨p z, hp z, rfl⟩, a₀, ?_, hZ, ?_, k z, hk z, ?_, hfin z⟩
    · intro α hα
      simpa only [Category.id_comp] using hch α hα
    · simpa only [Category.id_comp] using hOut
    · have hid : CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i = 𝓕.i := Category.id_comp _
      simpa only [positiveMap, positivePointMap, hid] using hRep z
  obtain ⟨T, hHS, hT, hTrep⟩ := 𝓕.adelicRelativeCuspidalRestrictionCompact (𝟙 𝓕.T) hG rho hTS hN
    P Zχ hSpan' b B hB Ω' K hΩ' hK.isCompact hΩ'P Yf hYf L hL
    E ev hf hfS hfR hfU hfL hCusp R hR hGrow Z measure rep 0 hMeas hRepAe
    (by simpa only [pow_zero, inv_one] using memLp_const («μ» := measure) (1 : ℝ))
  exact ⟨T, hHS, hT, fun q => (hTrep q).trans (Eventually.of_forall (hval q))⟩

end Langlands.Global.StandardParabolicFamily
