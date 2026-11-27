import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Global.AdelicConstantTermComposition
import Langlands.Global.AdelicConstantTermDirectionalGrowth
import Langlands.Global.AdelicLeviConstantTermPairing

/-! # Decay of the difference of two nested constant terms

For a continuous left `G(F)`-invariant function `g`, a standard index `J` and a simple root
`α ∈ J`, the difference `C_J g - C_{J ∖ α} g` has vanishing constant term along the maximal
standard parabolic omitting `α`. Mœglin–Waldspurger's estimate I.2.10, in the form of the
Library's `adelicMaximalUnipotentDecay`, then bounds it by an arbitrary power of `|α(a)|^{-1}`
times bounds for its derivatives. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set MeasureTheory
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "B₀" => (Subtype.mk ∅ (empty_subset Δ) : Idx)
local notation "rad(" Q ")" => SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)

/-- The constant terms of a continuous `G(F)`-invariant function are invariant under the
rational points of the minimal standard parabolic. -/
theorem constantTerm_minimalParabolic_invariant (Q : Idx) (g : ContinuousRationalFunctions F G)
    (r : A) (hr : r ∈ rationalImage F (𝓕.p B₀)) (x : A) :
    𝓕.constantTerm Q (evaluate F G g) (r * x) = 𝓕.constantTerm Q (evaluate F G g) x := by
  let := isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  obtain ⟨v, rfl⟩ := (mem_rationalImage_iff _ _).mp hr
  let vG := (𝓕.P B₀).affinePointsTarget (𝓕.p B₀) (CommAlgCat.of F F) v
  have hNormalizer : (rad(Q)).IsNormalizedBy (SubgroupFunctor.range (𝓕.p B₀)) := by
    intro U r u hr hu
    have hrQ := ((𝓕.le_iff_range_le B₀ Q).mp (empty_subset Q.val)) U hr
    rw [(𝓕.isCompatible Q).parabolic_eq] at hrQ
    rw [𝓕.range_radical_eq_standardUnipotent] at hu ⊢
    exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hrQ hu
  have hC (y : A) : 𝓕.constantTerm Q (evaluate F G g) y =
      normalizedConstantTerm F G rad(Q) g y :=
    (normalizedConstantTerm_range_eq_subgroupConstantTerm F G (𝓕.iU Q ≫ 𝓕.p Q) g y).symm
  rw [hC, hC, map_rational]
  exact normalizedConstantTerm_rationalNormalizer_mul F G rad(Q) hNormalizer ⟨vG, ⟨v, rfl⟩⟩ g x

/-- A continuous function invariant under the rational points of a standard radical has an
integrable constant-term integrand along it. -/
theorem integrable_radical_integrand (Q : Idx) {φ : A → ℂ} (hφ : Continuous φ)
    (hinv : ∀ q : RationalGroupPoints F (𝓕.U Q), ∀ x,
      φ (map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) q) * x) = φ x) (g : A) :
    haveI := isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
    Integrable (fun q : RationalQuotient F G rad(Q) =>
      φ (((Quotient.out q : adelicPoints F G rad(Q)) : A) * g))
      (normalizedRationalQuotientHaarMeasure F G rad(Q)) := by
  let := isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  let := rationalQuotientBorelSpace F G rad(Q)
  let m := normalizedRationalQuotientHaarMeasure F G rad(Q)
  let : IsProbabilityMeasure m :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G rad(Q)
  let b (n : adelicPoints F G rad(Q)) : ℂ := φ ((n : A) * g)
  have hb (gam : AdelicSubgroupPoints.rationalSubgroup F G rad(Q))
      (n : adelicPoints F G rad(Q)) : b (gam.val * n) = b n := by
    obtain ⟨q, hq⟩ := (mem_rationalSubgroup_range_iff (𝓕.iU Q ≫ 𝓕.p Q) gam.val).mp gam.2
    change map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) q) = gam.val.val at hq
    change φ (((gam.val : A) * n) * g) = φ ((n : A) * g)
    rw [mul_assoc, ← hq, hinv q]
  let B := LeftCosetSpace.lift (AdelicSubgroupPoints.rationalSubgroup F G rad(Q)) b hb
  have hB : Continuous B := LeftCosetSpace.continuous_lift _ _ _
    (hφ.comp (continuous_subtype_val.mul_const g))
  have hI := hB.integrable_of_hasCompactSupport («μ» := m) (HasCompactSupport.of_compactSpace _)
  refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G rad(Q))
      (Quotient.out x) = x := Quotient.out_eq x
  calc B x = b (Quotient.out x) := congrArg B hx.symm
    _ = _ := rfl

/-- The difference `C_J φ - C_{J ∖ α} φ` of nested constant terms. -/
def constantTermStep (J : Idx) (α : characterLattice 𝓕.T) (φ : A → ℂ) : A → ℂ :=
  𝓕.constantTerm J φ - 𝓕.constantTerm (𝓕.removeSimpleRoot J α) φ

/-- Rational points of the radical omitting `α` preserve the step. -/
theorem constantTermStep_rational_mul (J : Idx) (α : characterLattice 𝓕.T)
    (g : ContinuousRationalFunctions F G)
    (q : RationalGroupPoints F (𝓕.U (𝓕.omitSimpleRoot α))) (x : A) :
    𝓕.constantTermStep J α (evaluate F G g)
        (map F _ G (𝓕.iU (𝓕.omitSimpleRoot α) ≫ 𝓕.p (𝓕.omitSimpleRoot α))
          (rational F _ q) * x) =
      𝓕.constantTermStep J α (evaluate F G g) x := by
  have hr : map F _ G (𝓕.iU (𝓕.omitSimpleRoot α) ≫ 𝓕.p (𝓕.omitSimpleRoot α))
      (rational F _ q) ∈ rationalImage F (𝓕.p B₀) :=
    𝓕.radical_rationalImage_le_minimalParabolic (𝓕.omitSimpleRoot α) ⟨q, rfl⟩
  simp only [constantTermStep, Pi.sub_apply]
  rw [𝓕.constantTerm_minimalParabolic_invariant J g _ hr,
    𝓕.constantTerm_minimalParabolic_invariant (𝓕.removeSimpleRoot J α) g _ hr]

/-- **The step has vanishing constant term along the maximal parabolic omitting `α`.** -/
theorem constantTerm_constantTermStep (J : Idx) (α : characterLattice 𝓕.T)
    (g : ContinuousRationalFunctions F G) :
    𝓕.constantTerm (𝓕.omitSimpleRoot α) (𝓕.constantTermStep J α (evaluate F G g)) = 0 := by
  let M := 𝓕.omitSimpleRoot α
  let J₂ := 𝓕.removeSimpleRoot J α
  have h1 := 𝓕.constantTerm_constantTerm M J g
  have h2 := 𝓕.constantTerm_constantTerm M J₂ g
  have hi1 : 𝓕.interIndex M J = J₂ := by
    apply Subtype.ext
    change M.val ∩ J.val = J.val ∩ M.val
    exact Set.inter_comm _ _
  have hi2 : 𝓕.interIndex M J₂ = J₂ := by
    apply Subtype.ext
    change M.val ∩ (J.val ∩ M.val) = J.val ∩ M.val
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [hi1] at h1
  rw [hi2] at h2
  have hcont (Q : Idx) : Continuous (𝓕.constantTerm Q (evaluate F G g)) :=
    𝓕.continuous_constantTerm Q g
  have hinv (Q : Idx) (q : RationalGroupPoints F (𝓕.U M)) (x : A) :
      𝓕.constantTerm Q (evaluate F G g)
          (map F (𝓕.U M) G (𝓕.iU M ≫ 𝓕.p M) (rational F (𝓕.U M) q) * x) =
        𝓕.constantTerm Q (evaluate F G g) x :=
    𝓕.constantTerm_minimalParabolic_invariant Q g _
      (𝓕.radical_rationalImage_le_minimalParabolic M ⟨q, rfl⟩) x
  funext x
  have hI1 := 𝓕.integrable_radical_integrand M (hcont J) (hinv J) x
  have hI2 := 𝓕.integrable_radical_integrand M (hcont J₂) (hinv J₂) x
  have e1 := congrFun h1 x
  have e2 := congrFun h2 x
  simp only [constantTerm, subgroupConstantTerm, Pi.zero_apply] at e1 e2 ⊢
  simp only [constantTermStep, Pi.sub_apply]
  rw [integral_sub hI1 hI2]
  change _ - _ = (0 : ℂ)
  rw [sub_eq_zero]
  exact e1.trans e2.symm

theorem constantTerm_mul_ofFinite (Q : Idx) {φ : A → ℂ}
    {L : Subgroup (FiniteAdelicGroupPoints F G)}
    (hφ : ∀ l ∈ L, ∀ x, φ (x * ofFinite F G l) = φ x) :
    ∀ l ∈ L, ∀ x, 𝓕.constantTerm Q φ (x * ofFinite F G l) = 𝓕.constantTerm Q φ x := by
  intro l hl x
  simp only [constantTerm, subgroupConstantTerm]
  congr 1
  funext q
  rw [← mul_assoc, hφ l hl]

section Decay

variable {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (rT : T₀ ⟶ 𝓕.T)

local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Jw" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i T₀ rT

/-- **Decay of a constant-term step** (Mœglin–Waldspurger I.2.10 through
`adelicMaximalUnipotentDecay`). For a simple root `α`, compact sets `K` of right factors and
`Y_f` of finite coordinates, an open level `L`, a threshold `b` and `n`, there are a compact
`K' ⊇ K` and `C ≥ 0` with the following property. Let `g` be a continuous `G(F)`-invariant
function, smooth on archimedean slices and right `L`-invariant. Let `a` lie in the weak
simple-root chamber of threshold `b`, let `k ∈ K` with `finite(aG(a) k) ∈ Y_f`, and let `M ≥ 0`
bound the derivatives of order `n` of the step `C_J g - C_{J ∖ α} g` at the points `aG(a) k'`,
`k' ∈ K'` with the same finite coordinate as `k`. Then the step at `aG(a) k` is bounded by
`C |α(a)|^{-n/[F:ℚ]} M`. -/
theorem exists_constantTermStep_decay (J : Idx) {α : characterLattice 𝓕.T} (hα : α ∈ Δ)
    (L : Subgroup Gf) (hL : IsOpen (L : Set Gf)) (b : ℝ≥0ˣ) (n : ℕ) (K : Set A)
    (hK : IsCompact K) (Yf : Set Gf) (hYf : IsCompact Yf) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : ContinuousRationalFunctions F G,
      (∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => evaluate F G g (pair F G y c))) →
      (∀ l ∈ L, ∀ x, evaluate F G g (x * ofFinite F G l) = evaluate F G g x) →
      ∀ a ∈ weakSimpleRootChamber F T₀ 𝓕.T rT G 𝓕.i 𝓕.ν b, ∀ k ∈ K,
      finite F G (aG a * k) ∈ Yf → ∀ M : ℝ, 0 ≤ M →
      (∀ k' ∈ K', finite F G k' = finite F G k → ∀ s : List Jw, s.length = n →
        ‖adelicIteratedDirectionalValue hG (s.map basisG)
          (𝓕.constantTermStep J α (evaluate F G g)) (aG a * k')‖ ≤ M) →
      ‖𝓕.constantTermStep J α (evaluate F G g) (aG a * k)‖ ≤
        C * (relativeCharacterDecay rT α a) ^ n * M := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let M' := 𝓕.omitSimpleRoot α
  let j := 𝓕.iU M' ≫ 𝓕.p M'
  let hgeom := (𝓕.isUnipotentRadical M').isGeometricUnipotentRadical
  obtain ⟨dU, hU⟩ := Classical.indefiniteDescription _
    (Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension (𝓕.U M').X.left _
      (𝓕.U M').X.hom hgeom.2.1 hgeom.2.2.1)
  have hΩ : ({1} : Set A) ⊆
      (Subgroup.normalizer ((MonoidHom.range (ContinuousMonoidHom.toMonoidHom
        (map F (𝓕.U M') G j))) : Set A) : Set A) := by
    intro p hp
    rw [Set.mem_singleton_iff.mp hp]
    exact Subgroup.one_mem _
  obtain ⟨K', hK', hKK', C, hC, hdec⟩ := adelicMaximalUnipotentDecay hG (dU := dU) 𝓕.i 𝓕.ν rT j
    𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic hU hgeom.2.2.1 hgeom.2.2.2.1
    α hα (𝓕.range_radical_eq_standardUnipotent M') {1} isCompact_singleton hΩ
    Yf hYf L hL b n K hK
  refine ⟨K', hK', hKK', C, hC, ?_⟩
  intro g hgS hgL a ha k hk hx M hM hbound
  -- regularity of the two constant terms
  have hreg (Q : Idx) :
      (∀ c : Gf, ContMDiff IG IC ∞ (fun y : G∞ => 𝓕.constantTerm Q (evaluate F G g)
        (pair F G y c))) := by
    have hQ := (𝓕.isUnipotentRadical Q).isGeometricUnipotentRadical
    have hinvQ : ∀ (q : RationalGroupPoints F (𝓕.U Q)) x,
        evaluate F G g (map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) q) * x) =
          evaluate F G g x := by
      intro q x
      rw [map_rational]
      exact evaluate_rational_mul F G g _ x
    have hD := adelicUnipotentConstantTermDifferentiation (𝓕.iU Q ≫ 𝓕.p Q) hG hQ.2.1
      hQ.2.2.1 hQ.2.2.2.1 L hL (evaluate F G g) g.property hgS hinvQ hgL
    exact fun c => (hD.2 c).1
  have hfS : ∀ c : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => 𝓕.constantTermStep J α (evaluate F G g) (pair F G y c)) := by
    intro c
    exact (hreg J c).sub (hreg (𝓕.removeSimpleRoot J α) c)
  have hfC : Continuous (𝓕.constantTermStep J α (evaluate F G g)) :=
    (𝓕.continuous_constantTerm J g).sub (𝓕.continuous_constantTerm _ g)
  have hfL : ∀ l ∈ L, ∀ x, 𝓕.constantTermStep J α (evaluate F G g) (x * ofFinite F G l) =
      𝓕.constantTermStep J α (evaluate F G g) x := by
    intro l hl x
    simp only [constantTermStep, Pi.sub_apply, 𝓕.constantTerm_mul_ofFinite J hgL l hl,
      𝓕.constantTerm_mul_ofFinite _ hgL l hl]
  have hfR := 𝓕.constantTermStep_rational_mul J α g
  have hCT := 𝓕.constantTerm_constantTermStep J α g
  have hx' : finite F G (1 * aG a * k) ∈ Yf := by rwa [one_mul]
  have := hdec 1 (Set.mem_singleton 1) a ha k hk hx'
    (𝓕.constantTermStep J α (evaluate F G g)) hfC hfS hfR hfL hCT M hM
    (fun k' hk' hfin s hs => by rw [one_mul]; exact hbound k' hk' hfin s hs)
  rwa [one_mul] at this

end Decay

end Langlands.Global.StandardParabolicFamily
