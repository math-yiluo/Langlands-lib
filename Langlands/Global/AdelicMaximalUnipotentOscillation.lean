import Langlands.Global.AdelicMaximalUnipotentContraction
import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicUnipotentArchimedeanRepresentatives
import Langlands.Geometry.Manifold.SmoothGroupCompactCoordinateEstimate

/-! # A chamber-dependent estimate for the maximal-parabolic constant term -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal Pointwise

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints
  AdelicSiegelFactors PositiveRealTorus

section ConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "m" => map F U G j
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν₀" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V

/-- A uniform bound on the differences with unipotent translates passes to the
normalized constant term. -/
theorem norm_sub_subgroupConstantTerm_le (hUs : Smooth U.X.hom)
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (f : A → ℂ) (hf : Continuous f)
    (hfR : ∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x)
    (x : A) {B : ℝ} (hB : ∀ u : AdelicGroupPoints F U, ‖f (m u * x) - f x‖ ≤ B) :
    ‖f x - subgroupConstantTerm F j f x‖ ≤ B := by
  let : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hUs hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν₀ := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let a (q : Q) := f ((Quotient.out q : H).val * x)
  let φ := LeftCosetSpace.lift Γ (fun y : H => f (y.val * x)) (fun r y => by
    obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
    change f ((r.val.val * y.val) * x) = _
    rw [← hr₀, mul_assoc]
    exact hfR r₀ (y.val * x))
  have hφ : Continuous φ :=
    (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
  have heq : a = φ := funext fun q => congrArg φ (Quotient.out_eq q)
  have hai : Integrable a ν₀ :=
    heq ▸ hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd (q : Q) : ‖f x - a q‖ ≤ B := by
    obtain ⟨u, huq⟩ := AdelicSubgroupPoints.adelicRangeMap_surjective F j (Quotient.out q)
    change ‖f x - f ((Quotient.out q : H).val * x)‖ ≤ B
    rw [← congrArg Subtype.val huq, norm_sub_rev]
    exact hB u
  change ‖f x - ∫ q, a q ∂ν₀‖ ≤ B
  have hc : (∫ _ : Q, f x ∂ν₀) = f x := by simp
  rw [← hc, ← integral_sub (integrable_const _) hai]
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall hbd)).trans_eq (by simp)

end ConstantTerm

section Chamber

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (rT : T₀ ⟶ T)
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {dU dG : ℕ} (hG : SmoothOfRelativeDimension dG G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "Aₐ" => CommAlgCat.of F (Adeles F)
local notation "A∞" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "W" => smoothModel F dG
local notation "IG" => 𝓘(ℝ, W)
local notation "IU" => 𝓘(ℝ, smoothModel F dU)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "basisG" => Module.finBasis ℝ W
local notation "j∞" => U.affinePointsTarget j A∞
local notation "m" => map F U G j
local notation "R" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom m)
local notation "aG" => positiveMap F G T i T₀ rT

/-- The deviation from the maximal-parabolic constant term gains one power of inverse
archimedean root scale, using only first invariant derivatives on enlarged compact
right factors with the same finite coordinate at each evaluation. -/
def AdelicMaximalUnipotentOscillationStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  SmoothOfRelativeDimension dU U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
  ∀ α ∈ simpleRelativeRoots i ν,
  SubgroupFunctor.range j = standardUnipotent i ν (simpleRelativeRoots i ν \ {α}) →
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (Ω : Set A), IsCompact Ω → Ω ⊆ (Subgroup.normalizer (R : Set A) : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (b : ℝ≥0ˣ) (K : Set A), IsCompact K →
  ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ω, ∀ a ∈ weakSimpleRootChamber F T₀ T rT G i ν b,
    ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
    ∀ (f : A → ℂ), Continuous f →
    (∀ v : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y v))) →
    (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
    (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
    ∀ M : ℝ, 0 ≤ M →
    (∀ k' ∈ K', finite F G k' = finite F G k → ∀ l : Fin (Module.finrank ℝ W),
      ‖adelicDirectionalValue hG (basisG l) f (p * aG a * k')‖ ≤ M) →
    ‖f (p * aG a * k) - subgroupConstantTerm F j f (p * aG a * k)‖ ≤
      C * relativeCharacterDecay rT α a * M

theorem adelicMaximalUnipotentOscillation :
    AdelicMaximalUnipotentOscillationStatement (dU := dU) i ν rT j hG := by
  intro hRed hi hν hU hconn hu α hα hStd
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F U hU
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  let : Smooth U.X.hom := hU.smooth
  intro Ω hΩ hNorm Yf hY L hL b K hK
  obtain ⟨D, hD, hrep⟩ := adelicUnipotentArchimedeanRepresentatives j hconn hu Yf hY L hL
  obtain ⟨n, Q, hQ₀, hQs, hconj⟩ := adelicMaximalUnipotentContraction i ν rT j hU
    hRed hi hν α hα inferInstance hStd
  let E := Fin n → mixedEmbedding.mixedSpace F
  let Ψ : E → G∞ := fun v => j∞ (Q.symm v)
  have hΨ : ContMDiff 𝓘(ℝ, E) IG ∞ Ψ := by
    have hj : ContMDiff IU IG ∞ j∞ := by
      apply (contMDiff_iff_coordinateSmooth F G IU hG _).mpr
      exact ((contMDiff_iff_coordinateSmooth F U IU hU id).mp contMDiff_id).postcomp j.hom.hom
    exact hj.comp hQs
  have hΨ₀ : Ψ 0 = 1 := by
    change j∞ (Q.symm 0) = 1
    rw [← hQ₀, Q.symm_apply_apply, map_one]
  have hi_map (z : AdelicGroupPoints F U) : infinite F G (m z) = j∞ (infinite F U z) :=
    DFunLike.congr_fun (U.affinePointsTarget_naturality j
      (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeles F)))) z
  have hmInf (u : U∞) : m (ofInfinite F U u) = ofInfinite F G (j∞ u) := by
    apply (split F G).injective
    simp only [split_apply, hi_map, finite_map, infinite_ofInfinite, finite_ofInfinite, map_one]
  let W₀ (pu : A × U∞) := pu.1⁻¹ * m (ofInfinite F U pu.2) * pu.1
  have hW₀ : Continuous W₀ :=
    (continuous_fst.inv.mul (((m).continuous.comp (ofInfinite F U).continuous).comp continuous_snd)).mul
      continuous_fst
  let ΩU := m ⁻¹' (W₀ '' (Ω ×ˢ D))
  have hm : IsClosedEmbedding m := isClosedEmbedding_map_of_isClosedSubgroup F j
    (show IsClosedImmersion j.hom.hom.left from inferInstance)
  have hΩU : IsCompact ΩU := hm.isCompact_preimage ((hΩ.prod hD).image hW₀)
  obtain ⟨C₀, hC₀, hCconj⟩ := hconj ΩU hΩU b
  let e : ℝ := -1 / (Module.finrank ℚ F : ℝ)
  let B := C₀ * ((b : ℝ≥0) : ℝ) ^ e
  have hB : 0 ≤ B := mul_nonneg hC₀ (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
  have hscale (a : intrinsicSubgroup F T₀) (ha : a ∈ weakSimpleRootChamber F T₀ T rT G i ν b) :
      relativeCharacterDecay rT α a ≤ ((b : ℝ≥0) : ℝ) ^ e := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast b.ne_zero.bot_lt
    · exact_mod_cast (Units.val_le_val.mpr (ha α hα))
    · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)
  let S := Metric.closedBall (0 : E) B
  let K' := ((ofInfinite F G) ∘ Ψ '' S) * K
  have hK' : IsCompact K' :=
    ((isCompact_closedBall (0 : E) B).image ((ofInfinite F G).continuous.comp hΨ.continuous)).mul hK
  have hKK' : K ⊆ K' := by
    intro k hk
    refine Set.mem_mul.mpr ⟨_, ⟨0, Metric.mem_closedBall_self hB, rfl⟩, k, hk, ?_⟩
    simp only [Function.comp_apply, hΨ₀, map_one, one_mul]
  obtain ⟨C₁, hC₁, hMean⟩ := smoothGroupCompactCoordinateEstimate («W» := W) Ψ
    hΨ (infinite F G '' K) (hK.image (infinite F G).continuous) B hB
  refine ⟨K', hK', hKK', C₁ * C₀, mul_nonneg hC₁ hC₀, ?_⟩
  intro p hp a ha k hk hfinite f hf hfS hfR hfL M hM hDer
  let x := p * aG a * k
  let fS (z : G∞) := f (pair F G z (finite F G x))
  have hpt (v : E) : pair F G (infinite F G (p * aG a) * Ψ v * infinite F G k) (finite F G x) =
      p * aG a * (ofInfinite F G (Ψ v) * k) := by
    apply (split F G).injective
    rw [split_apply, split_apply]
    simp only [infinite_pair, finite_pair, x, map_mul, infinite_ofInfinite,
      finite_ofInfinite, one_mul, mul_assoc]
  have hbound (v : E) (hv : v ∈ S) (l : Fin (Module.finrank ℝ W)) :
      ‖groupDirectionalValue IG (basisG l) fS (infinite F G (p * aG a) * Ψ v * infinite F G k)‖ ≤ M := by
    let k' := ofInfinite F G (Ψ v) * k
    have hk' : k' ∈ K' := Set.mem_mul.mpr ⟨_, ⟨v, hv, rfl⟩, k, hk, rfl⟩
    have hk'f : finite F G k' = finite F G k := by simp [k']
    have hd := hDer k' hk' hk'f l
    change ‖adelicDirectionalValue hG (basisG l) f (p * aG a * (ofInfinite F G (Ψ v) * k))‖ ≤ M at hd
    rw [← hpt, adelicDirectionalValue_pair] at hd
    exact hd
  apply norm_sub_subgroupConstantTerm_le j hU.smooth hconn hu f hf hfR x
  intro u
  obtain ⟨u₀, hu₀, q, hq⟩ := hrep u
  obtain ⟨l, hl⟩ := hq x hfinite
  rw [← hfR q (m u * x), hl, hfL l.val l.property]
  have hpu : W₀ (p, u₀) ∈ R := by
    change p⁻¹ * m (ofInfinite F U u₀) * p ∈ R
    have hn : p⁻¹ ∈ Subgroup.normalizer (R : Set A) := inv_mem (hNorm hp)
    have hu' : m (ofInfinite F U u₀) ∈ R := ⟨ofInfinite F U u₀, rfl⟩
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn (m (ofInfinite F U u₀))).mp hu'
  obtain ⟨z, hz⟩ := hpu
  change m z = W₀ (p, u₀) at hz
  have hzΩ : z ∈ ΩU := ⟨(p, u₀), ⟨hp, hu₀⟩, hz.symm⟩
  obtain ⟨y, hy, hyNorm⟩ := hCconj z hzΩ a ha
  have hyf : finite F G (m y) = 1 := by
    rw [← hy, hz]
    simp only [W₀, hmInf, map_mul, map_inv, finite_ofInfinite, mul_one, inv_mul_cancel]
  let v : E := Q (infinite F U y)
  have hvS : v ∈ S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hyNorm.trans (mul_le_mul_of_nonneg_left (hscale a ha) hC₀)
  have hyInf : m y = ofInfinite F G (Ψ v) := by
    apply (split F G).injective
    simp only [split_apply, hi_map, hyf, infinite_ofInfinite, finite_ofInfinite, Ψ, v,
      Q.symm_apply_apply]
  have he : m (ofInfinite F U u₀) * x = p * aG a * (ofInfinite F G (Ψ v) * k) := by
    rw [← hyInf, ← hy, hz]
    dsimp only [W₀, x]
    group
  have h := hMean (infinite F G k) ⟨k, hk, rfl⟩ v hvS (infinite F G (p * aG a))
    fS (hfS _) M hM hbound
  have h0 : p * aG a * (ofInfinite F G (Ψ 0) * k) = x := by simp only [hΨ₀, map_one, one_mul, x]
  change ‖f (pair F G _ (finite F G x)) - f (pair F G _ (finite F G x))‖ ≤ _ at h
  rw [hpt, hpt, h0] at h
  rw [he]
  exact h.trans (by
    calc
      C₁ * ‖v‖ * M ≤ (C₁ * (C₀ * relativeCharacterDecay rT α a)) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyNorm hC₁) hM
      _ = (C₁ * C₀) * relativeCharacterDecay rT α a * M := by ring)

end Chamber

end Langlands.Global
