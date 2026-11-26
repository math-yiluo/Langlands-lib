import Langlands.Global.AdelicMaximalUnipotentDecay

/-! # Iterated decay from contraction modulo a left invariance subgroup -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Pointwise

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "m" => map F U G j
local notation "J" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W

variable {X : Type v} {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- After left multiplication by the subgroup `L₀`, the displacement by an
archimedean unipotent point has a coordinate of size proportional to `ε`. -/
def HasUnipotentContractionModulo (Ω : Set A) (a : X → A) (L₀ : Subgroup A)
    (Ψ : E → G∞) (ε : X → ℝ) : Prop :=
  ∀ D : Set U∞, IsCompact D → ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ω, ∀ t : X, ∀ u ∈ D, ∃ v : E, ‖v‖ ≤ C * ε t ∧
      ∃ l : A, l ∈ L₀ ∧ m (ofInfinite F U u) * (p * a t) = l * ((p * a t) * ofInfinite F G (Ψ v))

set_option maxHeartbeats 600000 in
/-- One application of the mean-value inequality compares the function with
its constant term and gains the contraction factor. -/
private theorem unipotentOscillationModulo
    [FiniteDimensional ℝ E]
    (Ω : Set A) (a : X → A) (L₀ : Subgroup A) (Ψ : E → G∞) (ε : X → ℝ)
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (Bε : ℝ) (hBε : 0 ≤ Bε) (hεB : ∀ t, ε t ≤ Bε)
    (hconj : HasUnipotentContractionModulo (F := F) (X := X) (E := E) j Ω a L₀ Ψ ε)
    (hΨ₀ : Ψ 0 = 1)
    (Yf : Set Gf) (hY : IsCompact Yf) (L : Subgroup Gf) (hL : IsOpen (L : Set Gf))
    (K : Set A) (hK : IsCompact K) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Ω, ∀ t : X, ∀ k ∈ K, finite F G (p * a t * k) ∈ Yf →
      ∀ f : A → ℂ, Continuous f →
      (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b))) →
      (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
      (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
      (∀ l ∈ L₀, ∀ x, f (l * x) = f x) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ k' ∈ K', finite F G k' = finite F G k → ∀ l : J,
        ‖adelicDirectionalValue hG (basisG l) f (p * a t * k')‖ ≤ M) →
      ‖f (p * a t * k) - subgroupConstantTerm F j f (p * a t * k)‖ ≤ C * ε t * M := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  let : Smooth U.X.hom := hUs
  intro hΨ
  obtain ⟨D, hD, hrep⟩ := adelicUnipotentArchimedeanRepresentatives j hconn hu Yf hY L hL
  obtain ⟨C₀, hC₀, hCconj⟩ := hconj D hD
  let B := C₀ * Bε
  have hB : 0 ≤ B := mul_nonneg hC₀ hBε
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
  intro p hp t k hk hfinite f hf hfS hfR hfL hfL₀ M hM hDer
  let x := p * a t * k
  let fS (z : G∞) := f (pair F G z (finite F G x))
  have hpt (v : E) : pair F G (infinite F G (p * a t) * Ψ v * infinite F G k) (finite F G x) =
      p * a t * (ofInfinite F G (Ψ v) * k) := by
    apply (split F G).injective
    rw [split_apply, split_apply]
    simp only [infinite_pair, finite_pair, x, map_mul, infinite_ofInfinite,
      finite_ofInfinite, one_mul, mul_assoc]
  have hbound (v : E) (hv : v ∈ S) (l : J) :
      ‖groupDirectionalValue IG (basisG l) fS (infinite F G (p * a t) * Ψ v * infinite F G k)‖ ≤ M := by
    let k' := ofInfinite F G (Ψ v) * k
    have hk' : k' ∈ K' := Set.mem_mul.mpr ⟨_, ⟨v, hv, rfl⟩, k, hk, rfl⟩
    have hk'f : finite F G k' = finite F G k := by simp [k']
    have hd := hDer k' hk' hk'f l
    change ‖adelicDirectionalValue hG (basisG l) f (p * a t * (ofInfinite F G (Ψ v) * k))‖ ≤ M at hd
    rw [← hpt, adelicDirectionalValue_pair] at hd
    exact hd
  apply norm_sub_subgroupConstantTerm_le j hUs hconn hu f hf hfR x
  intro u
  obtain ⟨u₀, hu₀, q, hq⟩ := hrep u
  obtain ⟨l, hl⟩ := hq x hfinite
  rw [← hfR q (m u * x), hl, hfL l.val l.property]
  obtain ⟨v, hv, l₀, hl₀, he⟩ := hCconj p hp t u₀ hu₀
  have hvS : v ∈ S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hv.trans (mul_le_mul_of_nonneg_left (hεB t) hC₀)
  have he' : m (ofInfinite F U u₀) * x = l₀ * (p * a t * (ofInfinite F G (Ψ v) * k)) := by
    simp only [x, ← mul_assoc, he]
  have hh := hMean (infinite F G k) ⟨k, hk, rfl⟩ v hvS (infinite F G (p * a t))
    fS (hfS _) M hM hbound
  have h₀ : p * a t * (ofInfinite F G (Ψ 0) * k) = x := by simp only [hΨ₀, map_one, one_mul, x]
  change ‖f (pair F G _ (finite F G x)) - f (pair F G _ (finite F G x))‖ ≤ _ at hh
  rw [hpt, hpt, h₀] at hh
  rw [he', hfL₀ l₀ hl₀]
  calc
    _ ≤ C₁ * ‖v‖ * M := hh
    _ ≤ C₁ * (C₀ * ε t) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC₁) hM
    _ = _ := by ring

/-- On a region with archimedean unipotent contraction modulo a left
invariance subgroup, vanishing of the unipotent constant term gives a
gain of one contraction factor per derivative order. -/
def AdelicUnipotentDecayModuloStatement (Ω : Set A) (a : X → A) (L₀ : Subgroup A)
    (Ψ : E → G∞) (ε : X → ℝ) : Prop :=
  FiniteDimensional ℝ E →
  Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
  (∀ t, 0 ≤ ε t) → (∃ B : ℝ, 0 ≤ B ∧ ∀ t, ε t ≤ B) →
  HasUnipotentContractionModulo (F := F) (X := X) (E := E) j Ω a L₀ Ψ ε → Ψ 0 = 1 →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (n : ℕ) (K : Set A), IsCompact K →
  ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ω, ∀ t : X, ∀ k ∈ K, finite F G (p * a t * k) ∈ Yf →
    ∀ f : A → ℂ, Continuous f →
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b))) →
    (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
    (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
    (∀ l ∈ L₀, ∀ x, f (l * x) = f x) →
    subgroupConstantTerm F j f = 0 →
    ∀ M : ℝ, 0 ≤ M →
    (∀ k' ∈ K', finite F G k' = finite F G k → ∀ s : List J, s.length = n →
      ‖adelicIteratedDirectionalValue hG (s.map basisG) f (p * a t * k')‖ ≤ M) →
    ‖f (p * a t * k)‖ ≤ C * ε t ^ n * M

set_option maxHeartbeats 600000 in
theorem adelicUnipotentDecayModulo
    (Ω : Set A) (a : X → A) (L₀ : Subgroup A) (Ψ : E → G∞) (ε : X → ℝ) :
    AdelicUnipotentDecayModuloStatement (F := F) (X := X) (E := E) j hG Ω a L₀ Ψ ε := by
  intro hE hUs hconn hu hε ⟨B, hB, hεB⟩ hconj hΨ₀
  let : FiniteDimensional ℝ E := hE
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro hΨ Yf hY L hL n
  have hOne := fun K hK => unipotentOscillationModulo j hG Ω a L₀ Ψ ε hUs hconn hu B hB hεB
    hconj hΨ₀ Yf hY L hL K hK hΨ
  induction n with
  | zero =>
    intro K hK
    refine ⟨K, hK, subset_rfl, 1, zero_le_one, ?_⟩
    intro p _ t k hk _ f _ _ _ _ _ _ M _ hM
    simpa only [pow_zero, one_mul, List.map_nil, adelicIteratedDirectionalValue_nil] using
      hM k hk rfl [] rfl
  | succ n ih =>
    intro K hK
    obtain ⟨K₁, hK₁, hKK₁, C₁, hC₁, hone⟩ := hOne K hK
    obtain ⟨K', hK', hK₁K', C₂, hC₂, hiter⟩ := ih K₁ hK₁
    refine ⟨K', hK', hKK₁.trans hK₁K', C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
    intro p hp t k hk hx f hf hfS hfR hfL hfL₀ hfCT M hM hBound
    have hDiff := adelicUnipotentConstantTermDifferentiation j hG hUs hconn hu L hL f hf hfS hfR hfL
    have hdCT (X : W) : subgroupConstantTerm F j (adelicDirectionalValue hG X f) = 0 := by
      funext z
      conv_lhs => rw [← pair_projections F G z]
      rw [← (hDiff.2 (finite F G z)).2 X (infinite F G z), hfCT]
      simp [groupDirectionalValue, mvfderiv]
    have hdL₀ (X : W) (l : A) (hl : l ∈ L₀) (z : A) :
        adelicDirectionalValue hG X f (l * z) = adelicDirectionalValue hG X f z := by
      unfold adelicDirectionalValue
      apply congrArg (fun w : G∞ → ℂ => mvfderiv IG w 1 X)
      funext b
      rw [mul_assoc, hfL₀ l hl]
    have hDer (k' : A) (hk' : k' ∈ K₁) (hk'f : finite F G k' = finite F G k) (l : J) :
        ‖adelicDirectionalValue hG (basisG l) f (p * a t * k')‖ ≤ C₂ * ε t ^ n * M := by
      have hx' : finite F G (p * a t * k') ∈ Yf := by rwa [map_mul, hk'f, ← map_mul]
      obtain ⟨hd, hdS, hdR, hdL⟩ := hDiff.1 (basisG l)
      refine hiter p hp t k' hk' hx' _ hd hdS hdR hdL (hdL₀ (basisG l)) (hdCT (basisG l)) M hM ?_
      intro k'' hk'' hk''f s hs
      simpa only [List.map_append, List.map_cons, List.map_nil, adelicIteratedDirectionalValue_append,
        adelicIteratedDirectionalValue_cons, adelicIteratedDirectionalValue_nil] using
          hBound k'' hk'' (hk''f.trans hk'f) (s ++ [l]) (by simp [hs])
    have h := hone p hp t k hk hx f hf hfS hfR hfL hfL₀ (C₂ * ε t ^ n * M)
      (mul_nonneg (mul_nonneg hC₂ (pow_nonneg (hε t) _)) hM) hDer
    rw [hfCT, Pi.zero_apply, sub_zero] at h
    calc
      ‖f (p * a t * k)‖ ≤ C₁ * ε t * (C₂ * ε t ^ n * M) := h
      _ = (C₁ * C₂) * ε t ^ (n + 1) * M := by rw [pow_succ]; ring

end Langlands.Global
