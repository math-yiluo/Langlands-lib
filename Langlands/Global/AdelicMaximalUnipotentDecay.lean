import Langlands.Global.AdelicMaximalUnipotentOscillation

/-! # Iterated decay from a vanishing maximal-parabolic constant term -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints
  AdelicSiegelFactors PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {dG : ℕ} (hG : SmoothOfRelativeDimension dG G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "W" => smoothModel F dG
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "J" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W

section BasisDerivative

variable [IsAffine G.X.left]

/-- Compose right-orbit derivatives in the order of a word in the tangent directions. -/
def adelicIteratedDirectionalValue (s : List W) (f : A → ℂ) : A → ℂ :=
  s.foldr (adelicDirectionalValue hG) f

@[simp]
theorem adelicIteratedDirectionalValue_nil (f : A → ℂ) :
    adelicIteratedDirectionalValue hG [] f = f := rfl

@[simp]
theorem adelicIteratedDirectionalValue_cons (X : W) (s : List W) (f : A → ℂ) :
    adelicIteratedDirectionalValue hG (X :: s) f =
      adelicDirectionalValue hG X (adelicIteratedDirectionalValue hG s f) := rfl

theorem adelicIteratedDirectionalValue_append (s t : List W) (f : A → ℂ) :
    adelicIteratedDirectionalValue hG (s ++ t) f =
      adelicIteratedDirectionalValue hG s (adelicIteratedDirectionalValue hG t f) :=
  List.foldr_append

end BasisDerivative

section Chamber

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (rT : T₀ ⟶ T)
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {dU : ℕ}

local notation "m" => map F U G j
local notation "V" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom m)
local notation "aG" => positiveMap F G T i T₀ rT

/-- For a function whose maximal-parabolic constant term vanishes, each additional
derivative in the bound gains one more inverse power of the corresponding simple
root's archimedean scalar, on an enlarged compact set of right factors. -/
def AdelicMaximalUnipotentDecayStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  SmoothOfRelativeDimension dU U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
  ∀ α ∈ simpleRelativeRoots i ν,
  SubgroupFunctor.range j = standardUnipotent i ν (simpleRelativeRoots i ν \ {α}) →
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (Ω : Set A), IsCompact Ω → Ω ⊆ (Subgroup.normalizer (V : Set A) : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (b : ℝ≥0ˣ) (n : ℕ) (K : Set A), IsCompact K →
  ∃ K' : Set A, IsCompact K' ∧ K ⊆ K' ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ p ∈ Ω, ∀ a ∈ weakSimpleRootChamber F T₀ T rT G i ν b,
    ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
    ∀ (f : A → ℂ), Continuous f →
    (∀ v : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y v))) →
    (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
    (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
    subgroupConstantTerm F j f = 0 →
    ∀ M : ℝ, 0 ≤ M →
    (∀ k' ∈ K', finite F G k' = finite F G k → ∀ s : List J, s.length = n →
      ‖adelicIteratedDirectionalValue hG (s.map basisG) f (p * aG a * k')‖ ≤ M) →
    ‖f (p * aG a * k)‖ ≤ C * (relativeCharacterDecay rT α a) ^ n * M

theorem adelicMaximalUnipotentDecay :
    AdelicMaximalUnipotentDecayStatement hG (dU := dU) i ν rT j := by
  intro hRed hi hν hU hconn hu α hα hStd
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro Ω hΩ hNorm Yf hY L hL b n
  have hOne := adelicMaximalUnipotentOscillation (dU := dU) i ν rT j hG
    hRed hi hν hU hconn hu α hα hStd Ω hΩ hNorm Yf hY L hL b
  induction n with
  | zero =>
    intro K hK
    refine ⟨K, hK, subset_rfl, 1, zero_le_one, ?_⟩
    intro p _ a _ k hk _ f _ _ _ _ _ M _ hM
    simpa only [pow_zero, one_mul, List.map_nil, adelicIteratedDirectionalValue_nil] using
      hM k hk rfl [] rfl
  | succ n ih =>
    intro K hK
    obtain ⟨K₁, hK₁, hKK₁, C₁, hC₁, hone⟩ := hOne K hK
    obtain ⟨K', hK', hK₁K', C₂, hC₂, hiter⟩ := ih K₁ hK₁
    refine ⟨K', hK', hKK₁.trans hK₁K', C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
    intro p hp a ha k hk hx f hf hfS hfR hfL hfCT M hM hBound
    let r := relativeCharacterDecay rT α a
    have hr : 0 ≤ r := (relativeCharacterDecay_pos rT α a).le
    have hDiff := adelicUnipotentConstantTermDifferentiation j hG hU.smooth hconn hu L hL f hf hfS hfR hfL
    have hdCT (X : W) : subgroupConstantTerm F j (adelicDirectionalValue hG X f) = 0 := by
      funext z
      conv_lhs => rw [← pair_projections F G z]
      rw [← (hDiff.2 (finite F G z)).2 X (infinite F G z), hfCT]
      simp [groupDirectionalValue, mvfderiv]
    have hDer (k' : A) (hk' : k' ∈ K₁) (hk'f : finite F G k' = finite F G k) (l : J) :
        ‖adelicDirectionalValue hG (basisG l) f (p * aG a * k')‖ ≤ C₂ * r ^ n * M := by
      have hx' : finite F G (p * aG a * k') ∈ Yf := by
        rwa [map_mul, hk'f, ← map_mul]
      obtain ⟨hd, hdS, hdR, hdL⟩ := hDiff.1 (basisG l)
      refine hiter p hp a ha k' hk' hx' _ hd hdS hdR hdL (hdCT (basisG l)) M hM ?_
      intro k'' hk'' hk''f s hs
      simpa only [List.map_append, List.map_cons, List.map_nil, adelicIteratedDirectionalValue_append,
        adelicIteratedDirectionalValue_cons, adelicIteratedDirectionalValue_nil] using
          hBound k'' hk'' (hk''f.trans hk'f)
          (s ++ [l]) (by simp [hs])
    have h := hone p hp a ha k hk hx f hf hfS hfR hfL (C₂ * r ^ n * M)
      (mul_nonneg (mul_nonneg hC₂ (pow_nonneg hr _)) hM) hDer
    rw [hfCT, Pi.zero_apply, sub_zero] at h
    calc
      ‖f (p * aG a * k)‖ ≤ C₁ * r * (C₂ * r ^ n * M) := h
      _ = (C₁ * C₂) * r ^ (n + 1) * M := by rw [pow_succ]; ring

end Chamber

end Langlands.Global
