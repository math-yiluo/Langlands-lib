import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RightFiniteUniqueness
import Langlands.Representation.Jacquet.StandardCasselmanConstantTerm
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction

/-! # Weak and positive constant terms of actual orbit coefficients (Waldspurger VI.2.3)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus `S`,
a generic cocharacter, an actual standard parabolic `P = P_I(F)` with the inducing data of
`rationalInducedOrbitCoefficientMap` and a second actual standard parabolic `P' = P_{I'}(F)` with a
compatible split component `A` of `M' = M_{I'}`, this module defines

* the weak and positive parts of a function on a group along the right translations by a
  commutative group (`weakPart`, `positivePart`): the sum of the generalized eigencomponents with
  unitary exponents, and the rest;
* the constant term `(f_ω)_{P'}` of the orbit coefficient `f_ω = E^G_P ψ_ω` and its weak and
  positive parts (`rationalOrbitConstantTerm`, `rationalOrbitWeakConstantTerm`,
  `rationalOrbitPositiveConstantTerm`);
* Waldspurger's `H_0` on the actual minimal Levi `M_0(F) = Z_G(S)(F)` (`rationalMinimalH0`), the
  closed chamber `M̄_0^+` (`rationalMinimalClosedChamber`) and the regions of the threshold and of
  `D_{M'}(δ)` (`rationalConstantTermThresholdRegion`, `rationalPositivePartRegion`);

and states, as Prop-valued targets, the existence of the constant terms, the uniform constant-term
threshold (I.4.3 and I.5), the weak-term limit (Lemma III.5.1) and Lemma VI.2.3.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section WeakPositiveSplit

variable {M : Type*} [Group M] {A : Type*} [CommGroup A] (j : A →* M)

/-- Right translation `φ ↦ (m ↦ φ(m j(a)))` by the image of `a ∈ A`, on all functions on `M`. -/
def componentRightTranslation : A →* Module.End ℂ (M → ℂ) :=
  (HarmonicAnalysis.GroupAction.rightFunctions (G := M)).comp j

@[simp] theorem componentRightTranslation_apply (a : A) (φ : M → ℂ) (m : M) :
    componentRightTranslation j a φ m = φ (m * j a) := by
  change HarmonicAnalysis.GroupAction.rightFunctions (j a) φ m = _
  simp

variable (A) in
/-- The unitary exponents `χ : A → ℂ`, `|χ(a)| = 1` for every `a` (Waldspurger's `Re(χ) = 0`). -/
def unitaryExponents : Set (A → ℂ) := {χ | ∀ a, ‖χ a‖ = 1}

/-- The span of the simultaneous generalized eigenspaces of the right translations by `j(A)`
whose exponents are unitary. -/
def weakExponentSpace : Submodule ℂ (M → ℂ) :=
  ⨆ χ ∈ unitaryExponents A, jointGenEigenspace (componentRightTranslation j) χ

/-- The span of the simultaneous generalized eigenspaces of the right translations by `j(A)`
whose exponents are not unitary. -/
def positiveExponentSpace : Submodule ℂ (M → ℂ) :=
  ⨆ χ ∈ (unitaryExponents A)ᶜ, jointGenEigenspace (componentRightTranslation j) χ

/-- The weak and positive exponent spaces are independent. -/
theorem disjoint_weakExponentSpace_positiveExponentSpace :
    Disjoint (weakExponentSpace j) (positiveExponentSpace j) :=
  (iSupIndep_jointGenEigenspace _).disjoint_biSup_biSup disjoint_compl_right

open Classical in
/-- **The weak part of `φ` along `j(A)`**: the unique `w` in the span of the unitary
generalized eigencomponents with `φ - w` in the span of the non-unitary ones, when `φ` lies in
the sum of the two spaces (for instance when `φ` is right finite for `j(A)`), and `0` otherwise. -/
def weakPart (φ : M → ℂ) : M → ℂ :=
  if h : ∃ w ∈ weakExponentSpace j, φ - w ∈ positiveExponentSpace j then h.choose else 0

/-- **The positive part of `φ` along `j(A)`**: `φ` minus its weak part. -/
def positivePart (φ : M → ℂ) : M → ℂ := φ - weakPart j φ

theorem weakPart_add_positivePart (φ : M → ℂ) : weakPart j φ + positivePart j φ = φ := by
  simp [positivePart]

/-- Uniqueness: a decomposition `φ = w + (φ - w)` along the two exponent spaces determines the
weak part. -/
theorem weakPart_eq_of_mem {φ w : M → ℂ} (hw : w ∈ weakExponentSpace j)
    (hφw : φ - w ∈ positiveExponentSpace j) : weakPart j φ = w := by
  unfold weakPart
  split_ifs with h
  swap
  · exact absurd ⟨w, hw, hφw⟩ h
  obtain ⟨hw', hφw'⟩ := h.choose_spec
  have h1 : h.choose - w ∈ weakExponentSpace j := Submodule.sub_mem _ hw' hw
  have h2 : h.choose - w ∈ positiveExponentSpace j := by
    have h3 := Submodule.sub_mem _ hφw hφw'
    have e : φ - w - (φ - h.choose) = h.choose - w := by abel
    rwa [e] at h3
  exact sub_eq_zero.mp
    (Submodule.disjoint_def.mp (disjoint_weakExponentSpace_positiveExponentSpace j) _ h1 h2)

/-- On the sum of the two exponent spaces, the weak and positive parts are its components. -/
theorem weakPart_mem_and_positivePart_mem {φ : M → ℂ}
    (hφ : φ ∈ weakExponentSpace j ⊔ positiveExponentSpace j) :
    weakPart j φ ∈ weakExponentSpace j ∧ positivePart j φ ∈ positiveExponentSpace j := by
  obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.mp hφ
  have e : weakPart j (w + p) = w := weakPart_eq_of_mem j hw (by simpa using hp)
  refine ⟨by rw [e]; exact hw, ?_⟩
  rw [positivePart, e]
  simpa using hp

open Classical in
theorem sum_filter_mem_weakExponentSpace (s : Finset (A → ℂ)) (c : (A → ℂ) → M → ℂ)
    (hc : ∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) :
    ∑ χ ∈ s with χ ∈ unitaryExponents A, c χ ∈ weakExponentSpace j := by
  refine Submodule.sum_mem _ fun χ hχ => ?_
  obtain ⟨hχs, hχU⟩ := Finset.mem_filter.mp hχ
  exact (le_iSup₂ (f := fun χ (_ : χ ∈ unitaryExponents A) =>
    jointGenEigenspace (componentRightTranslation j) χ) χ hχU) (hc χ hχs)

open Classical in
theorem sum_filter_not_mem_positiveExponentSpace (s : Finset (A → ℂ)) (c : (A → ℂ) → M → ℂ)
    (hc : ∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) :
    ∑ χ ∈ s with χ ∉ unitaryExponents A, c χ ∈ positiveExponentSpace j := by
  refine Submodule.sum_mem _ fun χ hχ => ?_
  obtain ⟨hχs, hχU⟩ := Finset.mem_filter.mp hχ
  exact (le_iSup₂ (f := fun χ (_ : χ ∈ (unitaryExponents A)ᶜ) =>
    jointGenEigenspace (componentRightTranslation j) χ) χ hχU) (hc χ hχs)

open Classical in
/-- **The weak part is the sum of the components with unitary exponents**: for a finite
expansion `φ = Σ_χ φ_χ` into simultaneous generalized eigenfunctions of the right translations by
`j(A)`, the weak part of `φ` is `Σ_{|χ| = 1} φ_χ`. -/
theorem weakPart_sum (s : Finset (A → ℂ)) (c : (A → ℂ) → M → ℂ)
    (hc : ∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) :
    weakPart j (∑ χ ∈ s, c χ) = ∑ χ ∈ s with χ ∈ unitaryExponents A, c χ := by
  refine weakPart_eq_of_mem j (sum_filter_mem_weakExponentSpace j s c hc) ?_
  rw [← Finset.sum_filter_add_sum_filter_not s (· ∈ unitaryExponents A), add_sub_cancel_left]
  exact sum_filter_not_mem_positiveExponentSpace j s c hc

open Classical in
/-- The positive part of a finite expansion is the sum of its components with non-unitary
exponents. -/
theorem positivePart_sum (s : Finset (A → ℂ)) (c : (A → ℂ) → M → ℂ)
    (hc : ∀ χ ∈ s, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ) :
    positivePart j (∑ χ ∈ s, c χ) = ∑ χ ∈ s with χ ∉ unitaryExponents A, c χ := by
  rw [positivePart, weakPart_sum j s c hc,
    ← Finset.sum_filter_add_sum_filter_not s (· ∈ unitaryExponents A), add_sub_cancel_left]

/-- The coefficient `m ↦ lam (J(m) y)` of a joint generalized eigenvector `y` of `J ∘ j` with
exponent `χ` is a joint generalized eigenfunction of the right translations by `j(A)` with the
same exponent (the published `aeval_rightFunctions_coefficient`). -/
theorem coefficient_mem_jointGenEigenspace {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ M Y) (lam : Y →ₗ[ℂ] ℂ) {χ : A → ℂ} {y : Y}
    (hy : y ∈ jointGenEigenspace (J.comp j) χ) :
    (fun m => lam (J m y)) ∈ jointGenEigenspace (componentRightTranslation j) χ := by
  rw [mem_jointGenEigenspace] at hy ⊢
  intro a
  obtain ⟨k, hk⟩ := hy a
  refine ⟨k, ?_⟩
  have h := aeval_rightFunctions_coefficient J lam (j a)
    ((Polynomial.X - Polynomial.C (χ a)) ^ k) y
  simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  change ((HarmonicAnalysis.GroupAction.rightFunctions (j a) - χ a • 1) ^ k) _ = 0
  rw [h]
  have hk' : ((J (j a) - χ a • 1) ^ k) y = 0 := hk
  funext m
  simp [hk']

open Classical in
/-- **Relation with `exists_weak_positive_decomposition`.** For a coefficient
`m ↦ lam (J(m) y)` and a finite decomposition `y = Σ_χ y_χ` into joint generalized eigenvectors
of `J ∘ j` (as given by `exists_sum_mem_jointGenEigenspace`), the weak part is the coefficient
of the sum of the components with unitary exponents: the function `F^w` constructed in the proof
of `exists_weak_positive_decomposition`. -/
theorem weakPart_coefficient {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ M Y) (lam : Y →ₗ[ℂ] ℂ) (s : Finset (A → ℂ)) (c : (A → ℂ) → Y)
    (hc : ∀ χ ∈ s, c χ ∈ jointGenEigenspace (J.comp j) χ) :
    weakPart j (fun m => lam (J m (∑ χ ∈ s, c χ))) =
      fun m => lam (J m (∑ χ ∈ s with χ ∈ unitaryExponents A, c χ)) := by
  have e : (fun m => lam (J m (∑ χ ∈ s, c χ))) = ∑ χ ∈ s, fun m => lam (J m (c χ)) := by
    funext m
    simp [map_sum]
  rw [e, weakPart_sum j s _ fun χ hχ => coefficient_mem_jointGenEigenspace j J lam (hc χ hχ)]
  funext m
  simp [map_sum]

/-- A function that is right finite for `j(A)` (Waldspurger's `A`-finiteness, `IsRightFinite`)
has a finite expansion into simultaneous generalized eigenfunctions, hence lies in the sum of the
weak and positive exponent spaces. -/
theorem mem_sup_of_isRightFinite {φ : M → ℂ} (hφ : IsRightFinite j.range φ) :
    φ ∈ weakExponentSpace j ⊔ positiveExponentSpace j := by
  classical
  obtain ⟨V, hV, hφV, hVst⟩ := hφ
  have := hV
  have hW : ∀ a, ∀ x ∈ V, componentRightTranslation j a x ∈ V := by
    intro a x hx
    have h := hVst (j a) ⟨a, rfl⟩ x hx
    convert h using 1
    funext m
    simp
  obtain ⟨c, hc, hsum⟩ :=
    exists_sum_mem_jointGenEigenspace (componentRightTranslation j) V hW hφV
  have hc' : ∀ χ ∈ c.support, c χ ∈ jointGenEigenspace (componentRightTranslation j) χ :=
    fun χ _ => (Submodule.mem_inf.mp (hc χ)).2
  rw [← hsum, Finsupp.sum,
    ← Finset.sum_filter_add_sum_filter_not c.support (· ∈ unitaryExponents A)]
  exact Submodule.add_mem_sup (sum_filter_mem_weakExponentSpace j _ _ hc')
    (sum_filter_not_mem_positiveExponentSpace j _ _ hc')

end WeakPositiveSplit

section MinimalLevi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- The actual minimal Levi `M_0(F) = M_∅(F)` is the group `Z_G(S)(F)` of points centralizing
the maximal split torus. -/
theorem standardLeviPoints_empty_eq_centralizerPoints :
    standardLeviPoints i ν ∅ = centralizerPoints i := by
  change (standardLevi i ν ∅).carrier _ = _
  rw [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    torusCentralizer_carrier_base]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- `M_0(F) ⊆ M_J(F)` for every standard Levi `M_J`. -/
theorem standardLeviPoints_empty_le (J : Set (characterLattice S)) :
    standardLeviPoints i ν ∅ ≤ standardLeviPoints i ν J := by
  rw [standardLeviPoints_empty_eq_centralizerPoints hG hi hν]
  exact centralizerPoints_le_standardLeviPoints i ν J

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion `M_0(F) → M_J(F)`, `m ↦ m`. -/
def minimalLeviInclusion (J : Set (characterLattice S)) :
    standardLeviPoints i ν ∅ →* standardLeviPoints i ν J :=
  Subgroup.inclusion (standardLeviPoints_empty_le hG hi hν J)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem coe_minimalLeviInclusion (J : Set (characterLattice S))
    (m : standardLeviPoints i ν ∅) :
    ((minimalLeviInclusion hG hi hν J m : standardLeviPoints i ν J) : rationalPoints G) =
      (m : rationalPoints G) :=
  Subgroup.coe_inclusion _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- Restriction of rational characters from the actual minimal Levi scheme `M_∅` to `S`,
followed by evaluation on `V(S) = ℝ ⊗ X_*(S)`, is bijective: the published comparison
`restrictionEvaluation_bijective_of_torusCentralizer`, since `M_∅` represents `Z_G(S)`. -/
theorem minimalLevi_restrictionEvaluation_bijective :
    Function.Bijective
      (BruhatTits.Cartan.restrictionEvaluation (Standard.leviTorusHom i ν ∅)) := by
  have hrep : (torusCentralizer i).IsRepresentedBy (Standard.leviHom i ν ∅) := by
    rw [← standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν]
    exact Standard.isRepresentedBy_leviHom i ν ∅
  exact BruhatTits.Cartan.restrictionEvaluation_bijective_of_torusCentralizer hG hi
    (Standard.isClosedSubgroup_leviHom i ν ∅) hrep (Standard.leviTorusHom_comp i ν ∅)

/-- **Waldspurger's `H_0` on the actual minimal Levi `M_0(F)`** (I.1, printed pp. 239–240):
the published character-normalized `centralizerValuation` of the minimal Levi scheme `M_∅`
(which represents `Z_G(S)`), read on `M_0(F) = M_∅(F)` and valued in `V(S) = ℝ ⊗ X_*(S)`. It is
characterized by `q^{-⟨χ|_S, H_0(m)⟩} = |χ(m)|_F` for every rational character `χ` of `M_∅`
(`rationalMinimalH0_spec`). -/
def rationalMinimalH0 (m : standardLeviPoints i ν ∅) : RealTorusSpace.V S :=
  (BruhatTits.Cartan.centralizerValuation (Standard.leviTorusHom i ν ∅)
    (minimalLevi_restrictionEvaluation_bijective hG hi hν)
    ((Standard.leviPointsEquiv i ν ∅).symm m)).toAdd

/-- `H_0` is additive. -/
theorem rationalMinimalH0_mul (m m' : standardLeviPoints i ν ∅) :
    rationalMinimalH0 hG hi hν (m * m') =
      rationalMinimalH0 hG hi hν m + rationalMinimalH0 hG hi hν m' := by
  simp only [rationalMinimalH0, map_mul, toAdd_mul]

/-- **The I.1 convention** `q^{-⟨χ, H_0(m)⟩} = |χ(m)|_F`, for every rational character `χ` of the
minimal Levi scheme, `⟨χ, ·⟩` being evaluation of its restriction to `S`. -/
theorem rationalMinimalH0_spec (m : standardLeviPoints i ν ∅)
    (χ : rationalCharacters (Standard.leviScheme i ν ∅)) :
    (LocalField.residueCardinality F : ℝ) ^
        (-RealTorusSpace.eval S
          (BruhatTits.Cartan.characterRestriction (Standard.leviTorusHom i ν ∅) χ)
          (rationalMinimalH0 hG hi hν m)) =
      LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval χ ((Standard.leviPointsEquiv i ν ∅).symm m) : F) := by
  rw [rationalMinimalH0, BruhatTits.Cartan.centralizerValuation_spec,
    ← rationalNormLogarithm_eq_intValuation, rationalNormLogarithm_spec]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem realTorusEval_add (a b : characterLattice S) (v : RealTorusSpace.V S) :
    RealTorusSpace.eval S (a + b) v = RealTorusSpace.eval S a v + RealTorusSpace.eval S b v := by
  simp only [RealTorusSpace.eval_eq_pair, TensorProduct.tmul_add, map_add, LinearMap.add_apply]

/-- **The closed chamber `M̄_0^+`** (I.1, printed p. 240): the points `m` of the actual
`M_0(F)` with `⟨α, H_0(m)⟩ ≥ 0` for every simple relative root `α ∈ Δ_0`. -/
def rationalMinimalClosedChamber : Set (standardLeviPoints i ν ∅) :=
  {m | ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν m)}

/-- Agreement with the published `dominantCentralizer` (inequalities for all positive relative
roots) of the minimal Levi scheme. -/
theorem mem_rationalMinimalClosedChamber_iff_dominantCentralizer (m : standardLeviPoints i ν ∅) :
    m ∈ rationalMinimalClosedChamber hG hi hν ↔
      (Standard.leviPointsEquiv i ν ∅).symm m ∈
        BruhatTits.Cartan.dominantCentralizer i ν (Standard.leviTorusHom i ν ∅)
          (minimalLevi_restrictionEvaluation_bijective hG hi hν) := by
  constructor
  · intro hm α hα
    exact positiveRelativeRoots_induction i ν
      (P := fun α => 0 ≤ RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν m)) hm
      (fun a _ b _ ha hb => by rw [realTorusEval_add]; exact add_nonneg ha hb) hα
  · intro hm α hα
    exact hm α (simpleRelativeRoots_subset_positive i ν hα)

/-- **The threshold region** `{m ∈ M̄_0^+ ; ⟨α, H_0(m)⟩ ≥ t for all α ∈ Δ_0 − J}` of the actual
`M_0(F)`, for a set `J` of simple roots (`J = Δ_0^{M'}`). -/
def rationalConstantTermThresholdRegion (J : Set (characterLattice S)) (t : ℝ) :
    Set (standardLeviPoints i ν ∅) :=
  {m | m ∈ rationalMinimalClosedChamber hG hi hν ∧
    ∀ α ∈ simpleRelativeRoots i ν \ J, t ≤ RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν m)}

/-- **Waldspurger's `D_{M'}(δ)`** (printed p. 299) on the actual `M_0(F)`, for a set `J` of simple
roots (`J = Δ_0^{M'}`) and a norm `N` on `V(S)` (the source's `|·|`):
`{m ∈ M̄_0^+ ; ⟨α, H_0(m)⟩ ≥ δ N(H_0(m)) for all α ∈ Δ_0 − J}`. -/
def rationalPositivePartRegion (N : Seminorm ℝ (RealTorusSpace.V S)) (J : Set (characterLattice S))
    (δ : ℝ) : Set (standardLeviPoints i ν ∅) :=
  {m | m ∈ rationalMinimalClosedChamber hG hi hν ∧
    ∀ α ∈ simpleRelativeRoots i ν \ J,
      δ * N (rationalMinimalH0 hG hi hν m) ≤ RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν m)}

/-- Change of norm in `D_{M'}(δ)`: if `N₁ ≤ c N₂` with `c > 0`, then
`D^{N₂}_{M'}(δ) ⊆ D^{N₁}_{M'}(δ / c)`. -/
theorem rationalPositivePartRegion_subset_of_le {N₁ N₂ : Seminorm ℝ (RealTorusSpace.V S)}
    {c : ℝ} (hc : 0 < c) (hN : ∀ v, N₁ v ≤ c * N₂ v) (J : Set (characterLattice S)) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    rationalPositivePartRegion hG hi hν N₂ J δ ⊆ rationalPositivePartRegion hG hi hν N₁ J (δ / c) := by
  rintro m ⟨hm, hα⟩
  refine ⟨hm, fun α hαJ => le_trans ?_ (hα α hαJ)⟩
  have h := mul_le_mul_of_nonneg_left (hN (rationalMinimalH0 hG hi hν m)) (div_nonneg hδ hc.le)
  calc δ / c * N₁ (rationalMinimalH0 hG hi hν m)
      ≤ δ / c * (c * N₂ (rationalMinimalH0 hG hi hν m)) := h
    _ = δ * N₂ (rationalMinimalH0 hG hi hν m) := by field_simp

/-- **Lemma VI.2.3-type decay with respect to a norm `N`** for a family `Φ` of functions on
`M_0(F)` and a weight `B`: for every `δ > 0` there are `ε > 0` and `C > 0` with
`|Φ_ω(m)| ≤ C B(m) e^{−ε N(H_0(m))}` for every `ω` and every `m ∈ D^N_{M'}(δ)`. -/
def HasRationalPositivePartDecay {κ : Type*} (N : Seminorm ℝ (RealTorusSpace.V S))
    (J : Set (characterLattice S)) (Φ : κ → standardLeviPoints i ν ∅ → ℂ)
    (B : standardLeviPoints i ν ∅ → ℝ) : Prop :=
  ∀ δ > 0, ∃ ε > 0, ∃ C > 0, ∀ ω, ∀ m ∈ rationalPositivePartRegion hG hi hν N J δ,
    ‖Φ ω m‖ ≤ C * B m * Real.exp (-(ε * N (rationalMinimalH0 hG hi hν m)))

/-- **The decay property does not depend on the norm** within an equivalence class: if
`N₁ ≤ c₁ N₂` and `N₂ ≤ c₂ N₁` (`c₁, c₂ > 0`) and `B ≥ 0`, decay for `N₁` gives decay for `N₂`.
All norms on the finite-dimensional `V(S)` are equivalent, so the targets below, which quantify
over every norm, are equivalent to their versions for one fixed norm. -/
theorem HasRationalPositivePartDecay.of_equivalent {κ : Type*}
    {N₁ N₂ : Seminorm ℝ (RealTorusSpace.V S)} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h₁ : ∀ v, N₁ v ≤ c₁ * N₂ v) (h₂ : ∀ v, N₂ v ≤ c₂ * N₁ v) {J : Set (characterLattice S)}
    {Φ : κ → standardLeviPoints i ν ∅ → ℂ} {B : standardLeviPoints i ν ∅ → ℝ}
    (hB : ∀ m, 0 ≤ B m) (h : HasRationalPositivePartDecay hG hi hν N₁ J Φ B) :
    HasRationalPositivePartDecay hG hi hν N₂ J Φ B := by
  intro δ hδ
  obtain ⟨ε, hε, C, hC, hbound⟩ := h (δ / c₁) (div_pos hδ hc₁)
  refine ⟨ε / c₂, div_pos hε hc₂, C, hC, fun ω m hm => ?_⟩
  refine (hbound ω m (rationalPositivePartRegion_subset_of_le hG hi hν hc₁ h₁ J hδ.le hm)).trans ?_
  have hCB : 0 ≤ C * B m := mul_nonneg hC.le (hB m)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCB
  have h2 := h₂ (rationalMinimalH0 hG hi hν m)
  have : ε / c₂ * N₂ (rationalMinimalH0 hG hi hν m) ≤ ε * N₁ (rationalMinimalH0 hG hi hν m) := by
    calc ε / c₂ * N₂ (rationalMinimalH0 hG hi hν m)
        ≤ ε / c₂ * (c₂ * N₁ (rationalMinimalH0 hG hi hν m)) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hε.le hc₂.le)
      _ = ε * N₁ (rationalMinimalH0 hG hi hν m) := by field_simp
  linarith

end MinimalLevi

section OrbitConstantTerms

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

-- The unitary unramified orbit `O` of `π`.
set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

-- The orbit coefficients `(ψ, ω) ↦ f_ω = E^G_P ψ_ω`.
set_option hygiene false in
local notation "𝐟" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq

-- `M' = M_{I'}(F)`.
set_option hygiene false in
local notation "𝐌'" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')

/-- **The constant term `(f_ω)_{P'}`** of the actual orbit coefficient `f_ω = E^G_P ψ_ω` along
the actual standard parabolic `P' = P_{I'}(F)`: the published `standardConstantTerm`
(Proposition I.6.2, normalized by `δ_{U'}`) for the compatible split component `A` of `M'`. -/
def rationalOrbitConstantTerm (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (ω : 𝒪) : 𝐌' → ℂ :=
  standardConstantTerm hA (fun g => 𝐟 ψ ω g)

/-- **The weak constant term `(f_ω)^w_{P'}`**: the sum of the generalized eigencomponents of
`(f_ω)_{P'}` under right translation by `A(F)` whose exponents are unitary (`weakPart`). -/
def rationalOrbitWeakConstantTerm (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (ω : 𝒪) : 𝐌' → ℂ :=
  weakPart (standardComponentHom hA) (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I'
    hA ψ ω)

/-- **The positive constant term `(f_ω)^+_{P'} = (f_ω)_{P'} − (f_ω)^w_{P'}`** (printed p. 299). -/
def rationalOrbitPositiveConstantTerm
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (ω : 𝒪) : 𝐌' → ℂ :=
  positivePart (standardComponentHom hA)
    (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω)

theorem rationalOrbitWeakConstantTerm_add_positive
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (ω : 𝒪) :
    rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω +
        rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω =
      rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω :=
  weakPart_add_positivePart _ _

/-- When `f_ω` has a constant term along `P'`, its weak and positive parts are its components in
the spans of the unitary, resp. non-unitary, generalized eigenspaces of `A(F)`. -/
theorem rationalOrbitWeakConstantTerm_mem
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (ω : 𝒪)
    (h : HasStandardConstantTerm hA (fun g => 𝐟 ψ ω g)) :
    rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω ∈
        weakExponentSpace (standardComponentHom hA) ∧
      rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω ∈
        positiveExponentSpace (standardComponentHom hA) :=
  weakPart_mem_and_positivePart_mem _
    (mem_sup_of_isRightFinite _ (HasStandardConstantTerm.isRightFinite hA h))

/-- **`δ_{P'}` versus `δ_{U'}` on `M'(F)`**: for `m ∈ M'(F)`, Mathlib's modular character of the
actual standard parabolic group `P'(F)` at `m` is `δ_{U'}(m)`, the modulus used by
`standardConstantTerm` (from the published `modularCharacter_standardParabolicPoints`). -/
theorem modularCharacter_standardParabolicPoints_leviPoint (m : 𝐌') :
    haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I'
    Measure.modularCharacter
        (⟨(m : rationalPoints G), standardLevi_le_standardParabolic i ν _ _ m.2⟩ :
          standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I')) =
      (standardRadicalModulus i ν (RationalPointFamily.rootSet i ν I') m : ℝ≥0) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I'
  rw [modularCharacter_standardParabolicPoints hG hi hν I' rfl
    (RationalPointFamily.rootSet_subset i ν I')]
  rfl

/-- `H_0` on `A(F)`: the value of `H_0` at the image of `x ∈ A(F)` in `M_0(F)`. -/
def rationalComponentH0 (x : rationalPoints A.toGrp) : RealTorusSpace.V S :=
  rationalMinimalH0 hG hi hν ⟨rationalPoints.map (qA ≫ i) x, map_mem_standardLeviPoints_empty qA x⟩

open Classical in
/-- The simple roots outside `J` (`Δ_0 − Δ_0^{M'}`), as linear forms on `V(S)`. -/
def rationalOutsideSimpleForms (J : Set (characterLattice S)) :
    Finset (Module.Dual ℝ (RealTorusSpace.V S)) :=
  ((hi.1.1.finite_simpleRelativeRoots i ν).subset
    (Set.sdiff_subset : simpleRelativeRoots i ν \ J ⊆ simpleRelativeRoots i ν)).toFinset.image
    (RealTorusSpace.eval S)

/-- **Existence of the constant terms** (Proposition I.6.2 for the coefficients of the induced
representations): under Renard's V.5.2 data for `P'` (a standard cocharacter `ζ` of `I'`, a
compact-open normal basis `B` of `K0`, and the basis-member clauses of `P'` for the split
component `A`), every orbit coefficient `f_ω` has a constant term along `P'`. -/
def RationalOrbitConstantTermExistenceStatement : Prop :=
  ∀ {ζ : cocharacterLattice S},
    IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ →
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    CompactOpenNormalBasis K0 B →
    (∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K') →
  ∀ (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (ω : 𝒪),
    HasStandardConstantTerm hA (fun g => 𝐟 ψ ω g)

/-- **The uniform constant-term threshold** (Proposition I.4.3 and I.5, as used on printed
pp. 299 and 303): under Renard's structural data, for every section `ψ ∈ C^∞(O, P)` there is
`t > 0` such that for every `ω ∈ O` and every `m ∈ M̄_0^+` with `⟨α, H_0(m)⟩ ≥ t` for all
`α ∈ Δ_0 − Δ_0^{M'}`, `f_ω(m) = δ_{U'}(m)^{1/2} (f_ω)_{P'}(m)`. -/
def RationalOrbitConstantTermThresholdStatement : Prop :=
  ∀ {ζ : cocharacterLattice S},
    IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ →
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    IsOpen (K0 : Set (rationalPoints G)) → IsCompact (K0 : Set (rationalPoints G)) →
    CompactOpenNormalBasis K0 B →
    (∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K') →
    SimultaneousStandardBasisAt i ν K0 →
    RationalPointFamily.FiniteCartanCovering F i ν K0 →
    (∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J K0) →
  ∀ ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π, ∃ t > 0, ∀ ω : 𝒪,
    ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν (RationalPointFamily.rootSet i ν I') t,
      𝐟 ψ ω (m : rationalPoints G) =
        standardHalfModulus i ν (RationalPointFamily.rootSet i ν I')
            (minimalLeviInclusion hG hi hν _ m) *
          rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω
            (minimalLeviInclusion hG hi hν _ m)

/-- **The weak constant term as a limit** (Lemma III.5.1, printed pp. 269–270): under Renard's
structural data, for every `ψ`, every `ω ∈ O` and every `m' ∈ M'(F)`,
`δ_{U'}(m' a)^{-1/2} f_ω(m' a) − (f_ω)^w_{P'}(m' a)` tends to `0` as `a →_{P'} ∞` in `A(F)`, in
the sense of III.5 (`TendstoZeroAlongParabolic`), for `H_{M'}(a) = H_0(a)` and the simple roots
`Δ_0 − Δ_0^{M'}`. The quotient measurable structure must be Borel for its quotient topology. -/
def RationalOrbitWeakConstantTermLimitStatement : Prop :=
  ∀ [BorelSpace (𝐌 ⧸ C)],
  ∀ {ζ : cocharacterLattice S},
    IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ →
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    IsOpen (K0 : Set (rationalPoints G)) → IsCompact (K0 : Set (rationalPoints G)) →
    CompactOpenNormalBasis K0 B →
    (∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K') →
    SimultaneousStandardBasisAt i ν K0 →
    RationalPointFamily.FiniteCartanCovering F i ν K0 →
    (∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J K0) →
  ∀ (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (ω : 𝒪) (m' : 𝐌'),
    TendstoZeroAlongParabolic (rationalComponentH0 hG hi hν (qA := qA))
      (rationalOutsideSimpleForms hi (ν := ν) (RationalPointFamily.rootSet i ν I'))
      (fun x => (standardHalfModulus i ν (RationalPointFamily.rootSet i ν I')
            (m' * standardComponentHom hA x))⁻¹ *
          𝐟 ψ ω ((m' * standardComponentHom hA x : 𝐌') : rationalPoints G) -
        rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω
          (m' * standardComponentHom hA x))

/-- **Waldspurger's Lemma VI.2.3 on actual rational points** (printed p. 299; principal target):
under Renard's structural data, for every norm `N` on `V(S)`, every `ψ ∈ C^∞(O, P)` and every
`δ > 0` there are `ε > 0` and `C > 0` such that for every `ω ∈ O` and every `m ∈ D_{M'}(δ)`,
`|(f_ω)^+_{P'}(m)| ≤ C Ξ^{M'}(m) e^{−ε N(H_0(m))}`. The quotient measurable structure
must be Borel for its quotient topology. -/
def RationalOrbitPositiveConstantTermDecayStatement
    (hM' : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))) : Prop :=
  ∀ [BorelSpace (𝐌 ⧸ C)],
  ∀ {ζ : cocharacterLattice S},
    IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ →
  ∀ {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))},
    IsOpen (K0 : Set (rationalPoints G)) → IsCompact (K0 : Set (rationalPoints G)) →
    CompactOpenNormalBasis K0 B →
    (∀ K' ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν I') qA K') →
    SimultaneousStandardBasisAt i ν K0 →
    RationalPointFamily.FiniteCartanCovering F i ν K0 →
    (∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J K0) →
  ∀ (N : Seminorm ℝ (RealTorusSpace.V S)), (∀ v, N v = 0 → v = 0) →
  ∀ ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    HasRationalPositivePartDecay hG hi hν N (RationalPointFamily.rootSet i ν I')
      (fun (ω : 𝒪) m => rationalOrbitPositiveConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω
        (minimalLeviInclusion hG hi hν _ m))
      (fun m => rationalLeviXi hKc hM' (minimalLeviInclusion hG hi hν _ m))

end OrbitConstantTerms

end Langlands.HarishChandraSchwartz
