import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # The projections `p_χ` of Waldspurger VIII.4 on actual rational points

For the actual rational points `G(F)` of a group scheme over a nonarchimedean local field, a
split torus `i : S → G`, a cocharacter `ν` and a central `s : T → G` (for a connected reductive `G`
and a split component `s`, the image is `A_G(F)`), this module proves that `A_G(F)` lies in every
actual standard Levi and parabolic subgroup, that `δ₀` is trivial on it and that `Ξ(a g) = Ξ(g)`
for `a ∈ A_G(F)`. It states the two height properties of `A_G(F)` and `G¹` used in VIII.4
(`RationalSplitCenterHeightStatement`) and, from them, gives the Library's `CentralWeights` for
the actual weights, the projection `p_χ` on the actual `C(G)` and its rapid decay on `G¹`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {P K : Subgroup G} {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
include hδ in
/-- Left translation by `z ∈ P` with `δ(z) = 1` does not change the Iwasawa weight. -/
theorem iwasawaWeight_mul_left_of_eq_one {z : G} (hz : z ∈ P) (hz1 : δ ⟨z, hz⟩ = 1) (g : G) :
    iwasawaWeight hPK δ (z * g) = iwasawaWeight hPK δ g := by
  obtain ⟨k, hk, hg⟩ := exists_iwasawaFactor hPK g
  have hzq : z * (iwasawaFactor hPK g : G) ∈ P := P.mul_mem hz (iwasawaFactor hPK g).2
  have h1 : z * g = (z * (iwasawaFactor hPK g : G)) * k := by
    conv_lhs => rw [hg]
    rw [mul_assoc]
  rw [h1, iwasawaWeight_mul hδ hzq hk]
  have h2 : (⟨z * (iwasawaFactor hPK g : G), hzq⟩ : P) = ⟨z, hz⟩ * iwasawaFactor hPK g := rfl
  rw [h2, map_mul, hz1, one_mul]
  rfl

include hδ in
/-- `Ξ(z g) = Ξ(g)` for `z ∈ P` with `δ(z) = 1` commuting with `K`. -/
theorem xi_mul_left_of_eq_one [CompactSpace K] {z : G} (hz : z ∈ P) (hz1 : δ ⟨z, hz⟩ = 1)
    (hzK : ∀ k ∈ K, k * z = z * k) (g : G) : xi hPK δ (z * g) = xi hPK δ g := by
  unfold xi
  congr 1
  funext k
  rw [← mul_assoc, hzK k k.2, mul_assoc, iwasawaWeight_mul_left_of_eq_one hδ hz hz1]

end Abstract

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

section Center

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) {s : T.toGrp ⟶ G}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image of a central `s : T → G` lies in every actual standard Levi subgroup `M_J(F)`: a
central point lies in the centralizer of the torus. -/
theorem range_le_standardLeviPoints (hs : IsCentral s) (J : Set (characterLattice S)) :
    (rationalPoints.map s).range ≤ standardLeviPoints i ν J := by
  rintro _ ⟨y, rfl⟩
  exact SubgroupFunctor.le_def.mp (torusCentralizer_le_standardLevi i ν J) _
    (SubgroupFunctor.le_def.mp (center_le_torusCentralizer i) _ (hs _ y))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image of a central `s : T → G` lies in every actual standard parabolic `P_J(F)`. -/
theorem range_le_standardParabolicPoints (hs : IsCentral s) (J : Set (characterLattice S)) :
    (rationalPoints.map s).range ≤ standardParabolicPoints i ν J := fun _ hx =>
  SubgroupFunctor.le_def.mp (standardLevi_le_standardParabolic i ν J) _
    (range_le_standardLeviPoints i ν hs J hx)

end Center

variable [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalCentralSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalCentralT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalCentralNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

/-- `δ₀(z) = 1` for `z ∈ P₀(F)` central in `G(F)`. -/
theorem rationalMinimalModulus_eq_one_of_mem_center (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (p : standardParabolicPoints i ν ∅)
    (hp : (p : rationalPoints G) ∈ Subgroup.center (rationalPoints G)) :
    rationalMinimalModulus i ν p = 1 :=
  closedNormalizerCharacter_eq_one_of_commute _ (isClosed_standardUnipotentPoints i ν ∅) _
    fun u _ => (Subgroup.mem_center_iff.mp hp u).symm

section Weights

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hKo in
/-- **`Ξ(a g) = Ξ(g)` for `a ∈ A_G(F)`**: `A_G(F)` is central, lies in `P₀(F)` and `δ₀` is trivial
on it. -/
theorem rationalXi_mul_of_mem_range (hs : IsCentral s) {a : rationalPoints G}
    (ha : a ∈ (rationalPoints.map s).range) (g : rationalPoints G) :
    rationalXi hKc hPK (a * g) = rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have haP := range_le_standardParabolicPoints i ν hs ∅ ha
  have hac := hs.range_le_center ha
  exact xi_mul_left_of_eq_one (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) haP
    (rationalMinimalModulus_eq_one_of_mem_center i ν ⟨a, haP⟩ hac)
    (fun k _ => Subgroup.mem_center_iff.mp hac k) g

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `1 + σ(a) ≤ (1 + σ(a g)) (1 + σ(g))` for all `a, g ∈ G(F)`. -/
theorem one_add_rationalHeight_le_mul {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (a g : rationalPoints G) :
    1 + rationalHeight (F := F) ρ a ≤
      (1 + rationalHeight (F := F) ρ (a * g)) * (1 + rationalHeight (F := F) ρ g) := by
  have h := rationalHeight_mul_le (F := F) ρ (a * g) g⁻¹
  rw [mul_inv_cancel_right, rationalHeight_inv] at h
  have h1 := rationalHeight_nonneg (F := F) ρ (a * g)
  have h2 := rationalHeight_nonneg (F := F) ρ g
  nlinarith

include hKo in
/-- **The Library's `CentralWeights`** for `A = A_G(F)`, a measure `μ_A` on it and the actual
`Ξ`, `σ`, given the integrability `∫_{A_G(F)} (1 + σ(a))^{-r₀} dμ_A(a) < ∞` for some `r₀`. -/
theorem rationalCentralWeights (hs : IsCentral s) {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (ρ : MatrixRepresentation G n)
    (muA : Measure (rationalPoints.map s).range)
    (hint : ∃ r₀ : ℝ, ∫⁻ a, ENNReal.ofReal ((1 + rationalHeight (F := F) ρ a) ^ (-r₀)) ∂muA < ⊤) :
    CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ) where
  pos := rationalXi_pos hKo hKc hPK
  nonneg := rationalHeight_nonneg ρ
  xi_mul a g := rationalXi_mul_of_mem_range hKo hKc hPK hs a.2 g
  one_add_le a g := one_add_rationalHeight_le_mul ρ a g
  integrable := hint

end Weights

/-- **Heights on the split centre** (the two properties of `A_G(F)` and `G¹` behind Waldspurger
VIII.4, derived from I.1): for a connected reductive `G` over a nonarchimedean local field, a
split component `s : T → G` with image `A_G(F)` and a closed matrix representation `ρ` with
height `σ`, (1) there is `C` with `1 + σ(a) ≤ C (1 + σ(a g))` for all `a ∈ A_G(F)` and
`g ∈ G¹`, and (2) for every Haar measure `μ_A` on `A_G(F)` there is `r₀` with
`∫_{A_G(F)} (1 + σ(a))^{-r₀} dμ_A(a) < ∞`. -/
def RationalSplitCenterHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G), IsSplitComponent s →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
      (∃ C : ℝ, ∀ a ∈ (rationalPoints.map s).range, ∀ g ∈ Plancherel.rationalCommonNormKernel G,
          1 + rationalHeight (F := F) ρ a ≤ C * (1 + rationalHeight (F := F) ρ (a * g))) ∧
      ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
        ∃ r₀ : ℝ, ∫⁻ a, ENNReal.ofReal ((1 + rationalHeight (F := F) ρ a) ^ (-r₀)) ∂muA < ⊤

section Projection

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hKo in
/-- The statement applied to one group: the actual `CentralWeights` for every Haar measure on
`A_G(F)`. -/
theorem RationalSplitCenterHeightStatement.centralWeights
    (h : RationalSplitCenterHeightStatement.{u}) (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s) (hρ : IsClosedSubgroup ρ)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ) :=
  rationalCentralWeights hKo hKc hPK hs.isCentralSplitTorus.isCentral ρ muA
    ((h F G hG T s hs N ρ hρ).2 muA)

/-- The statement applied to one group: `1 + σ(g) + σ(a) ≤ C (1 + σ(a g))` for `g ∈ G¹` and
`a ∈ A_G(F)`, with `C > 0` (the hypothesis `hS` of the Library's
`CentralWeights.enorm_centralProjection_le_rpow_neg`). -/
theorem RationalSplitCenterHeightStatement.exists_one_add_add_le
    (h : RationalSplitCenterHeightStatement.{u}) (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s) (hρ : IsClosedSubgroup ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ Plancherel.rationalCommonNormKernel G,
      ∀ a : (rationalPoints.map s).range,
        1 + rationalHeight (F := F) ρ g + rationalHeight (F := F) ρ a ≤
          C * (1 + rationalHeight (F := F) ρ ((a : rationalPoints G) * g)) := by
  obtain ⟨C, hC⟩ := (h F G hG T s hs N ρ hρ).1
  refine ⟨2 * max C 1 + 1, by positivity, fun g hg a => ?_⟩
  have h1 := hC a a.2 g hg
  have h2 := rationalHeight_mul_le (F := F) ρ (a : rationalPoints G)⁻¹
    ((a : rationalPoints G) * g)
  rw [inv_mul_cancel_left, rationalHeight_inv] at h2
  have h3 := rationalHeight_nonneg (F := F) ρ ((a : rationalPoints G) * g)
  have h4 : C * (1 + rationalHeight (F := F) ρ ((a : rationalPoints G) * g)) ≤
      max C 1 * (1 + rationalHeight (F := F) ρ ((a : rationalPoints G) * g)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  nlinarith [le_max_right C 1]

/-- **Waldspurger's `p_χ`** (VIII.4, printed p. 327) on the actual `C(G)`:
`(p_χ f)(g) = ∫_{A_G(F)} χ(a)^{-1} f(a g) dμ_A(a)` for a unitary character `χ` of `A_G(F)`, as a
linear map from `C(G)` to functions on `G(F)`, given the actual `CentralWeights` (for instance
from `RationalSplitCenterHeightStatement.centralWeights`). -/
def rationalCentralProjection (muA : Measure (rationalPoints.map s).range)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    {χ : (rationalPoints.map s).range →* ℂˣ} (hχ : IsUnitaryCharacter χ) :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] (rationalPoints G → ℂ) :=
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨⟨K, hKo⟩, hKc⟩⟩
  Space.centralProjection hw hχ

theorem rationalCentralProjection_apply (muA : Measure (rationalPoints.map s).range)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    {χ : (rationalPoints.map s).range →* ℂˣ} (hχ : IsUnitaryCharacter χ)
    (f : RationalSchwartzSpace hKc hPK ρ) (g : rationalPoints G) :
    rationalCentralProjection hKo hKc hPK ρ muA hw hχ f g =
      ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * (f : rationalPoints G → ℂ) ((a : rationalPoints G) * g) ∂muA :=
  rfl

/-- **Rapid decay of `p_χ f` on `G¹`** (the estimate "on vérifie aisément" in the proof of
Waldspurger's Proposition VIII.4.1, printed p. 328, here for every `f ∈ C(G)`), given
`RationalSplitCenterHeightStatement`: for every `r` there is a finite `c` with
`|(p_χ f)(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for all `g ∈ G¹`. -/
theorem RationalSplitCenterHeightStatement.enorm_rationalCentralProjection_le
    (h : RationalSplitCenterHeightStatement.{u}) (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s) (hρ : IsClosedSubgroup ρ)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    {χ : (rationalPoints.map s).range →* ℂˣ} (hχ : IsUnitaryCharacter χ)
    (f : RationalSchwartzSpace hKc hPK ρ) (r : ℝ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ g ∈ Plancherel.rationalCommonNormKernel G,
      ‖rationalCentralProjection hKo hKc hPK ρ muA (h.centralWeights hKo hKc hPK ρ hG hs hρ muA)
          hχ f g‖ₑ ≤
        c * ENNReal.ofReal (rationalXi hKc hPK g * (1 + rationalHeight (F := F) ρ g) ^ (-r)) := by
  obtain ⟨C, hC, hS⟩ := h.exists_one_add_add_le ρ hG hs hρ
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨⟨K, hKo⟩, hKc⟩⟩
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff _ _).mp (Space.coe_mem f)
  exact (h.centralWeights hKo hKc hPK ρ hG hs hρ muA).enorm_centralProjection_le_rpow_neg hχ hC
    (S := (Plancherel.rationalCommonNormKernel G : Set (rationalPoints G))) (fun g hg a => hS g hg a)
    (fun r => hH.2 r) r

end Projection

end Langlands.HarishChandraSchwartz
