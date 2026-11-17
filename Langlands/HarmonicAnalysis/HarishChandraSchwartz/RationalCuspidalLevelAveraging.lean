import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzCompactLifting
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalLowerInclusionStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay

/-! # Same-level cuspidal preimages: the VIII.5 inclusion from VIII.4.2

Waldspurger VIII.5 (printed p.332) deduces from Theorem VIII.4.2 and the
`G × G`-invariance of `p_χ` that the `H × H`-invariant coefficients of the classes in
`E₂(G)^H_χ` lie in `p_χ(°C_H)`. This module specializes the generic compact averaging
theorem `exists_biInvariant_central_preimage` to the actual cuspidal Schwartz space and
reduces `RationalCuspidalFixedCoefficientLiftingStatement` to central convergence and the
lower inclusion of VIII.4.2. Neither input is proved here.
-/

noncomputable section

universe u uV uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] {A : Subgroup Γ} [MeasurableSpace A]
  {Ξ σ : Γ → ℝ} {muA : Measure A} {χ : A →* ℂˣ}

/-- Convergence of the central integral passes to smaller subspaces. -/
theorem CentralIntegralConvergesOn.mono {E E' : Submodule ℂ (Space Ξ σ)}
    (h : CentralIntegralConvergesOn E muA χ) (hle : E' ≤ E) :
    CentralIntegralConvergesOn E' muA χ :=
  fun φ hφ g => h φ (hle hφ) g

end Generic

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Level

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The actual cuspidal kernel is stable under the actual two-sided translations. -/
theorem rationalCuspidalSubmodule_isTranslationStable :
    IsTranslationStable (rationalTranslationWeights K.isOpen hKc hPK ρ)
      (rationalCuspidalSubmodule hKc hPK ρ) := by
  intro g₁ g₂ f hf I hI muU hmuU
  exact (hf I hI muU hmuU).translate g₁ g₂

/-- **Same-level preimages.** If the central integral converges on the actual cuspidal
space, every `H`-bi-invariant element of the raw full image is the central integral of an
`H`-bi-invariant actual cuspidal Schwartz function. -/
theorem mem_rationalCuspidalCentralLevelImage_of_biInvariant
    {s : T.toGrp ⟶ G} (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) (χ : (rationalPoints.map s).range →* ℂˣ)
    (hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ)
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G)))
    {f : rationalPoints G → ℂ} (hf : f ∈ rationalCuspidalCentralImage hKc hPK ρ muA χ)
    (hHf : IsBiInvariant H.toSubgroup f) :
    f ∈ rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  obtain ⟨φ, hφ, hφH, hφf⟩ := exists_biInvariant_central_preimage
    (rationalTranslationWeights K.isOpen hKc hPK ρ) (rationalCuspidalSubmodule hKc hPK ρ)
    (rationalCuspidalSubmodule_isTranslationStable hKc hPK ρ)
    hs.isCentralSplitTorus.isCentral.range_le_center muA χ hc H hH hf hHf
  exact ⟨φ, ⟨hφ, hφH⟩, hφf⟩

/-- Every element of the raw level image is bi-invariant under that level. -/
theorem isBiInvariant_of_mem_rationalCuspidalCentralLevelImage
    {s : T.toGrp ⟶ G} (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) (χ : (rationalPoints.map s).range →* ℂˣ)
    (H : Subgroup (rationalPoints G)) {f : rationalPoints G → ℂ}
    (hf : f ∈ rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H) :
    IsBiInvariant H f := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  exact hφ.2.centralProjection (μA := muA) hs.isCentralSplitTorus.isCentral.range_le_center χ

/-- Under convergence on the actual cuspidal space, the raw level image at a compact open
`H` is exactly the set of `H`-bi-invariant elements of the raw full image. -/
theorem rationalCuspidalCentralLevelImage_eq_inter_biInvariant
    {s : T.toGrp ⟶ G} (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) (χ : (rationalPoints.map s).range →* ℂˣ)
    (hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ)
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup =
      rationalCuspidalCentralImage hKc hPK ρ muA χ ∩ {f | IsBiInvariant H.toSubgroup f} := by
  ext f
  constructor
  · intro hf
    exact ⟨rationalCuspidalCentralLevelImage_subset hKc hPK ρ muA χ H.toSubgroup hf,
      isBiInvariant_of_mem_rationalCuspidalCentralLevelImage hKc hPK ρ hs muA χ
        H.toSubgroup hf⟩
  · rintro ⟨hf, hHf⟩
    exact mem_rationalCuspidalCentralLevelImage_of_biInvariant hKc hPK ρ hs muA χ hc H hH
      hf hHf

end Level

/-- **Reduction of the VIII.5 level inclusion.** Central convergence for all actual
Schwartz functions and the lower inclusion of Theorem VIII.4.2 at carrier universe `uV`
imply the published same-level lifting target at the same universes. -/
theorem RationalCuspidalDiscreteCoefficientLowerInclusionStatement.fixedCoefficientLifting
    (hconv : RationalSchwartzCentralConvergenceStatement.{u})
    (hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV}) :
    RationalCuspidalFixedCoefficientLiftingStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _ mu _ χ hχ hu
    H hH ω hω f hf hHf
  have hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ :=
    (hconv F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχ hu).mono le_top
  exact mem_rationalCuspidalCentralLevelImage_of_biInvariant hKc hPK ρ hs muA χ hc H hH
    (hlower.coefficient_mem hG hi hν hKc hPK ρ hρ s hs muA mu χ hχ hu H.toSubgroup ω hω f hf)
    hHf

/-- The conditional VIII.5 level inclusion recorded as a proposition: central convergence
for all actual Schwartz functions and the lower inclusion of Theorem VIII.4.2 at carrier
universe `uV` imply the published same-level lifting target. It is proved below. -/
def RationalCuspidalFixedCoefficientLiftingReductionStatement : Prop :=
  RationalSchwartzCentralConvergenceStatement.{u} →
    RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV} →
      RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}

theorem rationalCuspidalFixedCoefficientLiftingReduction :
    RationalCuspidalFixedCoefficientLiftingReductionStatement.{u, uV} :=
  fun hconv hlower => hlower.fixedCoefficientLifting hconv

end Langlands.HarishChandraSchwartz
