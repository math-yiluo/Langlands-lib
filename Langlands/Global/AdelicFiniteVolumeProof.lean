import Langlands.Global.AdelicOpenIwasawaCompact
import Langlands.Global.AdelicSiegelMeasureOpenSubgroup
import Langlands.Global.AdelicSiegelChamberReduction
import Langlands.Global.AdelicSplitChamberReduction
import Langlands.Global.AdelicSplitFundamentalSetFromCover
import Langlands.Global.AdelicRankOneOrbitHeightBoundProof
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.Global.AdelicSiegelSetupExistence
import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Global.AdelicFiniteVolumeReduction
import Langlands.Global.PositiveTorusUnipotentModulus
import Langlands.Global.SimpleRootBoxCompact
import Langlands.Global.UnipotentRationalQuotientCompactProof
import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinatesProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof

/-! # Finite volume of the norm-one adelic rational quotient

This file proves Getz–Hahn, Theorem 2.6.3, over number fields: for every smooth connected
affine group `G` over a number field `F`, the quotient `G(F) \ G(𝔸_F)¹` of the actual norm-one
Haar measure by principal counting has finite volume.

The connected reductive case uses a Siegel set with a compact subgroup `K` that is **not**
required to satisfy `P(𝔸_F) K = G(𝔸_F)`. Instead (`exists_compact_openSubgroup_finite_cover`)
there are an open subgroup `H₁ ⊇ K` with `H₁ ⊆ P(𝔸_F) K` and a finite set `W ⊆ G(𝔸_F)¹` with
`P(𝔸_F) K W = G(𝔸_F)`. The chamber reduction for the compact set `K W` puts a rational left
translate of every norm-one point in `S W`, where `S` is a weak Siegel product with compact
subgroup `K`; the set `S` has finite Haar measure in `G(𝔸_F)¹` by
`measure_weakSiegelProduct_lt_top_of_openSubgroup`, and finitely many right translates of a
set of finite Haar measure have finite Haar measure.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal Pointwise

namespace Langlands.Global

open Langlands.GroupScheme

namespace AdelicSiegelFactors

open AdelicGroupPoints

/-- In a second-countable locally compact group, the union of finitely many right translates
of a set of finite Haar measure has finite Haar measure. -/
theorem measure_mul_finite_lt_top {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν₀ : Measure H) [ν₀.IsHaarMeasure]
    {A W : Set H} (hA : ν₀ A < ∞) (hW : W.Finite) : ν₀ (A * W) < ∞ := by
  have hsub : A * W ⊆ ⋃ w ∈ W, (fun x => x * w⁻¹) ⁻¹' A := by
    rintro _ ⟨a, ha, w, hw, rfl⟩
    exact mem_biUnion hw (by simpa using ha)
  refine (measure_mono hsub).trans_lt (measure_biUnion_lt_top hW fun w _ => ?_)
  have : IsFiniteMeasureOnCompacts (ν₀.map (fun x => x * w⁻¹)) :=
    Measure.IsFiniteMeasureOnCompacts.map ν₀ (Homeomorph.mulRight w⁻¹)
  have hν₀' := Measure.isMulLeftInvariant_eq_smul (ν₀.map (fun x => x * w⁻¹)) ν₀
  have happ : ν₀ ((fun x => x * w⁻¹) ⁻¹' A) = ν₀.map (fun x => x * w⁻¹) A :=
    ((MeasurableEquiv.mulRight w⁻¹).map_apply A).symm
  rw [happ, hν₀', Measure.coe_nnreal_smul_apply]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hA

/-- **Siegel cover with finitely many translates.** For an actual algebraic Siegel setup, a
compact subgroup `K` and a finite set `W ⊆ G(𝔸_F)¹` with `P(𝔸_F) (K W) = G(𝔸_F)`, there are
compact factors with compact subgroup `K` and a threshold `t` such that every norm-one point
has a rational left translate in `S W`, where `S` is the weak Siegel product. -/
theorem exists_rational_mul_mem_weakSiegelProduct_mul
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (W : Set (AdelicGroupPoints F G)) (hW : W.Finite)
    (hW1 : W ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)))
    (hcov : Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
      ((K : Set (AdelicGroupPoints F G)) * W) = Set.univ) :
    ∃ (C : CompactFactors F G
        (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ),
      C.compactSubgroup = K ∧
        ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
          rational F G q * (g : AdelicGroupPoints F G) ∈
            weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t * W := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hΩc : IsCompact ((K : Set (AdelicGroupPoints F G)) * W) := hKc.mul hW.isCompact
  have hΩ1 : (K : Set (AdelicGroupPoints F G)) * W ⊆
      (normOneSubgroup F G : Set (AdelicGroupPoints F G)) := by
    rintro _ ⟨k, hk, w, hw, rfl⟩
    exact (normOneSubgroup F G).mul_mem (compactSubgroup_le_normOneSubgroup F G K hKc hk)
      (hW1 hw)
  obtain ⟨t, ht⟩ := hasWeakChamberCoverReduction_of_rootLeviHeightBounds F G T i ν T₀ j hG hS
    (RepresentationGrowth.hasRootLeviHeightBounds_of_rankOne F G T i ν
      RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound hG hS.1 hS.2.1)
    _ hΩc hΩ1 hcov
  obtain ⟨ΩN, hΩN, hcovN⟩ := exists_unipotentCompactCover_of_setup hS
  obtain ⟨ΩM, hΩM, hcovM⟩ := exists_leviCompactCover_of_setup centralSplitCompactQuotient hS
  let C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅) :=
    ⟨ΩN, ΩM, hΩN, hΩM, K, hKc⟩
  refine ⟨C, t, rfl, ?_⟩
  intro g
  obtain ⟨q, n, m, a, ha, _, ⟨k, hk, w, hw, rfl⟩, heq⟩ := ht g
  obtain ⟨mu, hmu⟩ := hcovM m
  set ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  set ιM := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)
  set muG : RationalGroupPoints F G :=
    (Standard.leviScheme i ν ∅).affinePointsTarget (Standard.leviHom i ν ∅)
      (CommAlgCat.of F F) mu
  have hmuG : ιM (rational F _ mu) = rational F G muG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.leviScheme i ν ∅)
      (Standard.leviHom i ν ∅)) mu).symm
  have hconj : rational F G muG * ιN n * (rational F G muG)⁻¹ ∈
      standardUnipotentImage F G T i ν := by
    have hp : rational F G muG ∈ standardParabolicImage F G T i ν :=
      standardLeviImage_le_parabolic F G T i ν ⟨rational F _ mu, hmuG⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (standardParabolicImage_le_normalizer F G T i ν hp) (ιN n)).mp ⟨n, rfl⟩
  obtain ⟨n'', hn''⟩ := hconj
  obtain ⟨_, ⟨ρ, rfl⟩, hρ⟩ := hcovN n''
  set ρG : RationalGroupPoints F G :=
    (Standard.unipotentScheme i ν ∅).affinePointsTarget (Standard.unipotentHom i ν ∅)
      (CommAlgCat.of F F) ρ
  have hρG : ιN (rational F _ ρ) = rational F G ρG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.unipotentScheme i ν ∅)
      (Standard.unipotentHom i ν ∅)) ρ).symm
  refine ⟨ρG * muG * q, _, (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν)
    C T₀ j _ _).mpr ⟨rational F _ ρ * n'', hρ, rationalNormOne F _ mu * m, hmu, a, ha, k, hk,
      rfl⟩, w, hw, ?_⟩
  change ιN (rational F _ ρ * n'') * ιM ((rationalNormOne F _ mu * m :
      normOneSubgroup F (Standard.leviScheme i ν ∅)) : AdelicGroupPoints F _) *
    positiveMap F G T i T₀ j a * k * w = rational F G (ρG * muG * q) * g
  have hn''' : ιN n'' = rational F G muG * ιN n * (rational F G muG)⁻¹ := hn''
  rw [Subgroup.coe_mul, rationalNormOne_val, map_mul, map_mul, hρG, hmuG, hn''', map_mul,
    map_mul, mul_assoc (rational F G ρG * rational F G muG), ← heq]
  group

/-- **Finite volume, connected reductive case.** For every connected reductive group over a
number field, the actual norm-one rational quotient has finite Haar volume. -/
theorem isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) :
    IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) := by
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  obtain ⟨K, H₁, W, hKc, hH₁, hKH₁, hH₁P, hcompat, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hS
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hS K hKc W hW hW1 hcov
  have hfin := measure_weakSiegelProduct_lt_top_of_openSubgroup
    AdelicGroupPoints.unipotentRationalQuotientCompact
    (positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates)
    (simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
      relativeCharacterRootComplement)
    F G hG T i ν T₀ j hS C t H₁ hH₁ hKH₁ hH₁P hcompat
  set S := weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t
  have hsub : Subtype.val ⁻¹' (S * W) ⊆
      (Subtype.val ⁻¹' S : Set (normOneSubgroup F G)) * Subtype.val ⁻¹' W := by
    rintro x ⟨s, hs, w, hw, hsw⟩
    have hs1 : s ∈ normOneSubgroup F G := by
      have : s = (x : AdelicGroupPoints F G) * w⁻¹ := by rw [← hsw, mul_inv_cancel_right]
      rw [this]
      exact (normOneSubgroup F G).mul_mem x.2 ((normOneSubgroup F G).inv_mem (hW1 hw))
    exact ⟨⟨s, hs1⟩, hs, ⟨w, hW1 hw⟩, hw, Subtype.ext hsw⟩
  have hfin' : (Measure.haar : Measure (normOneSubgroup F G)) (Subtype.val ⁻¹' (S * W)) < ∞ :=
    (measure_mono hsub).trans_lt (measure_mul_finite_lt_top _ hfin
      (hW.preimage Subtype.val_injective.injOn))
  refine LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_measure_lt_top
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G) hfin' ?_
  intro x
  obtain ⟨q, hq⟩ := hcover x
  refine ⟨rationalNormOne F G q, ⟨q, rfl⟩, ?_⟩
  rw [Set.mem_preimage, Subgroup.coe_mul, rationalNormOne_val]
  exact hq

end AdelicSiegelFactors

namespace AdelicGroupPoints

/-- Finite volume of the actual norm-one rational quotient for every connected reductive group
over a number field (Borel–Harish-Chandra). -/
theorem connectedReductiveFiniteVolume : ConnectedReductiveFiniteVolumeStatement.{u} :=
  fun F _ _ G _ _ hG =>
    AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive
      F G hG

/-- **Getz–Hahn, Theorem 2.6.3, over number fields.** For every smooth connected affine group
`G` over a number field `F`, the quotient of the actual norm-one Haar measure on `G(𝔸_F)¹` by
principal counting of `G(F)` is a finite measure. -/
theorem normOneRationalQuotientFiniteVolume :
    NormOneRationalQuotientFiniteVolumeStatement.{u} :=
  fun F _ _ G _ _ hs hc =>
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi
      characteristicZeroLeviDecomposition unipotentRationalQuotientCompact
      connectedReductiveFiniteVolume F G hs hc

end AdelicGroupPoints

end Langlands.Global
