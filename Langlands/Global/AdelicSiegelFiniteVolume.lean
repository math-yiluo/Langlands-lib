import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicReductiveFiniteVolumeStatement

/-! # Finite Haar measure of Siegel sets and reductive finite volume -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- A discrete subgroup whose translates of one set of finite Haar outer measure cover the
group has finite Haar covolume. -/
theorem isFiniteMeasure_haarQuotientMeasure_of_measure_lt_top (Λ : Subgroup H)
    (hΛ : IsDiscrete (Λ : Set H)) {S : Set H} (hS : (Measure.haar : Measure H) S < ∞)
    (hcover : ∀ g, ∃ γ ∈ Λ, γ * g ∈ S) : IsFiniteMeasure (haarQuotientMeasure Λ hΛ) := by
  have : Countable Λ := countable_of_isDiscrete Λ hΛ
  have hS' : MeasurableSet (toMeasurable (Measure.haar : Measure H) S) :=
    measurableSet_toMeasurable _ _
  have himage : mk Λ '' toMeasurable (Measure.haar : Measure H) S = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨g, rfl⟩ := mk_surjective Λ q
    obtain ⟨γ, hγ, hγS⟩ := hcover g
    exact ⟨γ * g, subset_toMeasurable _ _ hγS, mk_subgroup_mul Λ ⟨γ, hγ⟩ g⟩
  have hle := quotientMeasure_image_le Λ (Measure.haar : Measure H)
    (isFundamentalDomain Λ hΛ Measure.haar) hS'
  rw [himage, measure_toMeasurable] at hle
  exact ⟨lt_of_le_of_lt hle hS⟩

end Langlands.Global.LeftCosetSpace

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

section Compatibility

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- Every element of the subgroup `K` that lies in the image of the actual canonical standard
parabolic `P(𝔸_F)` commutes with every element of the actual positive torus `A_{T₀}`. -/
def IsPositiveTorusCompatible (K : Subgroup (AdelicGroupPoints F G)) : Prop :=
  ∀ k ∈ K,
    k ∈ Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) →
      ∀ a : PositiveRealTorus.intrinsicSubgroup F T₀,
        Commute k (positiveMap F G T i T₀ j a)

end Compatibility

/-- **Finite Haar measure of Siegel sets.** For every number field `F`, every connected
reductive `F`-group `G`, every actual algebraic Siegel setup and every compact factor data
whose compact subgroup `K` is a maximal compact subgroup with `P(𝔸_F) K = G(𝔸_F)` and whose
parabolic part `P(𝔸_F) ∩ K` commutes with `A_{T₀}`, the actual ordered weak Siegel product
`Ω_N Ω_M A_{T₀}(t) K` meets the norm-one group `G(𝔸_F)¹` in a set of finite left Haar
measure, for every positive threshold `t`. -/
def SiegelProductFiniteMeasureStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          ∀ (C : CompactFactors F G
              (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
            (t : ℝ≥0ˣ),
            IsParabolicIwasawaCompact F G
                (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
                C.compactSubgroup →
              IsPositiveTorusCompatible F G T i ν T₀ j C.compactSubgroup →
                haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
                (Measure.haar : Measure (normOneSubgroup F G))
                    (Subtype.val ⁻¹' weakSiegelProduct F G T i ν
                      (canonicalStandardFactors F G T i ν) C T₀ j t) < ∞

/-- The number-field connected-reductive Siegel reduction target of
`AdelicSiegelReductionStatement`, with the additional requirement that the parabolic part of
the compact subgroup commutes with the positive torus `A_{T₀}`. -/
def AdelicGoodSiegelReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
          ∃ (C : CompactFactors F G
              (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
            (t : ℝ≥0ˣ),
            IsSiegelCover F G T i ν T₀ j C t ∧
              IsPositiveTorusCompatible F G T i ν T₀ j C.compactSubgroup

/-- The good-position Siegel reduction target implies the Library Siegel reduction target. -/
theorem adelicSiegelReductionStatement_of_good
    (h : AdelicGoodSiegelReductionStatement.{u}) : AdelicSiegelReductionStatement.{u} := by
  intro F _ _ G _ _ hG
  obtain ⟨T, i, ν, T₀, j, hsetup, C, t, hcover, -⟩ := h F G hG
  exact ⟨T, i, ν, T₀, j, hsetup, C, t, hcover⟩

/-- Good-position Siegel reduction together with finite Haar measure of Siegel sets gives
finite volume of the actual norm-one rational quotient of every connected reductive group. -/
theorem isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_siegel
    (hred : AdelicGoodSiegelReductionStatement.{u})
    (hmeas : SiegelProductFiniteMeasureStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) :
    IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) := by
  obtain ⟨T, i, ν, T₀, j, hsetup, C, t, hcover, hgood⟩ := hred F G hG
  have hfin := hmeas F G hG T i ν T₀ j hsetup C t hcover.1 hgood
  refine LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_measure_lt_top
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G) hfin ?_
  intro x
  have hx : (x : AdelicGroupPoints F G) ∈
      (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
        weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t := by
    rw [hcover.2]
    exact x.2
  obtain ⟨r, ⟨q, rfl⟩, s, hs, hrs⟩ := hx
  refine ⟨rationalNormOne F G q⁻¹, ⟨q⁻¹, rfl⟩, ?_⟩
  rw [Set.mem_preimage, Subgroup.coe_mul, rationalNormOne_val, map_inv, ← hrs,
    inv_mul_cancel_left]
  exact hs

/-- Good-position Siegel reduction together with finite Haar measure of Siegel sets gives the
Library connected-reductive finite-volume target. -/
theorem connectedReductiveFiniteVolumeStatement_of_siegel
    (hred : AdelicGoodSiegelReductionStatement.{u})
    (hmeas : SiegelProductFiniteMeasureStatement.{u}) :
    ConnectedReductiveFiniteVolumeStatement.{u} :=
  fun F _ _ G _ _ hG =>
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_siegel hred hmeas F G hG

end Langlands.Global.AdelicSiegelFactors
