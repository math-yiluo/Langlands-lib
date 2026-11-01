import Langlands.Representation.RankinSelberg.AdjacentRankFullRankCutoff
import Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! One compact open level for all full-rank approximating normalized sections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.Padic

open Set Filter Topology HarmonicAnalysis Matrix

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance invariantApproximationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance invariantApproximationValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance invariantApproximationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance invariantApproximationT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance invariantApproximationSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance invariantApproximationNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance invariantApproximationGLNonarch (n : ℕ) :
    NonarchimedeanGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearNonarchimedean n
local instance invariantApproximationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n

variable {r : ℕ}

/-- A compact open subgroup fixing a Schwartz test and killing a smooth scalar weight. -/
theorem exists_adjacentRankTestWeightLevel
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (r + 2) F.Carrier)) :
    ∃ J : OpenSubgroup (GeneralLinear (r + 2) F.Carrier),
      IsCompact (J : Set (GeneralLinear (r + 2) F.Carrier)) ∧
      (∀ M (k : J.toSubgroup), Φ (M * k.val.val) = Φ M) ∧
      ∀ k : J.toSubgroup, θ.toMonoidHom k.val = 1 := by
  obtain ⟨U, hU⟩ := rectangularTestSmooth Φ
  let K : OpenSubgroup (GeneralLinear (r + 2) F.Carrier) :=
    ⟨θ.toMonoidHom.ker, θ.isOpen_ker⟩
  obtain ⟨J, hJc, hJ⟩ := compactOpenSubgroupBasis
    (GeneralLinear (r + 2) F.Carrier) (↑(U ⊓ K))
    ((U ⊓ K).isOpen.mem_nhds (U ⊓ K).one_mem)
  exact ⟨J, hJc, fun M k => hU k.val (hJ k.property).1 M,
    fun k => (hJ k.property).2⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (χ : Quasicharacter F.Carrier)

/-- Full-rank tests approximating one Schwartz test, all of whose actual normalized
sections lie at one compact open level, uniformly in the original vector. -/
structure AdjacentRankInvariantApproximationData (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) where
  level : OpenSubgroup (GeneralLinear (r + 2) F.Carrier)
  isCompact_level : IsCompact (level : Set (GeneralLinear (r + 2) F.Carrier))
  tests : ℕ → adjacentRankCompactTests (r + 1) F.Carrier
  invariant : ∀ n M (k : level.toSubgroup),
    (tests n).val (M * k.val.val) = (tests n).val M
  norm_le : ∀ n M, ‖(tests n).val M‖ ≤ ‖Φ M‖
  eventually_eq : ∀ M, AdjacentRankFullRank M →
    ∀ᶠ n in atTop, (tests n).val M = Φ M
  fixed : ∀ n v, adjacentRankNormalizedSection F σ χ hσ (tests n) v ∈
    fixedVectors
      (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))))
      level.toSubgroup

/-- Invariant cutoff tests exist at one compact open level of the exact host induction. -/
theorem nonempty_adjacentRankInvariantApproximation (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    Nonempty (AdjacentRankInvariantApproximationData F σ χ hσ Φ) := by
  let θ := adjacentRankDeterminantWeight F.canonicalTopologicalData χ
    (r + 2) ((r + 1 : ℕ) / 2)
  obtain ⟨J, hJc, hΦ, hθ⟩ := exists_adjacentRankTestWeightLevel F Φ θ
  obtain ⟨Ψ, hΨ, hnorm, heq⟩ :=
    exists_adjacentRankFullRankTestApproximation J.toSubgroup hJc Φ hΦ
  refine ⟨⟨J, hJc, Ψ, hΨ, hnorm, heq, ?_⟩⟩
  intro n v
  change ∀ k : J.toSubgroup,
    F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))) k.val
      (adjacentRankNormalizedSection F σ χ hσ (Ψ n) v) =
      adjacentRankNormalizedSection F σ χ hσ (Ψ n) v
  intro k
  have ht : adjacentRankCompactTestTranslate k.val (Ψ n) = Ψ n := by
    apply Subtype.ext
    ext M
    exact hΨ n M k
  rw [adjacentRankNormalizedSection_right, ht]
  change (θ.toMonoidHom k.val : ℂ) • _ = _
  rw [hθ k, Units.val_one]
  exact one_smul ℂ _

/-- Choose one invariant approximation, retaining the exact normalized sections on V. -/
def adjacentRankInvariantApproximation (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    AdjacentRankInvariantApproximationData F σ χ hσ Φ :=
  Classical.choice (nonempty_adjacentRankInvariantApproximation F σ χ hσ Φ)

end Langlands.RankinSelberg.Padic
