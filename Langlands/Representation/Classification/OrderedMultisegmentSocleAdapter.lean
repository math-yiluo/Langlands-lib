import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.StrongIndecomposabilitySocleProof
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityProof

/-! # Assembly of the actual ordered-product socle

Finite length supplies Artinianity at positive rank.
The published mirabolic reduction transfers homogeneity and strong
indecomposability of the actual highest derivative to the full action.
Nontriviality and the actual-product derivative premises remain explicit.
This module does not prove `OrderedMultisegmentSocleExistence`.
-/

noncomputable section

namespace Langlands.Classification

open scoped MonoidAlgebra

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Homogeneity of the actual mirabolic restriction and strong
indecomposability of its actual highest derivative imply strong
indecomposability of the full general-linear action. -/
theorem generalLinear_stronglyIndecomposable_of_highestDerivative
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)),
      Nontrivial A →
      k = Derivative.level T ψ ((Derivative.generalLinearRestriction T N).obj A) →
      Derivative.IsGeneralLinearHomogeneous T ψ A →
      IsStronglyIndecomposable
        ((Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj
          ((Derivative.generalLinearRestriction T N).obj A)).representation →
      IsStronglyIndecomposable A.representation := by
  let := T.topology
  intro A hA hlevel hhom hderiv
  have hrestriction : Nontrivial ((Derivative.generalLinearRestriction T N).obj A) := hA
  have hmirabolic :=
    ((Derivative.mirabolicStrongIndecomposabilityReduction.{uF, uV} F T ψ N
      ((Derivative.generalLinearRestriction T N).obj A)).2 k hk hrestriction hlevel).mpr
        ⟨hhom, hderiv⟩
  exact stronglyIndecomposable_of_comp
    (GeneralLinear.mirabolic N F.Carrier).subtype hmirabolic

/-- Actual segment-socle blocks are irreducible, so their supplied normalized
product has finite length at positive total rank. -/
theorem segmentProduct_isFiniteLength
    {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hs : d.HasSegmentSocles) :
    letI := T.topology
    IsFiniteLength ℂ[GeneralLinear n F.Carrier] d.induced.representation.asModule := by
  let := T.topology
  apply irreducibleProductFiniteLength.{uF, max uF uV} F T n hn d.shape d.blocks
  intro i
  obtain ⟨A, hA, hπ⟩ := hs i
  exact hπ.1

/-- The actual positive-rank product module is Artinian. -/
theorem segmentProduct_isArtinian
    {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hs : d.HasSegmentSocles) :
    letI := T.topology
    IsArtinian ℂ[GeneralLinear n F.Carrier] d.induced.representation.asModule := by
  let := T.topology
  exact ((isFiniteLength_iff_isNoetherian_isArtinian
    (R := ℂ[GeneralLinear n F.Carrier]) (M := d.induced.representation.asModule)).mp
    (segmentProduct_isFiniteLength.{uF, uV} F T hn d hs)).2

/-- Apply the published Artinian bridge to the actual supplied product. -/
theorem segmentProduct_socle_of_stronglyIndecomposable
    {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : d.IsPrecedenceOrdered) (hs : d.HasSegmentSocles)
    (hnonzero : Nontrivial d.induced)
    (hArt : letI := T.topology
      IsArtinian ℂ[GeneralLinear n F.Carrier] d.induced.representation.asModule)
    (hSI : letI := T.topology
      IsStronglyIndecomposable d.induced.representation) :
    letI := T.topology
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      d.IsZelevinskySocle π := by
  let := T.topology
  obtain ⟨π, hπ⟩ :=
    (strongIndecomposabilitySocle.{0, uF, 0, max uF uV}).2.2.1
      (GeneralLinear n F.Carrier) d.induced hnonzero hArt hSI
  exact ⟨π, ho, hs, hπ⟩

/-- At positive rank, finite length discharges the Artinian input to the
actual-product socle bridge. Nontriviality and strong indecomposability
remain explicit. -/
theorem segmentProduct_socle_of_stronglyIndecomposable_pos
    {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : d.IsPrecedenceOrdered) (hs : d.HasSegmentSocles)
    (hnonzero : Nontrivial d.induced)
    (hSI : letI := T.topology
      IsStronglyIndecomposable d.induced.representation) :
    letI := T.topology
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      d.IsZelevinskySocle π := by
  let := T.topology
  exact segmentProduct_socle_of_stronglyIndecomposable.{uF, uV} F T d ho hs hnonzero
    (segmentProduct_isArtinian.{uF, uV} F T hn d hs) hSI

/-- The actual positive-rank product has a unique irreducible socle if it is
nonzero, its mirabolic restriction is homogeneous, and its actual highest
derivative is strongly indecomposable. These analytic premises remain explicit. -/
theorem segmentProduct_socle_of_highestDerivative
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1)
    (d : T.SegmentProductDatum.{max uF uV, uF} (N + 1))
    (ho : d.IsPrecedenceOrdered) (hs : d.HasSegmentSocles)
    (hnonzero : Nontrivial d.induced) :
    letI := T.topology
    k = Derivative.level T ψ ((Derivative.generalLinearRestriction T N).obj d.induced) →
    Derivative.IsGeneralLinearHomogeneous T ψ d.induced →
    IsStronglyIndecomposable
      ((Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj
        ((Derivative.generalLinearRestriction T N).obj d.induced)).representation →
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      d.IsZelevinskySocle π := by
  let := T.topology
  intro hlevel hhom hderiv
  exact segmentProduct_socle_of_stronglyIndecomposable_pos.{uF, uV} F T
    (Nat.zero_lt_succ N) d ho hs hnonzero
    (generalLinear_stronglyIndecomposable_of_highestDerivative.{uF, max uF uV} F T
      ψ N k hk d.induced hnonzero hlevel hhom hderiv)

end Langlands.Classification
