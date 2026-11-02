import Langlands.Global.Factors.RelativePolePairingStatement
import Langlands.Global.Factors.PolePairingDescentProof

/-!
# Actual witnessed relative-pair pole comparison
-/

noncomputable section

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

private theorem localWeil_unitaryDegree_eq {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uF} p) :
    LocalWeil.unitaryDegree.{uF, uW} K =
      degree (fun b : LocalWeil.UnitaryBasis.{uF, uW} K => (b.val.1 : ℕ)) := by
  apply integral_hom_ext
  intro b
  simp [LocalWeil.unitaryDegree, VirtualRepresentation.Weil.unitaryDegree,
    VirtualRepresentation.Weil.degree, rankedDegree,
    VirtualRepresentation.Weil.includeUnitary, includeSubset, VirtualRepresentation.map,
    generator, degree, extend]

private theorem padicSupercuspidal_unitaryDegree_eq {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uF} p) :
    PadicSupercuspidal.unitaryDegree.{uF, uW} K =
      degree (fun b : PadicSupercuspidal.UnitaryBasis.{uF, uW} K => (b.val.1 : ℕ)) := by
  apply integral_hom_ext
  intro b
  simp [PadicSupercuspidal.unitaryDegree, PadicSupercuspidal.degree,
    PadicSupercuspidal.includeUnitary, Supercuspidal.degree, rankedDegree,
    Supercuspidal.includeUnitary, includeSubset, VirtualRepresentation.map, generator,
    degree, extend]

theorem relativePolePairing : RelativePolePairingStatement.{uF, uW, uP} := by
  intro F E _ _ _ _ _ _ _ c _ v ψ hcomparison
  obtain ⟨⟨ν, hν⟩, hdata⟩ := hcomparison
  obtain ⟨d, hregular, hleft, hright⟩ := hdata ν hν
  let left := fun j : WitnessedGenerator.{uF, uW, uP} F E c v => j.weilElement
  let right := fun j : WitnessedGenerator.{uF, uW, uP} F E c v => j.automorphicElement
  let sourceWeight := fun b : LocalWeil.UnitaryBasis.{uF, uW} (padicField v) =>
    (b.val.1 : ℕ)
  let targetWeight := fun b : PadicSupercuspidal.UnitaryBasis.{uF, uF} (padicField v) =>
    (b.val.1 : ℕ)
  have hgram := poleGramComparison _ _ _ _ _ left right d.comparison hregular hleft hright
  have hdegree : ∀ j, degree targetWeight (right j) = degree sourceWeight (left j) := by
    intro j
    change degree targetWeight j.automorphicElement =
      degree sourceWeight j.weilElement
    rw [← padicSupercuspidal_unitaryDegree_eq, ← localWeil_unitaryDegree_eq]
    exact j.degrees_eq.symm
  obtain ⟨hrelations, T, hT, hunique⟩ :=
    generatedPositiveIsometry_of_gram left right sourceWeight targetWeight hgram hdegree
  have hactual : RelativeGeneratedPositiveIsometry F E c v T := by
    refine ⟨?_, hT.2.1, ?_, ?_⟩
    · intro j
      have hj := hT.1 j
      rw [evaluateGenerators_generator, evaluateGenerators_generator] at hj
      exact hj
    · intro x
      rw [padicSupercuspidal_unitaryDegree_eq, localWeil_unitaryDegree_eq]
      exact hT.2.2.1 x
    · intro x hnorm hpositive
      apply hT.2.2.2 x hnorm
      rwa [localWeil_unitaryDegree_eq] at hpositive
  refine ⟨hgram, hrelations, T, hactual, ?_⟩
  intro S hS
  apply hunique S
  refine ⟨?_, hS.2.1, ?_, ?_⟩
  · intro j
    rw [evaluateGenerators_generator, evaluateGenerators_generator]
    exact hS.1 j
  · intro x
    rw [← padicSupercuspidal_unitaryDegree_eq, ← localWeil_unitaryDegree_eq]
    exact hS.2.2.1 x
  · intro x hnorm hpositive
    apply hS.2.2.2 x hnorm
    rwa [localWeil_unitaryDegree_eq]

end Langlands.Global.PoleComparison
