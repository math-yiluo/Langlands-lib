import Langlands.Representation.Whittaker.UnipotentOrbitProof
import Langlands.Representation.Whittaker.NonOpenCharacterProof
import Langlands.Representation.Whittaker.GelfandGraev
import Langlands.Representation.Geometric.OrbitRepresentatives
import Langlands.Representation.Whittaker.OpenStabilizer

/-!
# The `N`–`P` double cosets for the Gelfand–Graev Jacquet module

Restrict the Gelfand–Graev representation `c-Ind_N^G ψ` of `G = GL_(n+1)(F)` to a standard block
parabolic `P`. The Mackey filtration is indexed by an ordering of `N \ G / P`. This module
provides such an ordering whose representatives are inverse minimal permutation matrices. The
block-reversal matrix represents one orbit. Every other orbit has a stabilizer element in the
unipotent radical of `P` on which the conjugated character `ψ_N` is not trivial.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric HarmonicAnalysis

universe uF

/-- Inverting group elements swaps the two sides of a double coset quotient. -/
theorem doubleCoset_mk_inv_eq_iff {G : Type*} [Group G] (H K : Subgroup G) (a b : G) :
    DoubleCoset.mk K H a⁻¹ = DoubleCoset.mk K H b⁻¹ ↔
      DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨k, hk, h, hh, heq⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [← inv_inv b, heq]
    simp [mul_assoc]
  · rintro ⟨h, hh, k, hk, heq⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, ?_⟩
    rw [heq]
    simp [mul_assoc]

/-- Minimal permutation matrices classify the `N`–`P` double cosets: the map
`w ↦ N perm(w) P` is a bijection. -/
theorem gelfandGraevDoubleCoset_bijective (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    (B : BlockShape (n + 1)) :
    Function.Bijective
      (fun w : MinimalRepresentatives B (BlockShape.singletons (n + 1)) =>
        DoubleCoset.mk (upperUnipotent (n + 1) F.Carrier) (B.parabolic F.Carrier)
          ((permutation (n + 1) F.Carrier w.val)⁻¹)⁻¹) := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨hbij, -⟩ := unipotentOrbit p F n B
  constructor
  · intro v w hvw
    apply hbij.1
    exact (doubleCoset_mk_inv_eq_iff (B.parabolic F.Carrier) (upperUnipotent (n + 1) F.Carrier)
      _ _).mp hvw
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, hw⟩ := hbij.2 (DoubleCoset.mk (B.parabolic F.Carrier)
      (upperUnipotent (n + 1) F.Carrier) g⁻¹)
    refine ⟨w, ?_⟩
    have h := (doubleCoset_mk_inv_eq_iff (B.parabolic F.Carrier)
      (upperUnipotent (n + 1) F.Carrier) _ _).mpr hw
    rw [inv_inv] at h
    exact h

/-- An ordering of the `N`–`P` double cosets for the Gelfand–Graev Mackey filtration. The
block-reversal matrix represents the orbit with index `j`. For every other index there is a
stabilizer element in the unipotent radical whose conjugate into `N` is not in the kernel of
the standard character. -/
theorem gelfandGraevOrbitData (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (B : BlockShape (n + 1)) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
    ∃ (m : ℕ) (s : OrderedDoubleCosets (upperUnipotent (n + 1) F.Carrier)
        (B.parabolic F.Carrier) m) (j : Fin m),
      s.representative j = B.reverseMatrix F.Carrier ∧
      ∀ i, i ≠ j → ∃ x : orbitStabilizer (upperUnipotent (n + 1) F.Carrier)
          (B.parabolic F.Carrier) (s.representative i),
        (x : B.parabolic F.Carrier) ∈ B.unipotentRadical F.Carrier ∧
          standardCharacter ψ n (stabilizerToInducing (upperUnipotent (n + 1) F.Carrier)
            (B.parabolic F.Carrier) (s.representative i) x) ≠ 1 := by
  let := F.canonicalTopologicalData.topology
  let T := F.canonicalTopologicalData
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.fieldT2
  let := T.generalLinearT2Space (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearSigmaCompactSpace (n + 1)
  let N := upperUnipotent (n + 1) F.Carrier
  let P := B.parabolic F.Carrier
  let r : MinimalRepresentatives B (BlockShape.singletons (n + 1)) →
      Langlands.GeneralLinear (n + 1) F.Carrier :=
    fun w => (permutation (n + 1) F.Carrier w.val)⁻¹
  have hbij := gelfandGraevDoubleCoset_bijective p F n B
  let : Finite (DoubleCoset.Quotient (N : Set (Langlands.GeneralLinear (n + 1) F.Carrier))
      (P : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :=
    Finite.of_surjective _ hbij.2
  obtain ⟨m, ⟨s₀⟩⟩ := closedSubgroupOrbitOrdering (Langlands.GeneralLinear (n + 1) F.Carrier)
    N P (UpperUnipotent.isClosed (R := F.Carrier)) (B.isClosed_parabolic F.Carrier) inferInstance
  obtain ⟨e, s, hs⟩ := s₀.classifiedRepresentatives r hbij
  let vopen : MinimalRepresentatives B (BlockShape.singletons (n + 1)) :=
    ⟨B.reversePermutation.symm, reversePermutation_isMinimalRepresentative B⟩
  have hψ : ψ.complex ≠ 1 := by
    intro he
    apply ψ.nontrivial
    ext x
    exact congrArg (fun χ : AddChar F.Carrier ℂ => χ x) he
  refine ⟨m, s, e.symm vopen, ?_, ?_⟩
  · rw [hs, e.apply_symm_apply]
    change (permutation (n + 1) F.Carrier B.reversePermutation.symm)⁻¹ =
      permutation (n + 1) F.Carrier B.reversePermutation
    rw [← map_inv]
    rfl
  · intro i hi
    have hv : (e i).val ≠ B.reversePermutation.symm := by
      intro hv
      apply hi
      apply e.injective
      rw [e.apply_symm_apply]
      exact Subtype.ext hv
    obtain ⟨q, hq, hqψ⟩ := nonOpenCharacterWitness F.Carrier n B ψ.complex hψ (e i) hv
    rw [hs i]
    let w := permutation (n + 1) F.Carrier (e i).val
    have hmem : stabilizerToInducing P N w q ∈ orbitStabilizer N P (r (e i)) := by
      change ((MulAut.conj (r (e i))⁻¹) ((stabilizerToInducing P N w q : P) :
        Langlands.GeneralLinear (n + 1) F.Carrier)) ∈ N
      rw [stabilizerToInducing_apply]
      change ((MulAut.conj w⁻¹⁻¹) (w⁻¹ * ((q.val : N) : Langlands.GeneralLinear (n + 1) F.Carrier)
        * w)) ∈ N
      simp only [inv_inv, MulAut.conj_apply, mul_assoc, mul_inv_cancel, mul_one,
        mul_inv_cancel_left]
      exact (q.val : N).property
    refine ⟨⟨stabilizerToInducing P N w q, hmem⟩, hq, ?_⟩
    have hconj : stabilizerToInducing N P (r (e i)) ⟨stabilizerToInducing P N w q, hmem⟩ =
        q.val := by
      apply Subtype.ext
      rw [stabilizerToInducing_apply]
      change w⁻¹⁻¹ * (w⁻¹ * ((q.val : N) : Langlands.GeneralLinear (n + 1) F.Carrier) * w) *
        w⁻¹ = _
      simp [mul_assoc]
    rw [hconj, ← entrywiseCharacter_eq_standardCharacter]
    exact hqψ

end Langlands.Whittaker
