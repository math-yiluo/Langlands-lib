import Langlands.Representation.Parabolic.ProductReversalFactorsStatement
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Parabolic.InductionFiltration
import Langlands.Representation.Tensor.ProductFiltration
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.JordanHolderTransportProof
import Langlands.Representation.Filtration.LengthCriterionProof

/-!
# Composition-factor commutativity of two-factor products of finite length

Zelevinsky (1980), Theorem 1.9, derived from its irreducible two-factor case.
-/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV

/-- A smooth representation of finite length has an actual composition series. -/
theorem exists_hasSimpleFactors_of_hasFiniteLength {G : Type uF} [Group G]
    [TopologicalSpace G] (A : SmoothRep.{0, uF, uV} ℂ G) (h : A.HasFiniteLength) :
    ∃ (r : ℕ) (s : ObjectRepFiltration (Rep.of A.representation) r), s.HasSimpleFactors := by
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact ⟨_, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries
    (A := Rep.of A.representation) c h₀ h₁⟩

section Reduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- If reordering the blocks of `B` by `σ` preserves the composition factors of
every product of irreducible factors, it preserves those of every product of
finite-length factors. -/
theorem productPermutationFactors_of_irreducible {n : ℕ} (B : BlockShape n)
    (σ : Equiv.Perm (Fin B.length)) :
    letI := T.topology
    (∀ C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (C i).IsIrreducible) →
      HaveSameJordanHolderFactors
        (Rep.of ((T.normalizedProductInductionFunctor B).obj C).representation)
        (Rep.of ((T.normalizedProductInductionFunctor (B.permute σ)).obj
          (fun i => C (σ i))).representation)) →
    ∀ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (A i).HasFiniteLength) →
      HaveSameJordanHolderFactors
        (Rep.of ((T.normalizedProductInductionFunctor B).obj A).representation)
        (Rep.of ((T.normalizedProductInductionFunctor (B.permute σ)).obj
          (fun i => A (σ i))).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hirr A hA
  choose r s hs using fun i => exists_hasSimpleFactors_of_hasFiniteLength (A i) (hA i)
  obtain ⟨N, f, E, hE⟩ := FiniteTensorFiltration.exists_external B.length
    (H := fun i => GeneralLinear (B.size i) F.Carrier)
    (fun i => Rep.of (A i).representation) r s
  obtain ⟨N', f', E', hE'⟩ := FiniteTensorFiltration.exists_external (B.permute σ).length
    (H := fun i => GeneralLinear ((B.permute σ).size i) F.Carrier)
    (fun i => Rep.of (A (σ i)).representation) (fun i => r (σ i)) (fun i => s (σ i))
  let Φ : (∀ i, Fin (r i)) ≃ (∀ i, Fin (r (σ i))) :=
    Equiv.piCongrLeft' (fun i => Fin (r i)) σ.symm
  have hΦ (x : ∀ i, Fin (r i)) (i : Fin B.length) : Φ x i = x (σ i) := rfl
  have hN : N' = N := by
    simpa using (Fintype.card_congr (E.trans (Φ.trans E'.symm))).symm
  subst hN
  let e : Equiv.Perm (Fin N') := E.trans (Φ.trans E'.symm)
  have hsmooth : ∀ (i : Fin B.length) (j : Fin (r i)),
      IsSmooth ((s i).gradedRepresentation j).ρ := fun i j =>
    isSmooth_of_surjective ((s i).gradedProjection j).hom
      ((s i).gradedProjection_surjective j)
      (isSmooth_of_injective (FactorMatchingProof.subrepInclusion _)
        Subtype.val_injective (A i).isSmooth)
  let C : Fin N' → ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun j i => SmoothRep.of ((s i).gradedRepresentation (E j i)).ρ (hsmooth i (E j i))
  let indF := normalizedInductionFiltration T B (B.blockTensor fun i => (A i).representation) f
  let indF' := normalizedInductionFiltration T (B.permute σ)
    ((B.permute σ).blockTensor fun i => (A (σ i)).representation) f'
  have hmatch : ∀ j : Fin N', HaveSameJordanHolderFactors (indF.gradedRepresentation j)
      (indF'.gradedRepresentation (e j)) := by
    intro j
    have h₁ := nonempty_normalizedInductionFiltrationGradedEquiv T B
      (B.blockTensor fun i => (A i).representation) f j
      (B.blockTensor fun i => (C j i).representation)
      (FiniteTensor.isSmooth_external _ fun i => (A i).isSmooth)
      (FiniteTensor.isSmooth_external _ fun i => (C j i).isSmooth) (hE j).some
    have hE'j : E' (e j) = Φ (E j) := E'.apply_symm_apply _
    have h₂ := hE' (e j)
    rw [hE'j] at h₂
    have h₃ := nonempty_normalizedInductionFiltrationGradedEquiv T (B.permute σ)
      ((B.permute σ).blockTensor fun i => (A (σ i)).representation) f' (e j)
      ((B.permute σ).blockTensor fun i => (C j (σ i)).representation)
      (FiniteTensor.isSmooth_external _ fun i => (A (σ i)).isSmooth)
      (FiniteTensor.isSmooth_external _ fun i => (C j (σ i)).isSmooth) h₂.some
    exact haveSameJordanHolderFactors_transport
      (hirr (C j) fun i => hs i (E j i)) h₁.some.symm h₃.some.symm
  exact gradedJordanHolderRefinement ℂ (GeneralLinear n F.Carrier) _ _ N' indF indF' e hmatch

end Reduction

/-- Theorem 1.9 for two finite-length factors, from its irreducible case. -/
theorem twoBlockProductReversalFactors_of_irreducible
    (hirr : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
      Classification.TwoFactorProductConstituentCommutativity.{uF, uV} F T) :
    TwoBlockProductReversalFactors.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro a b ha hb π₁ π₂ h₁ h₂
  let := T.generalLinearTopologicalGroup (a + b)
  let B := BlockShape.binary a b ha hb
  let A : ∀ i : Fin B.length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => Fin.cases π₁ (fun _ => π₂) i
  have hA : ∀ i, (A i).HasFiniteLength := fun i => Fin.cases h₁ (fun _ => h₂) i
  exact productPermutationFactors_of_irreducible F T B (B.adjacentSwap 0 Nat.one_lt_two)
    (hirr p F T (a + b) B rfl) A hA

/-- Zelevinsky (1980), Theorem 1.9, for two factors of finite length. -/
theorem twoBlockProductReversalFactors : TwoBlockProductReversalFactors.{uF, uV} :=
  twoBlockProductReversalFactors_of_irreducible fun _ _ F T =>
    Classification.twoFactorProductConstituentCommutativity.{uF, uV} F T

end Langlands.Parabolic
