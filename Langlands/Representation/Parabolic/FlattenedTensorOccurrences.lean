import Langlands.Representation.Filtration.CoarseJacquetFactorization
import Langlands.Representation.Parabolic.RefinedTensorOccurrences
import Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof
import Langlands.Representation.Tensor.FlattenedGLRefinement
import Langlands.Representation.Tensor.FiniteProperties

/-! Actual tensor occurrences through flattened Jacquet refinement. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- Pulling back along a group equivalence and its inverse cancels on the
actual smooth representation, with the identity carrier map. -/
def pullbackSymmIso (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    pullback e.symm (pullback e A) ≅ A :=
  mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => by
    ext v
    change A.representation (e (e.symm g)) v = A.representation g v
    rw [e.apply_symm_apply])

/-- Move a common group equivalence from the ambient to the constituent
without altering the actual subquotient relation. -/
theorem subquotient_pullback_right_iff (e : H ≃ₜ* G)
    {A : SmoothRep.{0, uG, uV} ℂ G} {D : SmoothRep.{0, uH, uV} ℂ H} :
    IsSubquotient D (pullback e A) ↔ IsSubquotient (pullback e.symm D) A := by
  constructor
  · intro h
    exact (h.pullback e.symm).of_iso_right (pullbackSymmIso e A)
  · intro h
    exact (h.pullback e).of_iso_left (pullbackSymmIso e.symm D)

end Langlands.SmoothRep

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem suppliedTopologyRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The rank-transported original factor in an actual nested block. -/
abbrev flattenedBlockFactor :
    letI := T.topology
    (∀ k, SmoothRep.{0, uF, uV} ℂ
      (GeneralLinear ((B.flatten S).size k) F.Carrier)) →
    ∀ i j, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S i).size j) F.Carrier) := by
  let := T.topology
  intro C i j
  exact B.flatten_size_flattenBlockEquiv S ⟨i, j⟩ ▸ C (B.flattenBlockEquiv S ⟨i, j⟩)

/-- The original flattened tensor regrouped into each coarse block. -/
def flattenedBlockTensor :
    letI := T.topology
    (∀ k, SmoothRep.{0, uF, uV} ℂ
      (GeneralLinear ((B.flatten S).size k) F.Carrier)) →
    ∀ i, SmoothRep.{0, uF, uV} ℂ ((S i).Levi F.Carrier) := by
  let := T.topology
  intro C i
  exact FiniteTensor.externalSmoothObject (flattenedBlockFactor T B S C i)

/-- The flattened external tensor and its nested block tensor agree over
the actual refined subgroup, including every rank transport. -/
def flattenedTensorRefinedIso :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ C : ∀ k, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.flatten S).size k) F.Carrier),
      SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject C) ≅
        SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject (flattenedBlockTensor T B S C)) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro C
  apply SmoothRep.mkIso
  change Representation.Equiv
    ((FiniteTensor.external (fun k => (C k).representation)).comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)
    ((FiniteTensor.external (fun i => FiniteTensor.external
      (fun j => (flattenedBlockFactor T B S C i j).representation))).comp
      (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom)
  simpa only [FiniteTensor.leviRefinementEquiv_flatten] using
    (FiniteTensor.glRefinementEquiv F T (B.flatten S) B S
      (B.flattenBlockEquiv S)
      (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) C)

/-- Bundle the actual composed-to-flat normalized Jacquet comparison over
the flattened product Levi. -/
def flattenedComposedJacquetIso :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S)
          ((T.normalizedComposedJacquetFunctor B S).obj π) ≅
        (T.normalizedJacquetFunctor (B.flatten S)).obj π := by
  let := T.topology
  let := suppliedTopologyRing T
  intro π
  exact SmoothRep.mkIso (Classical.choose
    (flattenedJacquetComparison.{uF, uF, uV}.2 F T B S π.representation))

/-- An actual occurrence in a standard flattened Jacquet module is the
corresponding actual occurrence in the composed quotient. -/
theorem subquotient_flattenedJacquet_iff :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, uV} ℂ ((B.flatten S).Levi F.Carrier)),
      SmoothRep.IsSubquotient D ((T.normalizedJacquetFunctor (B.flatten S)).obj π) ↔
        SmoothRep.IsSubquotient
          (SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S).symm D)
          ((T.normalizedComposedJacquetFunctor B S).obj π) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro π D
  constructor
  · intro h
    exact (SmoothRep.subquotient_pullback_right_iff
      (flattenedLeviEquivContinuous F.Carrier B S)).mp
      (h.of_iso_right (flattenedComposedJacquetIso T B S π).symm)
  · intro h
    exact ((SmoothRep.subquotient_pullback_right_iff
      (flattenedLeviEquivContinuous F.Carrier B S)).mpr h).of_iso_right
      (flattenedComposedJacquetIso T B S π)

private theorem external_irreducible_of_admissible
    {ι : Type} [Fintype ι] {H : ι → Type uF}
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (H i))
    (hi : ∀ i, (C i).IsIrreducible) (ha : ∀ i, (C i).IsAdmissible) :
    (FiniteTensor.externalSmoothObject C).IsIrreducible := by
  classical
  have : ∀ i, (C i).representation.IsIrreducible := hi
  exact FiniteTensor.isIrreducible_external (fun i => (C i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _ (ha i) (hi i) φ).exists)

private theorem rankCast_properties {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier),
      C.IsIrreducible → C.IsAdmissible →
      (h ▸ C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear s F.Carrier)).IsIrreducible ∧
        (h ▸ C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear s F.Carrier)).IsAdmissible := by
  let := T.topology
  cases h
  exact fun _ hi ha => ⟨hi, ha⟩

/-- The nested block tensors of admissible irreducible original factors
are themselves irreducible, with the exact flattened rank casts. -/
theorem flattenedBlockTensor_isIrreducible :
    letI := T.topology
    ∀ C : ∀ k, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.flatten S).size k) F.Carrier),
      (∀ k, (C k).IsIrreducible) → (∀ k, (C k).IsAdmissible) →
      ∀ i, (flattenedBlockTensor T B S C i).IsIrreducible := by
  let := T.topology
  intro C hi ha i
  exact external_irreducible_of_admissible (flattenedBlockFactor T B S C i)
    (fun j => (rankCast_properties T (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩)
      _ (hi _) (ha _)).1)
    (fun j => (rankCast_properties T (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩)
      _ (hi _) (ha _)).2)

/-- Extract admissible finite-length irreducible factors of the whole coarse
Jacquet module from an actual flattened tensor occurrence. Every original
inner-block tensor occurs in its corresponding actual block Jacquet module. -/
theorem exists_factorized_coarseJacquet_of_flattened (hn : 0 < n) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (C : ∀ k, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.flatten S).size k) F.Carrier)),
      π.IsAdmissible → π.HasFiniteLength →
      (∀ k, (C k).IsIrreducible) → (∀ k, (C k).IsAdmissible) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C)
        ((T.normalizedJacquetFunctor (B.flatten S)).obj π) →
      ∃ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
        (∀ i, (A i).IsIrreducible) ∧
        (∀ i, (A i).IsAdmissible) ∧
        (∀ i, (A i).HasFiniteLength) ∧
        SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
          ((T.normalizedJacquetFunctor B).obj π) ∧
        (∀ i, SmoothRep.IsSubquotient (flattenedBlockTensor T B S C i)
          ((T.normalizedJacquetFunctor (S i)).obj (A i))) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro π C hπ hfin hCi hCa h
  have hD : (SmoothRep.pullback (flattenedLeviEquivContinuous F.Carrier B S).symm
      (FiniteTensor.externalSmoothObject C)).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff
      (FiniteTensor.externalSmoothObject C).representation
      (flattenedLeviEquivContinuous F.Carrier B S).symm).mpr
      (external_irreducible_of_admissible C hCi hCa)
  obtain ⟨A, hAi, hAa, hAfin, hA, hDref⟩ :=
    exists_factorized_coarseJacquet_subquotient T B S hn hπ hfin hD
      ((subquotient_flattenedJacquet_iff T B S π
        (FiniteTensor.externalSmoothObject C)).mp h)
  refine ⟨A, hAi, hAa, hAfin, hA, ?_⟩
  exact subquotient_factor_of_refinedJacquet_external T B S A
    (flattenedBlockTensor T B S C) (flattenedBlockTensor_isIrreducible T B S C hCi hCa)
    (hDref.of_iso_left (flattenedTensorRefinedIso T B S C))

/-- Reassemble actual occurrences in all refined blocks of a coarse
constituent and return to the standard flattened Jacquet module of the same
ambient object. No irreducibility or finiteness hypothesis is needed. -/
theorem subquotient_flattenedJacquet_of_coarse_factors :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (C : ∀ k, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.flatten S).size k) F.Carrier)),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject A)
        ((T.normalizedJacquetFunctor B).obj π) →
      (∀ i, SmoothRep.IsSubquotient (flattenedBlockTensor T B S C i)
        ((T.normalizedJacquetFunctor (S i)).obj (A i))) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C)
        ((T.normalizedJacquetFunctor (B.flatten S)).obj π) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro π A C hA hC
  apply (subquotient_flattenedJacquet_iff T B S π
    (FiniteTensor.externalSmoothObject C)).mpr
  apply subquotient_composedJacquet_of_coarse_subquotient T B S hA
  exact (subquotient_refinedJacquet_external_of_factors T B S A
    (flattenedBlockTensor T B S C) hC).of_iso_left
    (flattenedTensorRefinedIso T B S C).symm

end Langlands.Parabolic
