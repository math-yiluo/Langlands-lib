import Langlands.Global.ArchimedeanCompactOrbitSource
import Langlands.Representation.CompactFiniteSemisimplicity
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Finite compact-type coverage of an actual compact-finite smooth vector -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

namespace ContinuousCompactRep

variable (τ : ContinuousCompactRep K n) (S : Subrepresentation τ.toRepresentation)

/-- Standard complex coordinates on an invariant subspace of a finite source. -/
def subrepresentationModelEquiv :
    (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) ≃ₗ[ℂ] S.toSubmodule :=
  (Module.finBasis ℂ S.toSubmodule).equivFun.symm

/-- The action on the standard coordinates of an invariant subspace. -/
def subrepresentationCoordinateAction :
    _root_.Representation ℂ (standardInfiniteCompact K n)
      (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) :=
  (((subrepresentationModelEquiv τ S).symm.conjAlgEquiv ℂ :
    Module.End ℂ S.toSubmodule →*
      Module.End ℂ (Fin (Module.finrank ℂ S.toSubmodule) → ℂ))).comp S.toRepresentation

omit [NumberField K] in
theorem continuous_subrepresentationCoordinateAction :
    Continuous fun p : standardInfiniteCompact K n ×
        (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) =>
      subrepresentationCoordinateAction τ S p.1 p.2 := by
  have he := (subrepresentationModelEquiv τ S).toLinearMap.continuous_of_finiteDimensional
  have hei :=
    (subrepresentationModelEquiv τ S).symm.toLinearMap.continuous_of_finiteDimensional
  have hp : Continuous fun p : standardInfiniteCompact K n ×
      (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) =>
      (p.1, ((subrepresentationModelEquiv τ S p.2) : Fin τ.dim → ℂ)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp (he.comp continuous_snd))
  have ha := ((τ.continuous_action.comp hp).subtype_mk
    (fun p => S.apply_mem_toSubmodule p.1 (subrepresentationModelEquiv τ S p.2).property))
  exact hei.comp ha

/-- The canonical continuous source representing an invariant subspace. -/
def subrepresentationSource : ContinuousCompactRep K n where
  dim := Module.finrank ℂ S.toSubmodule
  toRepresentation := subrepresentationCoordinateAction τ S
  continuous_action := continuous_subrepresentationCoordinateAction τ S

/-- Coordinates give an actual equivalence with the subrepresentation. -/
def subrepresentationSourceEquiv :
    (subrepresentationSource τ S).toRepresentation.Equiv S.toRepresentation where
  toLinearEquiv := subrepresentationModelEquiv τ S
  isIntertwining' _ := LinearMap.ext fun _ => by
    change subrepresentationModelEquiv τ S
      ((subrepresentationModelEquiv τ S).symm _) = _
    exact (subrepresentationModelEquiv τ S).apply_symm_apply _

/-- An irreducible invariant subspace, expressed as a published compact type. -/
def subrepresentationType (hS : IsAtom S) : CompactType K n where
  toContinuousCompactRep := subrepresentationSource τ S
  isIrreducible :=
    (Langlands.CentralEigenspaceSplitting.isIrreducible_iff_of_equiv
      (subrepresentationSourceEquiv τ S)).mpr
      (Langlands.FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS)

/-- The canonical equivariant inclusion of the coordinate source. -/
def subrepresentationSourceInclusion :
    (subrepresentationSource τ S).toRepresentation.IntertwiningMap τ.toRepresentation where
  toLinearMap := S.toSubmodule.subtype.comp (subrepresentationModelEquiv τ S).toLinearMap
  isIntertwining' _ := LinearMap.ext fun _ => by
    change (subrepresentationModelEquiv τ S
      ((subrepresentationModelEquiv τ S).symm _)).val = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

end ContinuousCompactRep

variable (K n)

omit [NumberField K] in
/-- Every actual finite continuous compact source is spanned by finitely many
irreducible invariant subspaces, with the usual topology on its coordinates. -/
theorem exists_finite_compact_source_atoms (τ : ContinuousCompactRep K n) :
    ∃ (m : ℕ) (S : Fin m → Subrepresentation τ.toRepresentation),
      (∀ i, IsAtom (S i)) ∧ (⨆ i, (S i).toSubmodule) = ⊤ := by
  let : MeasurableSpace (standardInfiniteCompact K n) :=
    borel (standardInfiniteCompact K n)
  have : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩
  let C : TopologicalSpace.PositiveCompacts (standardInfiniteCompact K n) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure (standardInfiniteCompact K n) := Measure.haarMeasure C
  have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  exact Langlands.Representation.CompactFinite.exists_finite_atoms
    τ.toRepresentation τ.continuous_action ν

/-- The finite type decomposition can be taken inside the actual range of
the original source map. -/
theorem exists_finite_types_covering_range_within (τ : ContinuousCompactRep K n)
    (F : τ.toRepresentation.IntertwiningMap (compactAction K n)) :
    ∃ (m : ℕ) (σ : Fin m → CompactType K n),
      LinearMap.range F.toLinearMap ≤
        ⨆ i, LinearMap.range F.toLinearMap ⊓ compactTypeSubmodule (σ i) := by
  classical
  obtain ⟨m, S, hS, hsup⟩ := exists_finite_compact_source_atoms K n τ
  let σ : Fin m → CompactType K n := fun i => τ.subrepresentationType (S i) (hS i)
  refine ⟨m, σ, ?_⟩
  have hle : (⨆ i, (S i).toSubmodule) ≤
      (⨆ i, LinearMap.range F.toLinearMap ⊓ compactTypeSubmodule (σ i)).comap
        F.toLinearMap := by
    refine iSup_le fun i => ?_
    intro v hv
    apply le_iSup (fun i =>
      LinearMap.range F.toLinearMap ⊓ compactTypeSubmodule (σ i)) i
    refine ⟨⟨v, rfl⟩, ?_⟩
    apply range_le_isotypicSpan (σ i).toContinuousCompactRep
      (F.comp (τ.subrepresentationSourceInclusion (S i)))
    refine ⟨(τ.subrepresentationModelEquiv (S i)).symm ⟨v, hv⟩, ?_⟩
    change F (τ.subrepresentationModelEquiv (S i)
      ((τ.subrepresentationModelEquiv (S i)).symm ⟨v, hv⟩)).val = F v
    rw [LinearEquiv.apply_symm_apply]
  rw [hsup] at hle
  rintro _ ⟨v, rfl⟩
  exact hle Submodule.mem_top

/-- An actual intertwiner from a finite continuous source has its whole range
in the sum of finitely many actual irreducible compact types. -/
theorem exists_finite_types_covering_range (τ : ContinuousCompactRep K n)
    (F : τ.toRepresentation.IntertwiningMap (compactAction K n)) :
    ∃ (m : ℕ) (σ : Fin m → CompactType K n),
      LinearMap.range F.toLinearMap ≤ selectedTypeSum Finset.univ σ := by
  obtain ⟨m, σ, hσ⟩ := exists_finite_types_covering_range_within K n τ F
  refine ⟨m, σ, hσ.trans (iSup_le fun i => ?_)⟩
  exact inf_le_right.trans
    (isotypicSpan_le_selectedIsotypicSum
      (fun i => (σ i).toContinuousCompactRep) (Finset.mem_univ i))

/-- The actual compact orbit span of a compact-finite smooth vector is
contained in a selected finite sum of the published irreducible compact types. -/
theorem exists_finite_types_covering_compactOrbit
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    ∃ (m : ℕ) (σ : Fin m → CompactType K n),
      Langlands.FiniteVectors.orbitSpan (compactAction K n) f ≤
        selectedTypeSum Finset.univ σ := by
  let F : (compactOrbitSource K n f hf).toRepresentation.IntertwiningMap
      (compactAction K n) :=
    { toLinearMap := compactOrbitSourceMap K n f hf
      isIntertwining' k := LinearMap.ext (compactOrbitSourceMap_equivariant K n f hf k) }
  obtain ⟨m, σ, hσ⟩ :=
    exists_finite_types_covering_range K n (compactOrbitSource K n f hf) F
  exact ⟨m, σ, (range_compactOrbitSourceMap K n f hf) ▸ hσ⟩

/-- Every actual compact-finite vector belongs to a selected finite type sum. -/
theorem exists_finite_types_containing
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    ∃ (m : ℕ) (σ : Fin m → CompactType K n),
      f ∈ selectedTypeSum Finset.univ σ := by
  obtain ⟨m, σ, hσ⟩ := exists_finite_types_covering_compactOrbit K n f hf
  exact ⟨m, σ, hσ (Langlands.FiniteVectors.self_mem_orbitSpan _ _)⟩

/-- A compact-finite vector is a finite sum of actual compact-type vectors,
all taken inside its original compact orbit span. -/
theorem exists_finite_compact_type_decomposition
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    ∃ (m : ℕ) (σ : Fin m → CompactType K n)
      (w : Fin m → DerivativeSmoothFunctions K n),
      (∀ i, w i ∈ Langlands.FiniteVectors.orbitSpan (compactAction K n) f ∧
        w i ∈ compactTypeSubmodule (σ i)) ∧ ∑ i, w i = f := by
  classical
  let F : (compactOrbitSource K n f hf).toRepresentation.IntertwiningMap
      (compactAction K n) :=
    { toLinearMap := compactOrbitSourceMap K n f hf
      isIntertwining' k := LinearMap.ext (compactOrbitSourceMap_equivariant K n f hf k) }
  obtain ⟨m, σ, hσ⟩ :=
    exists_finite_types_covering_range_within K n (compactOrbitSource K n f hf) F
  have hrange : LinearMap.range F.toLinearMap =
      Langlands.FiniteVectors.orbitSpan (compactAction K n) f :=
    range_compactOrbitSourceMap K n f hf
  rw [hrange] at hσ
  have hmem := hσ (Langlands.FiniteVectors.self_mem_orbitSpan _ _)
  have hmem' : f ∈ ⨆ i ∈ (Finset.univ : Finset (Fin m)),
      Langlands.FiniteVectors.orbitSpan (compactAction K n) f ⊓
        compactTypeSubmodule (σ i) := by
    simpa only [Finset.mem_univ, iSup_pos] using hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ f).mp hmem'
  refine ⟨m, σ, fun i => (w i).val, fun i => (w i).property, ?_⟩
  exact hw

end Langlands.Global.ArchimedeanGL
