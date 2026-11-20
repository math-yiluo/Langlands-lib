import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # Genuine smooth vectors in invariant Hilbert subspaces -/

noncomputable section

open scoped Manifold ContDiff Topology
open Topology

namespace Langlands.Archimedean.SmoothInvariantSubspace

universe u𝔤 uH uG uE

variable {G : Type uG} [Group G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) (U : Submodule ℂ E)
  (hU : ∀ g v, v ∈ U → π g v ∈ U)

/-- Restrict an action by bounded operators to an invariant subspace. -/
def restriction : G →* (U →L[ℂ] U) where
  toFun g := (π g).restrict (hU g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    change π 1 (v : E) = v
    simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    change π (g * h) (v : E) = π g (π h (v : E))
    simp

@[simp]
theorem restriction_apply (g : G) (v : U) :
    (restriction π U hU g v : E) = π g v := rfl

/-- Restriction preserves an isometry hypothesis on the supplied action. -/
theorem isometry_restriction (hπ : ∀ g, Isometry (π g)) (g : G) :
    Isometry (restriction π U hU g) := by
  intro v w
  exact hπ g v w

variable [TopologicalSpace G]

include hU in
/-- Joint continuity descends to the invariant subspace with its norm topology. -/
theorem isContinuousRepresentation_restriction (hπ : IsContinuousRepresentation π) :
    IsContinuousRepresentation (restriction π U hU) := by
  apply Continuous.subtype_mk
  exact hπ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  [ChartedSpace H G]

/-- Smoothness in the subspace implies smoothness in the ambient representation. -/
theorem isSmoothVector_coe {v : U}
    (hv : IsSmoothVector I (restriction π U hU) v) :
    IsSmoothVector I π (v : E) := by
  have he : orbitMap π (v : E) =
      (U.subtypeL.restrictScalars ℝ) ∘ orbitMap (restriction π U hU) v := rfl
  change ContMDiff I 𝓘(ℝ, E) ∞ (orbitMap π (v : E))
  rw [he]
  exact (U.subtypeL.restrictScalars ℝ).contDiff.contMDiff.comp hv

variable [CompleteSpace U]

/-- Orthogonal projection recovers smoothness in the invariant subspace. -/
theorem isSmoothVector_of_coe {v : U} (hv : IsSmoothVector I π (v : E)) :
    IsSmoothVector I (restriction π U hU) v := by
  have he : orbitMap (restriction π U hU) v =
      (U.orthogonalProjectionOnto.restrictScalars ℝ) ∘ orbitMap π (v : E) := by
    funext g
    exact (U.orthogonalProjectionOnto_mem_subspace_eq_self
      (restriction π U hU g v)).symm
  change ContMDiff I 𝓘(ℝ, U) ∞ (orbitMap (restriction π U hU) v)
  rw [he]
  exact (U.orthogonalProjectionOnto.restrictScalars ℝ).contDiff.contMDiff.comp hv

/-- Genuine smoothness of a subspace vector is equivalent to ambient smoothness. -/
theorem isSmoothVector_iff (v : U) :
    IsSmoothVector I (restriction π U hU) v ↔ IsSmoothVector I π (v : E) :=
  ⟨isSmoothVector_coe π U hU I, isSmoothVector_of_coe π U hU I⟩

omit [CompleteSpace U] in
/-- Inclusion on the genuine smooth-vector subspaces. -/
def smoothInclusion :
    smoothVectors I (restriction π U hU) →ₗ[ℂ] smoothVectors I π where
  toFun v := ⟨(v : U), isSmoothVector_coe π U hU I v.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

omit [CompleteSpace U] in
@[simp]
theorem smoothInclusion_apply (v : smoothVectors I (restriction π U hU)) :
    (smoothInclusion π U hU I v : E) = (v : U) := rfl

omit [CompleteSpace U] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual real orbit derivative commutes with subspace inclusion. -/
theorem lieDerivative_coe (X : 𝔤) {v : U}
    (hv : IsSmoothVector I (restriction π U hU) v) :
    lieDerivative I π X (v : E) =
      (↑(lieDerivative I (restriction π U hU) X v : U) : E) := by
  let A := U.subtypeL.restrictScalars ℝ
  have hf : MDifferentiableAt I 𝓘(ℝ, U)
      (orbitMap (restriction π U hU) v) 1 :=
    hv.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt 𝓘(ℝ, U) 𝓘(ℝ, E) A
      (orbitMap (restriction π U hU) v 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : orbitMap π (v : E) = A ∘ orbitMap (restriction π U hU) v := rfl
  unfold lieDerivative
  rw [he, mfderiv_comp 1 hA hf, ContinuousLinearMap.mfderiv_eq]
  rfl

variable [LieGroup I ∞ G]

omit [CompleteSpace U] in
/-- Inclusion commutes with the genuine derived operators on smooth vectors. -/
theorem smoothInclusion_smoothLieDerivative (X : 𝔤)
    (v : smoothVectors I (restriction π U hU)) :
    smoothInclusion π U hU I (smoothLieDerivative I (restriction π U hU) X v) =
      smoothLieDerivative I π X (smoothInclusion π U hU I v) := by
  apply Subtype.ext
  exact (lieDerivative_coe π U hU I X v.property).symm

omit [CompleteSpace U] in
/-- Inclusion commutes with every genuine word of derived operators. -/
theorem smoothInclusion_smoothIteratedLieDerivative (Xs : List 𝔤)
    (v : smoothVectors I (restriction π U hU)) :
    smoothInclusion π U hU I (smoothIteratedLieDerivative I (restriction π U hU) Xs v) =
      smoothIteratedLieDerivative I π Xs (smoothInclusion π U hU I v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      change smoothInclusion π U hU I
        (smoothLieDerivative I (restriction π U hU) X
          (smoothIteratedLieDerivative I (restriction π U hU) Xs v)) =
        smoothLieDerivative I π X
          (smoothIteratedLieDerivative I π Xs (smoothInclusion π U hU I v))
      rw [smoothInclusion_smoothLieDerivative, ih]

omit [CompleteSpace U] in
/-- Every genuine ambient word derivative is the inclusion of the restricted derivative. -/
theorem iteratedLieDerivative_coe (Xs : List 𝔤)
    (v : smoothVectors I (restriction π U hU)) :
    iteratedLieDerivative I π Xs (smoothInclusion π U hU I v) =
      (↑(iteratedLieDerivative I (restriction π U hU) Xs v : U) : E) := by
  have h := congrArg (fun w : smoothVectors I π => (w : E))
    (smoothInclusion_smoothIteratedLieDerivative π U hU I Xs v)
  simpa only [smoothInclusion_apply, smoothIteratedLieDerivative_apply] using h.symm

omit [CompleteSpace U] in
/-- Inclusion preserves each genuine word seminorm exactly. -/
theorem wordSeminorm_smoothInclusion (Xs : List 𝔤)
    (v : smoothVectors I (restriction π U hU)) :
    wordSeminorm I π Xs (smoothInclusion π U hU I v) =
      wordSeminorm I (restriction π U hU) Xs v := by
  rw [wordSeminorm_apply, wordSeminorm_apply, iteratedLieDerivative_coe]
  rfl

omit [CompleteSpace U] in
/-- The linear inclusion on the copies carrying the genuine derivative topologies. -/
def derivativeInclusionLinear :
    DerivativeSmoothVectors I (restriction π U hU) →ₗ[ℂ] DerivativeSmoothVectors I π :=
  (DerivativeSmoothVectors.toSmooth I π).symm.toLinearMap.comp
    ((smoothInclusion π U hU I).comp
      (DerivativeSmoothVectors.toSmooth I (restriction π U hU)).toLinearMap)

omit [CompleteSpace U] [LieGroup I ∞ G] in
@[simp]
theorem toSmooth_derivativeInclusionLinear
    (v : DerivativeSmoothVectors I (restriction π U hU)) :
    DerivativeSmoothVectors.toSmooth I π (derivativeInclusionLinear π U hU I v) =
      smoothInclusion π U hU I
        (DerivativeSmoothVectors.toSmooth I (restriction π U hU) v) := rfl

omit [CompleteSpace U] in
/-- Inclusion acts by subspace inclusion on every derivative coordinate. -/
theorem derivativeCoordinates_derivativeInclusionLinear
    (v : DerivativeSmoothVectors I (restriction π U hU)) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates I π
      (derivativeInclusionLinear π U hU I v) Xs =
      (DerivativeSmoothVectors.derivativeCoordinates I (restriction π U hU) v Xs : E) := by
  simp only [DerivativeSmoothVectors.derivativeCoordinates_apply,
    toSmooth_derivativeInclusionLinear, iteratedLieDerivative_coe]

omit [CompleteSpace U] in
theorem continuous_derivativeInclusionLinear :
    Continuous (derivativeInclusionLinear π U hU I) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun v => DerivativeSmoothVectors.derivativeCoordinates I π
    (derivativeInclusionLinear π U hU I v) Xs)
  simp_rw [derivativeCoordinates_derivativeInclusionLinear]
  exact continuous_subtype_val.comp
    (DerivativeSmoothVectors.derivativeCLM I (restriction π U hU) Xs).continuous

omit [CompleteSpace U] in
/-- Inclusion is continuous for the genuine derivative topologies. -/
def derivativeInclusion :
    DerivativeSmoothVectors I (restriction π U hU) →L[ℂ] DerivativeSmoothVectors I π :=
  ⟨derivativeInclusionLinear π U hU I, continuous_derivativeInclusionLinear π U hU I⟩

omit [CompleteSpace U] in
@[simp]
theorem toSmooth_derivativeInclusion
    (v : DerivativeSmoothVectors I (restriction π U hU)) :
    DerivativeSmoothVectors.toSmooth I π (derivativeInclusion π U hU I v) =
      smoothInclusion π U hU I
        (DerivativeSmoothVectors.toSmooth I (restriction π U hU) v) := rfl

omit [CompleteSpace U] in
/-- The genuine derivative topology on the restriction is the ambient subspace topology. -/
theorem isEmbedding_derivativeInclusion :
    IsEmbedding (derivativeInclusion π U hU I) := by
  have hpi : IsEmbedding (fun f : List 𝔤 → U => fun Xs => (f Xs : E)) :=
    IsEmbedding.piMap fun _ => IsEmbedding.subtypeVal
  have he :
      (DerivativeSmoothVectors.derivativeCoordinates I π) ∘
          (derivativeInclusion π U hU I) =
        (fun f : List 𝔤 → U => fun Xs => (f Xs : E)) ∘
          (DerivativeSmoothVectors.derivativeCoordinates I (restriction π U hU)) := by
    funext v Xs
    exact derivativeCoordinates_derivativeInclusionLinear π U hU I v Xs
  apply (DerivativeSmoothVectors.isEmbedding_derivativeCoordinates I π).of_comp_iff.mp
  rw [he]
  exact hpi.comp
    (DerivativeSmoothVectors.isEmbedding_derivativeCoordinates I (restriction π U hU))

/-- The image consists exactly of ambient genuine smooth vectors whose values lie in U. -/
theorem mem_range_derivativeInclusion (v : DerivativeSmoothVectors I π) :
    v ∈ (derivativeInclusion π U hU I).range ↔
      (DerivativeSmoothVectors.toSmooth I π v : E) ∈ U := by
  constructor
  · rintro ⟨w, rfl⟩
    exact (DerivativeSmoothVectors.toSmooth I (restriction π U hU) w).val.property
  · intro hv
    let w : U := ⟨(DerivativeSmoothVectors.toSmooth I π v : E), hv⟩
    let w' : smoothVectors I (restriction π U hU) :=
      ⟨w, isSmoothVector_of_coe π U hU I
        (DerivativeSmoothVectors.toSmooth I π v).property⟩
    refine ⟨(DerivativeSmoothVectors.toSmooth I (restriction π U hU)).symm w', ?_⟩
    apply (DerivativeSmoothVectors.toSmooth I π).injective
    apply Subtype.ext
    rfl

/-- The complete invariant subspace gives a closed embedding of derivative smooth vectors. -/
theorem isClosedEmbedding_derivativeInclusion :
    IsClosedEmbedding (derivativeInclusion π U hU I) := by
  refine ⟨isEmbedding_derivativeInclusion π U hU I, ?_⟩
  have hrange :
      Set.range (derivativeInclusion π U hU I) =
        (fun v : DerivativeSmoothVectors I π =>
          (DerivativeSmoothVectors.toSmooth I π v : E)) ⁻¹' (U : Set E) := by
    ext v
    exact mem_range_derivativeInclusion π U hU I v
  rw [hrange]
  have hclosed : IsClosed (U : Set E) :=
    (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace U)).isClosed
  exact hclosed.preimage (DerivativeSmoothVectors.derivativeCLM I π []).continuous

omit [CompleteSpace U] in
/-- Ambient derivative smooth vectors with value in the specified subspace. -/
def ambientSmoothSubspace : Submodule ℂ (DerivativeSmoothVectors I π) :=
  U.comap (DerivativeSmoothVectors.derivativeCLM I π []).toLinearMap

omit [CompleteSpace U] in
@[simp]
theorem mem_ambientSmoothSubspace (v : DerivativeSmoothVectors I π) :
    v ∈ ambientSmoothSubspace π U I ↔
      (DerivativeSmoothVectors.toSmooth I π v : E) ∈ U := Iff.rfl

omit [CompleteSpace U] in
/-- For a closed subspace, the ambient smooth vectors valued in it form a closed
subspace for the genuine derivative topology. -/
theorem isClosed_ambientSmoothSubspace (hUc : IsClosed (U : Set E)) :
    IsClosed (ambientSmoothSubspace π U I : Set (DerivativeSmoothVectors I π)) :=
  hUc.preimage (DerivativeSmoothVectors.derivativeCLM I π []).continuous

/-- The range of the inclusion, as a submodule, is exactly the ambient subspace of
smooth vectors whose values lie in `U`. -/
theorem range_derivativeInclusion :
    (derivativeInclusion π U hU I).range = ambientSmoothSubspace π U I := by
  ext v
  rw [mem_ambientSmoothSubspace]
  exact mem_range_derivativeInclusion π U hU I v

/-- The linear identification with ambient smooth vectors valued in U. -/
def derivativeEquivLinear :
    DerivativeSmoothVectors I (restriction π U hU) ≃ₗ[ℂ] ambientSmoothSubspace π U I :=
  LinearEquiv.ofBijective
    ((derivativeInclusion π U hU I).codRestrict (ambientSmoothSubspace π U I)
      (fun v => (mem_range_derivativeInclusion π U hU I _).mp ⟨v, rfl⟩)).toLinearMap
    ⟨fun v w h => (isEmbedding_derivativeInclusion π U hU I).injective
        (congrArg Subtype.val h),
      fun v => by
        obtain ⟨w, hw⟩ := (mem_range_derivativeInclusion π U hU I v).mpr v.property
        exact ⟨w, Subtype.ext hw⟩⟩

@[simp]
theorem derivativeEquivLinear_apply
    (v : DerivativeSmoothVectors I (restriction π U hU)) :
    (derivativeEquivLinear π U hU I v : DerivativeSmoothVectors I π) =
      derivativeInclusion π U hU I v := rfl

/-- The identification with ambient smooth vectors valued in U is a homeomorphism. -/
def derivativeEquiv :
    DerivativeSmoothVectors I (restriction π U hU) ≃L[ℂ] ambientSmoothSubspace π U I where
  toLinearEquiv := derivativeEquivLinear π U hU I
  continuous_toFun := (derivativeInclusion π U hU I).continuous.subtype_mk _
  continuous_invFun := by
    apply (isEmbedding_derivativeInclusion π U hU I).continuous_iff.mpr
    have he :
        (derivativeInclusion π U hU I) ∘ (derivativeEquivLinear π U hU I).symm =
          (Subtype.val : ambientSmoothSubspace π U I → DerivativeSmoothVectors I π) := by
      funext v
      exact congrArg Subtype.val ((derivativeEquivLinear π U hU I).apply_symm_apply v)
    change Continuous
      ((derivativeInclusion π U hU I) ∘ (derivativeEquivLinear π U hU I).symm)
    rw [he]
    exact continuous_subtype_val

@[simp]
theorem coe_derivativeEquiv_apply
    (v : DerivativeSmoothVectors I (restriction π U hU)) :
    (derivativeEquiv π U hU I v : DerivativeSmoothVectors I π) =
      derivativeInclusion π U hU I v := rfl

/-- The inverse identification followed by inclusion is the subspace inclusion. -/
@[simp]
theorem derivativeInclusion_derivativeEquiv_symm_apply (v : ambientSmoothSubspace π U I) :
    derivativeInclusion π U hU I ((derivativeEquiv π U hU I).symm v) = v :=
  congrArg Subtype.val ((derivativeEquiv π U hU I).apply_symm_apply v)

end Langlands.Archimedean.SmoothInvariantSubspace
