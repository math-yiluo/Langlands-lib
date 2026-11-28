import Langlands.BaseChange.TwistedJacquet
import Langlands.BaseChange.TwistedLocalDescent.LocalHelpers
import Langlands.Representation.Geometric.ParabolicOrbitMeasureData

/-! Entrywise field action on the subgroups and maps of a parabolic orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BaseChange

open GeneralLinear Geometric QuotientIntegration TwistedLocalDescent

universe u v

section Algebraic

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]
  (σ : E ≃ₐ[F] E) {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The entrywise action commutes with the target Levi section. -/
theorem parabolicAut_leviInParabolic (m : C.Levi E) :
    parabolicAut σ C (C.leviInParabolic E m) = C.leviInParabolic E (leviAut σ C m) :=
  Subtype.ext (entrywiseAut_leviEmbedding σ C m)

variable (hw : entrywiseAut σ n (permutation n E w) = permutation n E w)

include hw

/-- A fixed representative gives an invariant orbit stabilizer. -/
theorem parabolicAut_mem_orbitStabilizer_iff (q : C.parabolic E) :
    parabolicAut σ C q ∈ parabolicOrbitStabilizer E B C w ↔
      q ∈ parabolicOrbitStabilizer E B C w := by
  change (permutation n E w)⁻¹ * entrywiseAut σ n q * ((permutation n E w)⁻¹)⁻¹ ∈
    B.parabolic E ↔ (permutation n E w)⁻¹ * q.val * ((permutation n E w)⁻¹)⁻¹ ∈ B.parabolic E
  simpa only [map_mul, map_inv, hw] using
    entrywiseAut_mem_parabolic_iff σ B
      ((permutation n E w)⁻¹ * q.val * ((permutation n E w)⁻¹)⁻¹)

/-- The same entrywise action preserves the target intersection on the Levi. -/
theorem leviAut_mem_parabolicOrbitStagesQuotient_iff (m : C.Levi E) :
    leviAut σ C m ∈ parabolicOrbitStagesQuotient E B C w ↔
      m ∈ parabolicOrbitStagesQuotient E B C w := by
  have h : parabolicOrbitStagesQuotient E B C w =
      (parabolicOrbitStabilizer E B C w).comap (C.leviInParabolic E) := by
    rw [parabolicOrbitStagesQuotient, parabolicOrbitStages_comap_section,
      parabolicOrbitStabilizer_comap_section]
  rw [h]
  change C.leviInParabolic E (leviAut σ C m) ∈ parabolicOrbitStabilizer E B C w ↔
    C.leviInParabolic E m ∈ parabolicOrbitStabilizer E B C w
  rw [← parabolicAut_leviInParabolic]
  exact parabolicAut_mem_orbitStabilizer_iff σ B C w hw _

/-- The inducing coefficient map commutes with the source Levi automorphism. -/
theorem parabolicOrbitToSourceLevi_parabolicAut (q : parabolicOrbitStabilizer E B C w) :
    parabolicOrbitToSourceLevi E B C w
        ⟨parabolicAut σ C q, (parabolicAut_mem_orbitStabilizer_iff σ B C w hw q).2 q.property⟩ =
      leviAut σ B (parabolicOrbitToSourceLevi E B C w q) := by
  let c := stabilizerToInducing (B.parabolic E) (C.parabolic E) (permutation n E w)
  have hc :
      c ⟨parabolicAut σ C q, (parabolicAut_mem_orbitStabilizer_iff σ B C w hw q).2 q.property⟩ =
        parabolicAut σ B (c q) := by
    apply Subtype.ext
    change (permutation n E w)⁻¹ * entrywiseAut σ n q.val * ((permutation n E w)⁻¹)⁻¹ =
      entrywiseAut σ n ((permutation n E w)⁻¹ * q.val.val * ((permutation n E w)⁻¹)⁻¹)
    simp only [map_mul, map_inv, hw]
  change B.leviProjection E (c _) = leviAut σ B (B.leviProjection E (c q))
  rw [hc, leviProjection_parabolicAut]

end Algebraic

section Topological

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Transport the entrywise radical automorphism to the actual nested kernel. -/
def parabolicOrbitNestedKernelAut :
    (parabolicOrbitStagesRetraction E B C w).ker ≃ₜ*
      (parabolicOrbitStagesRetraction E B C w).ker :=
  let e := parabolicOrbitNestedRadicalEquiv E B C w
  e.trans ((subgroupAutomorphism (C.unipotentRadical E) (parabolicContinuousAut C σ)
    (parabolicAut_mem_unipotentRadical_iff σ C)).trans e.symm)

@[simp]
theorem parabolicOrbitNestedKernelAut_val (x : (parabolicOrbitStagesRetraction E B C w).ker) :
    (parabolicOrbitNestedKernelAut σ B C w x).val.val = parabolicContinuousAut C σ x.val.val :=
  rfl

@[simp]
theorem parabolicOrbitNestedKernelAut_symm_val (x : (parabolicOrbitStagesRetraction E B C w).ker) :
    ((parabolicOrbitNestedKernelAut σ B C w).symm x).val.val =
      (parabolicContinuousAut C σ).symm x.val.val := by
  apply (parabolicContinuousAut C σ).injective
  rw [ContinuousMulEquiv.apply_symm_apply, ← parabolicOrbitNestedKernelAut_val σ B C w,
    ContinuousMulEquiv.apply_symm_apply]

/-- Preservation of the actual nested intersection for a fixed representative. -/
def ParabolicOrbitNestedIntersectionStable : Prop :=
  ∀ x : (parabolicOrbitStagesRetraction E B C w).ker,
    parabolicOrbitNestedKernelAut σ B C w x ∈ parabolicOrbitNestedIntersection E B C w ↔
      x ∈ parabolicOrbitNestedIntersection E B C w

theorem parabolicOrbitNestedIntersectionStable
    (hw : entrywiseAut σ n (permutation n E w) = permutation n E w) :
    ParabolicOrbitNestedIntersectionStable σ B C w := by
  intro x
  exact parabolicAut_mem_orbitStabilizer_iff σ B C w hw x.val.val

end Topological

end Langlands.BaseChange
