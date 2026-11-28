import Langlands.BaseChange.TwistedJacquet
import Langlands.BaseChange.TwistedLeviInductionTransferProof
import Langlands.Representation.Aubert.RefinementCuts
import Langlands.Representation.Geometric.ProductLeviSupportCut

/-!
# Relative Jacquet modules of Levi products and their σ-intertwiners

For block shapes `C` refining `B` of `n`, the relative parabolic `relParabolic E B C` of the
Levi product `B.Levi E` has the Levi projection `relProjection E B C` onto `C.Levi E`, split by
the block diagonal section `relLeviSection`. This module defines the unnormalized relative
Jacquet module: the coinvariants of the restriction to `relParabolic E B C` by the kernel of
`relProjection E B C`, on which `C.Levi E` acts through `relLeviSection`. An intertwiner `A`
of a representation `ρ` of `B.Levi E` with `ρ ∘ σ` descends by `[x] ↦ [A x]` to an
intertwiner of the relative Jacquet module with its composite with `σ`
(Rogawski 1988, §3). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear Geometric

universe u v z

section Section

variable {E : Type v} [CommRing E] [Nontrivial E] {n : ℕ} {B C : BlockShape n}

/-- Inclusion of the standard parabolics over a nontrivial coefficient ring forces the
coarse cuts to be among the fine cuts. -/
theorem cuts_subset_of_parabolic_le (hCB : C.parabolic E ≤ B.parabolic E) : B.cuts ⊆ C.cuts := by
  apply (blockWeyl_le_iff_cuts_subset B C).mp
  intro w hw
  exact (permutation_mem_parabolic_iff E B w).mp
    (hCB ((permutation_mem_parabolic_iff E C w).mpr hw))

/-- The fine block diagonal matrix subgroup lies in the coarse block diagonal matrix
subgroup. -/
theorem leviSubgroup_le_of_parabolic_le (hCB : C.parabolic E ≤ B.parabolic E) :
    C.leviSubgroup E ≤ B.leviSubgroup E := by
  obtain ⟨Q, rfl⟩ := Aubert.exists_refinement_of_cuts_subset B C (cuts_subset_of_parabolic_le hCB)
  rintro _ ⟨m, rfl⟩
  exact ⟨(flattenedLeviEquiv E B Q m).val, flattenedLeviEquiv_embedding E B Q m⟩

end Section

section Field

variable {E : Type v} [Field E] {n : ℕ} {B C : BlockShape n}

/-- The section `relLeviSection` is the block diagonal inclusion: the block diagonal matrix of
its value is the fine block diagonal matrix. -/
@[simp]
theorem relLeviSection_embedding (hCB : C.parabolic E ≤ B.parabolic E) (m : C.Levi E) :
    B.leviEmbedding E (relLeviSection hCB m) = C.leviEmbedding E m := by
  obtain ⟨m', hm'⟩ := leviSubgroup_le_of_parabolic_le hCB ⟨m, rfl⟩
  have hp : Subgroup.inclusion hCB (C.leviInParabolic E m) = B.leviInParabolic E m' :=
    Subtype.ext hm'.symm
  change B.leviEmbedding E
      (B.leviProjection E (Subgroup.inclusion hCB (C.leviInParabolic E m))) = _
  rw [hp, BlockShape.leviProjection_section, hm']

end Field

section Jacquet

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]
  {n : ℕ} (σ : E ≃ₐ[F] E) (B C : BlockShape n)

/-- Restrict the entrywise action of `σ` to the relative parabolic. -/
def relParabolicAut : relParabolic E B C ≃* relParabolic E B C where
  toFun p := ⟨leviAut σ B p, (leviAut_mem_relParabolic_iff σ B C p).2 p.2⟩
  invFun p := ⟨leviAut σ.symm B p, (leviAut_mem_relParabolic_iff σ.symm B C p).2 p.2⟩
  left_inv p := Subtype.ext ((leviAut σ B).symm_apply_apply (p : B.Levi E))
  right_inv p := Subtype.ext ((leviAut σ B).apply_symm_apply (p : B.Levi E))
  map_mul' p q := Subtype.ext (map_mul (leviAut σ B) (p : B.Levi E) q)

/-- The entrywise action of `σ` preserves the kernel of the relative Levi projection. -/
theorem relParabolicAut_mem_ker_iff (p : relParabolic E B C) :
    relParabolicAut σ B C p ∈ (relProjection E B C).ker ↔
      p ∈ (relProjection E B C).ker := by
  change relProjection E B C ⟨leviAut σ B p, _⟩ = 1 ↔ relProjection E B C p = 1
  rw [relProjection_leviAut]
  exact (leviAut σ C).map_eq_one_iff

variable {B} {W : Type z} [AddCommGroup W] [Module ℂ W]

/-- The coinvariants of the restriction of `ρ` to the relative parabolic by the kernel of the
relative Levi projection. -/
abbrev RelJacquetModule (ρ : Representation ℂ (B.Levi E) W) :=
  Jacquet.Coinvariants (ρ.comp (relParabolic E B C).subtype) (relProjection E B C).ker

/-- The quotient map from the ambient representation space to its relative coinvariants. -/
abbrev relJacquetMk (ρ : Representation ℂ (B.Levi E) W) : W →ₗ[ℂ] RelJacquetModule C ρ :=
  Jacquet.mk (ρ.comp (relParabolic E B C).subtype) (relProjection E B C).ker

end Jacquet

section FieldJacquet

variable {F : Type u} [CommRing F] {E : Type v} [Field E] [Algebra F E]
  {n : ℕ} (σ : E ≃ₐ[F] E) {B C : BlockShape n} (hCB : C.parabolic E ≤ B.parabolic E)

/-- The entrywise action of `σ` commutes with the block diagonal section. -/
theorem relParabolicAut_relLeviSection (m : C.Levi E) :
    relParabolicAut σ B C (relLeviSection hCB m) = relLeviSection hCB (leviAut σ C m) := by
  apply Subtype.ext
  apply (B.leviEmbedding_injective E)
  change B.leviEmbedding E (leviAut σ B (relLeviSection hCB m)) =
    B.leviEmbedding E (relLeviSection hCB (leviAut σ C m))
  rw [← entrywiseAut_leviEmbedding, relLeviSection_embedding, relLeviSection_embedding,
    entrywiseAut_leviEmbedding]

variable {W : Type z} [AddCommGroup W] [Module ℂ W]

/-- The unnormalized relative Jacquet module: `C.Levi E` acts on the relative coinvariants
through the block diagonal section `relLeviSection`. -/
def relJacquet (ρ : Representation ℂ (B.Levi E) W) :
    Representation ℂ (C.Levi E) (RelJacquetModule C ρ) :=
  (Representation.toCoinvariants (ρ.comp (relParabolic E B C).subtype)
    (relProjection E B C).ker).comp (relLeviSection hCB)

@[simp]
theorem relJacquet_mk (ρ : Representation ℂ (B.Levi E) W) (m : C.Levi E) (x : W) :
    relJacquet hCB ρ m (relJacquetMk C ρ x) =
      relJacquetMk C ρ (ρ (relLeviSection hCB m) x) := rfl

/-- The σ-intertwiner of the unnormalized relative Jacquet module descended from an
intertwiner `A` of `ρ` with `ρ ∘ σ` by `[x] ↦ [A x]`. -/
def relJacquetSigmaIntertwiner {ρ : Representation ℂ (B.Levi E) W}
    (A : ρ.Equiv (ρ.comp (leviAut σ B).toMonoidHom)) :
    (relJacquet hCB ρ).Equiv ((relJacquet hCB ρ).comp (leviAut σ C).toMonoidHom) :=
  Representation.Equiv.mk
    (Jacquet.twistedCoinvariantsEquiv (ρ.comp (relParabolic E B C).subtype)
      (relProjection E B C).ker (relParabolicAut σ B C) (relParabolicAut_mem_ker_iff σ B C)
      A.toLinearEquiv (fun p x => A.toIntertwiningMap.isIntertwining _ _ p.val x))
    (by
      intro m
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := Jacquet.mk_surjective (ρ.comp (relParabolic E B C).subtype)
        (relProjection E B C).ker q
      change relJacquetMk C ρ (A (ρ (relLeviSection hCB m) x)) =
        relJacquetMk C ρ (ρ (relLeviSection hCB (leviAut σ C m)) (A x))
      rw [← relParabolicAut_relLeviSection σ hCB]
      exact congrArg (relJacquetMk C ρ)
        (A.toIntertwiningMap.isIntertwining _ _ (relLeviSection hCB m).val x))

@[simp]
theorem relJacquetSigmaIntertwiner_mk {ρ : Representation ℂ (B.Levi E) W}
    (A : ρ.Equiv (ρ.comp (leviAut σ B).toMonoidHom)) (x : W) :
    relJacquetSigmaIntertwiner σ hCB A (relJacquetMk C ρ x) = relJacquetMk C ρ (A x) := rfl

end FieldJacquet

end Langlands.BaseChange.TwistedLeviPaleyWiener
