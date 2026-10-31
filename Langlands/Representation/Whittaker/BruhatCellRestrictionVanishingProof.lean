import Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement
import Langlands.Group.GL.UpperBruhatTransposeProof
import Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof

/-!
# Vanishing of a one-cell open restriction: proof

A supported distribution on the closed inversion layer of a cell `C_w` descends
through the open cell neighborhood to a distribution on the actual cell. Global
positive Whittaker bi-equivariance and transpose anti-invariance pass to this
descent; the cellwise alternative makes it zero, and so the open restriction is
zero.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis HarmonicAnalysis.Distribution

namespace RelativeCellTransport

universe u v

section Conjugacy

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Scalar covariance passes along a homeomorphism conjugating the two maps. -/
theorem covariance_of_conjugacy (r : X ≃ₜ Y) (a : X ≃ₜ X) (b : Y ≃ₜ Y)
    (h : ∀ x, b (r x) = r (a x)) (D : Distribution X) (c : ℂ)
    (hD : pushforward a D = c • D) :
    pushforward b (pushforward r D) = c • pushforward r D := by
  have he : r.trans b = a.trans r := Homeomorph.ext h
  rw [← pushforward_trans, he, pushforward_trans, hD, map_smul]

end Conjugacy

section Geometry

variable (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] (w : Equiv.Perm (Fin (n + 1)))

/-- The double subtype in supported descent is canonically the actual cell. -/
def relativeCellHomeomorph :
    ((Subtype.val : upperBruhatCellNeighborhood (n + 1) K w →
      GeneralLinear (n + 1) K) ⁻¹'
        upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)) ≃ₜ
      UpperBruhatCell (n + 1) K w := by
  let O := upperBruhatCellNeighborhood (n + 1) K w
  let L := upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)
  let P := (Subtype.val : O → GeneralLinear (n + 1) K) ⁻¹' L
  let fwd : P → UpperBruhatCell (n + 1) K w := fun x =>
    ⟨x.val.val, by
      rw [← upperBruhatCellNeighborhood_inter_layer w]
      exact ⟨x.val.property, x.property⟩⟩
  let rev : UpperBruhatCell (n + 1) K w → P := fun x =>
    ⟨⟨x.val, Or.inl x.property⟩, w, le_rfl, x.property⟩
  refine {
    toFun := fwd
    invFun := rev
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · exact (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem biTranslate_mem_cell (u₁ u₂ : upperUnipotent (n + 1) K)
    {g : GeneralLinear (n + 1) K} (hg : g ∈ upperBruhatCell (n + 1) K w) :
    u₁.val * g * u₂.val ∈ upperBruhatCell (n + 1) K w :=
  mem_upperBruhatCell_mul (n + 1) K w
    (upperUnipotentInUpperTriangular (n + 1) K u₂)
    (mul_mem_upperBruhatCell (n + 1) K w
      (upperUnipotentInUpperTriangular (n + 1) K u₁) hg)

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
theorem biTranslate_mem_neighborhood (u₁ u₂ : upperUnipotent (n + 1) K)
    {g : GeneralLinear (n + 1) K}
    (hg : g ∈ upperBruhatCellNeighborhood (n + 1) K w) :
    u₁.val * g * u₂.val ∈ upperBruhatCellNeighborhood (n + 1) K w := by
  rcases hg with hg | ⟨v, hv, hgv⟩
  · exact Or.inl (biTranslate_mem_cell n K w u₁ u₂ hg)
  · exact Or.inr ⟨v, hv, biTranslate_mem_cell n K v u₁ u₂ hgv⟩

/-- The actual bi-translation restricted to the specified open neighborhood. -/
def neighborhoodBiTranslate (u₁ u₂ : upperUnipotent (n + 1) K) :
    upperBruhatCellNeighborhood (n + 1) K w ≃ₜ
      upperBruhatCellNeighborhood (n + 1) K w where
  toFun g := ⟨u₁.val * g.val * u₂.val,
    biTranslate_mem_neighborhood n K w u₁ u₂ g.property⟩
  invFun g := ⟨u₁.val⁻¹ * g.val * u₂.val⁻¹,
    biTranslate_mem_neighborhood n K w u₁⁻¹ u₂⁻¹ g.property⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

omit [T2Space K] in
theorem transpose_mem_higher {g : GeneralLinear (n + 1) K}
    (hg : g ∈ upperBruhatHigherCells (n + 1) K w) :
    weylTransposeHomeomorph n K g ∈ upperBruhatHigherCells (n + 1) K w := by
  obtain ⟨v, hv, hgv⟩ := hg
  refine ⟨upperBruhatTransposeIndex (n + 1) v, ?_, ?_⟩
  · rwa [permutationInversionCount_upperBruhatTransposeIndex]
  · exact weylConjugateTranspose_image_upperBruhatCell_subset (n + 1) K v
      ⟨g, hgv, rfl⟩

variable (hτ : Set.MapsTo (weylTransposeHomeomorph n K)
  (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w))

include hτ in
omit [T2Space K] in
theorem transpose_mem_neighborhood {g : GeneralLinear (n + 1) K}
    (hg : g ∈ upperBruhatCellNeighborhood (n + 1) K w) :
    weylTransposeHomeomorph n K g ∈ upperBruhatCellNeighborhood (n + 1) K w := by
  rcases hg with hg | hg
  · exact Or.inl (hτ hg)
  · exact Or.inr (transpose_mem_higher n K w hg)

/-- Restrict the actual transpose to this neighborhood when the cell is stable. -/
def neighborhoodWeylTranspose :
    upperBruhatCellNeighborhood (n + 1) K w ≃ₜ
      upperBruhatCellNeighborhood (n + 1) K w where
  toFun g := ⟨weylTransposeHomeomorph n K g.val,
    transpose_mem_neighborhood n K w hτ g.property⟩
  invFun g := ⟨weylTransposeHomeomorph n K g.val,
    transpose_mem_neighborhood n K w hτ g.property⟩
  left_inv g := Subtype.ext (weylTransposeHomeomorph_involutive n K g.val)
  right_inv g := Subtype.ext (weylTransposeHomeomorph_involutive n K g.val)
  continuous_toFun :=
    ((weylTransposeHomeomorph n K).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((weylTransposeHomeomorph n K).continuous.comp continuous_subtype_val).subtype_mk _

end Geometry

section Distributions

variable (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]
  [LocallyCompactSpace (GeneralLinear (n + 1) K)]
  [TotallyDisconnectedSpace (GeneralLinear (n + 1) K)]
  (w : Equiv.Perm (Fin (n + 1)))

/-- Actual relative supported descent, transported to the actual cell subtype. -/
def descendToCell
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w))) :
    Distribution (UpperBruhatCell (n + 1) K w) :=
  pushforward (relativeCellHomeomorph n K w)
    (descendInOpen (isOpen_upperBruhatCellNeighborhood w)
      ((isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val) D)

theorem biEquivariant_descendToCell (ψ : UnitaryAdditiveCharacter K)
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)))
    (hD : IsBiEquivariantDistribution ψ n (D : Distribution (GeneralLinear (n + 1) K))) :
    IsBiEquivariantBruhatCellDistribution n K w ψ (descendToCell n K w D) := by
  intro u₁ u₂ f
  let r := relativeCellHomeomorph n K w
  let e := (Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)
  let eU := neighborhoodBiTranslate n K w u₁ u₂
  let b := bruhatCellBiTranslate n K w u₁ u₂
  let eZ := r.trans (b.trans r.symm)
  let c := (standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)
  have hglobal : pushforward e (D : Distribution (GeneralLinear (n + 1) K)) =
      c • (D : Distribution (GeneralLinear (n + 1) K)) := by
    ext φ
    exact (isBiEquivariantDistribution_iff n K ψ _).mp hD u₁ u₂ φ
  have hcov := supportedDescentCovariance
    (GeneralLinear (n + 1) K) _ _ (isOpen_upperBruhatCellNeighborhood w)
    ((isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val) D
    e eU eZ c (fun _ => rfl) (fun _ => rfl) hglobal
  have hcell := covariance_of_conjugacy r eZ b (by
    intro x
    exact (r.apply_symm_apply (b (r x))).symm) _ c hcov
  exact congrArg (fun T : Distribution (UpperBruhatCell (n + 1) K w) => T f) hcell

theorem antiInvariant_descendToCell
    (hτ : Set.MapsTo (weylTransposeHomeomorph n K)
      (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w))
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)))
    (hD : pushforward (weylTransposeHomeomorph n K)
      (D : Distribution (GeneralLinear (n + 1) K)) =
        -(D : Distribution (GeneralLinear (n + 1) K))) :
    pushforward (bruhatCellWeylTranspose n K w hτ) (descendToCell n K w D) =
      -descendToCell n K w D := by
  let r := relativeCellHomeomorph n K w
  let eU := neighborhoodWeylTranspose n K w hτ
  let b := bruhatCellWeylTranspose n K w hτ
  let eZ := r.trans (b.trans r.symm)
  have hglobal : pushforward (weylTransposeHomeomorph n K)
      (D : Distribution (GeneralLinear (n + 1) K)) =
        (-1 : ℂ) • (D : Distribution (GeneralLinear (n + 1) K)) := by
    simpa only [neg_one_smul] using hD
  have hcov := supportedDescentCovariance
    (GeneralLinear (n + 1) K) _ _ (isOpen_upperBruhatCellNeighborhood w)
    ((isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val) D
    (weylTransposeHomeomorph n K) eU eZ (-1) (fun _ => rfl) (fun _ => rfl) hglobal
  have hcell := covariance_of_conjugacy r eZ b (by
    intro x
    exact (r.apply_symm_apply (b (r x))).symm) _ (-1) hcov
  simpa only [neg_one_smul, descendToCell, r, b] using hcell

theorem restrictOpen_zero_of_descendToCell_zero
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)))
    (hD : descendToCell n K w D = 0) :
    restrictOpen (isOpen_upperBruhatCellNeighborhood w)
      (D : Distribution (GeneralLinear (n + 1) K)) = 0 := by
  have hz : descendInOpen (isOpen_upperBruhatCellNeighborhood w)
      ((isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val) D = 0 :=
    (pushforward (relativeCellHomeomorph n K w)).injective (by
      simpa only [map_zero, descendToCell] using hD)
  rw [← closedPushforward_descendInOpen
    (isOpen_upperBruhatCellNeighborhood w)
    ((isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val) D, hz, map_zero]

/-- Either cellwise vanishing, or stable cellwise invariance, kills the open
restriction of a globally anti-invariant bi-equivariant supported distribution. -/
theorem restriction_zero_of_cellwise (ψ : UnitaryAdditiveCharacter K)
    (D : supportedOn
      (upperBruhatLayerLE (n + 1) K (permutationInversionCount (n + 1) w)))
    (hD : IsBiEquivariantDistribution ψ n (D : Distribution (GeneralLinear (n + 1) K)))
    (hanti : pushforward (weylTransposeHomeomorph n K)
      (D : Distribution (GeneralLinear (n + 1) K)) =
        -(D : Distribution (GeneralLinear (n + 1) K)))
    (hcell :
      (∀ E : Distribution (UpperBruhatCell (n + 1) K w),
        IsBiEquivariantBruhatCellDistribution n K w ψ E → E = 0) ∨
      ∃ hτ : Set.MapsTo (weylTransposeHomeomorph n K)
        (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w),
        ∀ E : Distribution (UpperBruhatCell (n + 1) K w),
          IsBiEquivariantBruhatCellDistribution n K w ψ E →
            IsWeylTransposeInvariantBruhatCellDistribution n K w hτ E) :
    restrictOpen (isOpen_upperBruhatCellNeighborhood w)
      (D : Distribution (GeneralLinear (n + 1) K)) = 0 := by
  apply restrictOpen_zero_of_descendToCell_zero
  have hbi := biEquivariant_descendToCell n K w ψ D hD
  rcases hcell with hzero | ⟨hτ, hinv⟩
  · exact hzero _ hbi
  · have hfixed := hinv _ hbi
    have hneg := antiInvariant_descendToCell n K w hτ D hanti
    ext f
    exact CharZero.eq_neg_self_iff.mp
      (congrArg (fun E : Distribution (UpperBruhatCell (n + 1) K w) => E f)
        (hfixed.symm.trans hneg))

end Distributions

end RelativeCellTransport

universe u

/-- The one-cell transport: under global positive Whittaker bi-equivariance,
Weyl-transpose anti-invariance and the cellwise alternative, the restriction
of a supported distribution to the specified open cell neighborhood is zero. -/
theorem bruhatCellRestrictionVanishing : BruhatCellRestrictionVanishingStatement.{u} := by
  intro n K _ _ _ _ _ _ w ψ D hD hanti hcell
  exact RelativeCellTransport.restriction_zero_of_cellwise n K w ψ D hD hanti hcell

end Langlands.Whittaker
