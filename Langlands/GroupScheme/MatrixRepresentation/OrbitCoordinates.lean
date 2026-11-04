import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates

/-! # Split coordinates selected from a rational orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- Split coordinates for a span can be selected from its generators, retaining
any specified nonzero generator as a column. -/
theorem exists_selected_split_coordinates (t : Set (n → k))
    (v : n → k) (hv : v ∈ t) (hv0 : v ≠ 0) :
    ∃ (d : ℕ) (B : Matrix n (Fin d) k) (C : Matrix (Fin d) n k),
      C * B = 1 ∧
      (∀ s, (fun r => B r s) ∈ t) ∧
      (∀ w, w ∈ Submodule.span k t → (B * C) *ᵥ w = w) ∧
      ∃ s, (fun r => B r s) = v := by
  classical
  let W := Submodule.span k t
  let v' : W := ⟨v, Submodule.subset_span hv⟩
  let t' : Set W := Subtype.val ⁻¹' t
  have hv' : v' ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  have hs : LinearIndepOn k id ({v'} : Set W) :=
    (linearIndepOn_singleton_iff k).mpr hv'
  have hst : ({v'} : Set W) ⊆ t' := by
    rw [Set.singleton_subset_iff]
    exact hv
  have ht : ⊤ ≤ Submodule.span k t' := by
    change ⊤ ≤ Submodule.span k (Subtype.val ⁻¹' t)
    rw [Submodule.span_span_coe_preimage]
  let b₀ := Basis.extendLe hs hst ht
  let := FiniteDimensional.fintypeBasisIndex b₀
  let d := Fintype.card (hs.extend hst)
  let b : Module.Basis (Fin d) k W := b₀.reindex (Fintype.equivFin _)
  have hbt : ∀ s, (b s : n → k) ∈ t := by
    intro s
    have hb := Basis.extendLe_subset hs hst ht
    exact hb ⟨_, (Basis.reindex_apply _ _ _).symm⟩
  have hbv : v' ∈ Set.range b := by
    dsimp only [b]
    rw [Basis.range_reindex]
    exact Basis.subset_extendLe hs hst ht (Set.mem_singleton v')
  obtain ⟨p, hp⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let f : (Fin d → k) →ₗ[k] (n → k) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  let r : (n → k) →ₗ[k] (Fin d → k) :=
    b.equivFun.toLinearMap.comp p
  have hrf : r.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change b.equivFun (p (W.subtype (b.equivFun.symm x))) = x
    have h := LinearMap.congr_fun hp (b.equivFun.symm x)
    change p (W.subtype (b.equivFun.symm x)) = b.equivFun.symm x at h
    rw [h, b.equivFun.apply_symm_apply]
  have hcol : ∀ s, f (Pi.single s 1) = (b s : n → k) := by
    intro s
    change (b.equivFun.symm (Pi.single s 1) : n → k) = _
    simp
  refine ⟨d, LinearMap.toMatrix' f, LinearMap.toMatrix' r, ?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hrf, LinearMap.toMatrix'_id]
  · intro s
    change f (Pi.single s 1) ∈ t
    rw [hcol]
    exact hbt s
  · intro w hw
    rw [← LinearMap.toMatrix'_comp, LinearMap.toMatrix'_mulVec]
    change W.subtype (b.equivFun.symm (b.equivFun (p w))) = w
    rw [b.equivFun.symm_apply_apply]
    exact congrArg Subtype.val (LinearMap.congr_fun hp (⟨w, hw⟩ : W))
  · obtain ⟨s, hs⟩ := hbv
    refine ⟨s, ?_⟩
    change f (Pi.single s 1) = v
    rw [hcol]
    exact congrArg Subtype.val hs

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The base-field span of a coordinate vector's rational orbit. -/
def rationalOrbitSpan (ρ : MatrixRepresentation G n) (j : n) :
    Submodule k (n → k) :=
  Submodule.span k (Set.range fun g =>
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1)

/-- Rational matrices preserve the rational orbit span. -/
theorem rationalMatrix_mem_orbitSpan (ρ : MatrixRepresentation G n) (j : n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    {v : n → k} (hv : v ∈ ρ.rationalOrbitSpan j) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ ρ.rationalOrbitSpan j := by
  have hle : ρ.rationalOrbitSpan j ≤
      (ρ.rationalOrbitSpan j).comap (Matrix.toLin' (ρ.rationalMatrix g : Matrix n n k)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g', rfl⟩
    change (ρ.rationalMatrix g : Matrix n n k) *ᵥ
      ((ρ.rationalMatrix g' : Matrix n n k) *ᵥ Pi.single j 1) ∈
        ρ.rationalOrbitSpan j
    rw [Matrix.mulVec_mulVec]
    apply Submodule.subset_span
    refine ⟨g * g', ?_⟩
    change (ρ.rationalMatrix (g * g') : Matrix n n k) *ᵥ Pi.single j 1 = _
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact hle hv

/-- A rational orbit admits finite split coordinates, including the original
coordinate vector, which are invariant on all scheme tests. -/
theorem exists_rationalOrbit_coordinates
    [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    (ρ : MatrixRepresentation G n) (j : n) :
    ∃ (d : ℕ) (B : Matrix n (Fin d) k) (C : Matrix (Fin d) n k),
      C * B = 1 ∧
      (∀ s, ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        (fun r => B r s) =
          (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1) ∧
      ρ.IsStableCoordinates B C ∧
      ∃ s, (fun r => B r s) = Pi.single j 1 := by
  classical
  let t : Set (n → k) := Set.range fun g =>
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ Pi.single j 1
  have he : Pi.single j (1 : k) ∈ t := by
    refine ⟨1, ?_⟩
    change (ρ.rationalMatrix 1 : Matrix n n k) *ᵥ Pi.single j 1 = _
    rw [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have he0 : (Pi.single j (1 : k) : n → k) ≠ 0 :=
    Pi.single_ne_zero_iff.mpr one_ne_zero
  obtain ⟨d, B, C, hCB, hcols, hproj, hs⟩ :=
    exists_selected_split_coordinates t (Pi.single j 1) he he0
  refine ⟨d, B, C, hCB, ?_, ?_, hs⟩
  · intro s
    obtain ⟨g, hg⟩ := hcols s
    exact ⟨g, hg.symm⟩
  · apply isStableCoordinates_of_rationalMatrix
    intro g
    apply Matrix.ext_of_mulVec_single
    intro s
    have hmem : (fun r => B r s) ∈ ρ.rationalOrbitSpan j :=
      Submodule.subset_span (hcols s)
    have h := hproj _ (ρ.rationalMatrix_mem_orbitSpan j g hmem)
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one] at h ⊢
    exact h.symm

end Langlands.GroupScheme.MatrixRepresentation
