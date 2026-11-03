import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionProof
import Langlands.GroupScheme.Rational.PointedTensorPullback
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.TorusUnipotence.MatrixCoefficients

/-! # The character grading of the coordinate algebra of a group with a torus action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusUnipotence

section Tensor

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B]

/-- Let `W` be an independent family of subspaces of `B ⊗ B` such that `𝒜 α ⊗ 𝒜 β` lies in
`W (α + β)`, where the `𝒜 χ` span `B`. Then `W χ` lies in `∑ α, 𝒜 α ⊗ 𝒜 (χ - α)`. -/
theorem le_iSup_map₂_of_iSupIndep {Γ : Type*} [AddCommGroup Γ] (𝒜 : Γ → Submodule K B)
    (h𝒜 : ⨆ χ, 𝒜 χ = ⊤) (W : Γ → Submodule K (B ⊗[K] B)) (hW : iSupIndep W)
    (hmul : ∀ α β, ∀ x ∈ 𝒜 α, ∀ y ∈ 𝒜 β, x ⊗ₜ[K] y ∈ W (α + β)) (χ : Γ) :
    W χ ≤ ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α)) := by
  let V : Γ → Submodule K (B ⊗[K] B) := fun ψ =>
    ⨆ α, Submodule.map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (ψ - α))
  have hle : V ≤ W := fun ψ => iSup_le fun α => Submodule.map₂_le.2 fun x hx y hy => by
    have h := hmul α (ψ - α) x hx y hy
    rwa [add_sub_cancel] at h
  have htop : iSup V = ⊤ := by
    rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    have hx : x ∈ ⨆ χ, 𝒜 χ := h𝒜 ▸ Submodule.mem_top
    have hy : y ∈ ⨆ χ, 𝒜 χ := h𝒜 ▸ Submodule.mem_top
    refine Submodule.iSup_induction 𝒜 (motive := fun x => x ⊗ₜ[K] y ∈ iSup V) hx ?_ ?_ ?_
    · intro α x hx
      refine Submodule.iSup_induction 𝒜 (motive := fun y => x ⊗ₜ[K] y ∈ iSup V) hy ?_ ?_ ?_
      · intro β y hy
        refine Submodule.mem_iSup_of_mem (α + β) (Submodule.mem_iSup_of_mem α ?_)
        refine Submodule.apply_mem_map₂ _ hx ?_
        rwa [add_sub_cancel_left]
      · rw [TensorProduct.tmul_zero]
        exact zero_mem _
      · intro y y' h h'
        rw [TensorProduct.tmul_add]
        exact add_mem h h'
    · rw [TensorProduct.zero_tmul]
      exact zero_mem _
    · intro x x' h h'
      rw [TensorProduct.add_tmul]
      exact add_mem h h'
  exact (congrFun ((hW.le_iff_eq_of_iSup_eq_top htop).mp hle) χ).ge

end Tensor

section Group

open PointedCoordinateWeights

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "A" => CharacterUnits.Coord H

omit [IsAffineHom H.X.hom] in
/-- Multiplication `H × H → H` is equivariant for the diagonal action and preserves the
identity. -/
theorem mul_isPointedEquivariant (b : AutomorphicAction S.toGrp H) :
    IsPointedEquivariant ((PointedAction.ofGroup b).prod (PointedAction.ofGroup b))
      (PointedAction.ofGroup b) μ[H.X] := by
  refine ⟨fun T s v => ?_, ?_⟩
  · have hv : ((PointedAction.ofGroup b).prod (PointedAction.ofGroup b)).act s v =
        lift (b.act s (v ≫ fst _ _)) (b.act s (v ≫ snd _ _)) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hv, PointedAction.ofGroup_act, ← Hom.mul_def, ← b.act_mul_right, Hom.mul_def,
      lift_comp_fst_snd]
  · change lift η[H.X] η[H.X] ≫ μ[H.X] = η[H.X]
    have h := mul_one (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
    simpa [Hom.mul_def, Hom.one_def] using h

/-- The pullback along multiplication, in tensor coordinates, is the comultiplication. -/
theorem tensorPullback_mul :
    tensorPullback (V := H.X) (W := H.X) μ[H.X] = coordComul H := by
  rw [tensorPullback, tensorCoordinates_toAlgHom, ← PointedCoordinateWeights.coordinates_comp,
    tensorPresentation_hom, ← Hom.mul_def]
  rfl

/-- The constant function `1` has weight `0`. -/
theorem one_mem_weightSpace_zero (b : AutomorphicAction S.toGrp H) :
    (1 : A) ∈ CoordinateWeights.weightSpace b 0 := by
  intro R _ _ s g
  rw [map_one, map_one, Lie.characterValue_zero, Units.val_one, one_mul]

/-- The comultiplication is graded: it maps the `χ`-space into `∑ α, A_α ⊗ A_{χ - α}`. -/
theorem coordComul_mem_iSup (b : AutomorphicAction S.toGrp H) (hS : IsSplitTorus S.toGrp)
    {χ : characterLattice S} {f : A} (hf : f ∈ CoordinateWeights.weightSpace b χ) :
    coordComul H f ∈
      ⨆ α, Submodule.map₂ (TensorProduct.mk k A A) (CoordinateWeights.weightSpace b α)
        (CoordinateWeights.weightSpace b (χ - α)) := by
  classical
  let a := PointedAction.ofGroup b
  have hA : DirectSum.IsInternal (CoordinateWeights.weightSpace b) :=
    (CoordinateWeights.coordinateWeightDecomposition k H inferInstance S hS b).1
  have hprod : DirectSum.IsInternal (PointedCoordinateWeights.weightSpace (a.prod a)) :=
    (pointedCoordinateDecomposition k S hS (H.X ⊗ H.X) (a.prod a)).1
  have hmem := tensorPullback_mem_tensorWeightSpace a a a μ[H.X] (mul_isPointedEquivariant b) hf
  rw [tensorPullback_mul] at hmem
  exact le_iSup_map₂_of_iSupIndep (CoordinateWeights.weightSpace b) hA.submodule_iSup_eq_top
    (tensorWeightSpace a a) (tensorWeightSpace_iSupIndep a a hprod)
    (fun _ _ _ hx _ hy => tmul_mem_tensorWeightSpace a a hx hy) χ hmem

/-- The counit vanishes on the `χ`-space for `χ ≠ 0`. -/
theorem coordCounit_eq_zero (b : AutomorphicAction S.toGrp H) (hS : IsSplitTorus S.toGrp)
    {χ : characterLattice S} (hχ : χ ≠ 0) {f : A} (hf : f ∈ CoordinateWeights.weightSpace b χ) :
    coordCounit H f = 0 := by
  classical
  obtain ⟨hA, hAug, -, -⟩ := CoordinateWeights.coordinateWeightDecomposition k H inferInstance S hS b
  let _ : DirectSum.Decomposition (CoordinateWeights.weightSpace b) := hA.chooseDecomposition
  let U : characterLattice S → Submodule k A := fun ψ =>
    (CoordinateWeights.augmentationWeightSpace b ψ).map (CoordinateWeights.augmentation H).subtype
  have hz : f - algebraMap k A (coordCounit H f) ∈ CoordinateWeights.augmentation H := by
    rw [CoordinateWeights.mem_augmentation]
    change coordCounit H (f - algebraMap k A (coordCounit H f)) = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  have hsup : CoordinateWeights.augmentation H ≤ ⨆ ψ, U ψ := by
    rw [← Submodule.map_iSup, hAug.submodule_iSup_eq_top, Submodule.map_top,
      Submodule.range_subtype]
  have key : ∀ z ∈ ⨆ ψ, U ψ,
      coordCounit H (gradedProj (CoordinateWeights.weightSpace b) χ z) = 0 := by
    intro z hz
    refine Submodule.iSup_induction U
      (motive := fun z => coordCounit H (gradedProj (CoordinateWeights.weightSpace b) χ z) = 0)
      hz ?_ ?_ ?_
    · rintro ψ _ ⟨w, hw, rfl⟩
      have hw' : (w : A) ∈ CoordinateWeights.weightSpace b ψ := hw
      by_cases h : ψ = χ
      · subst h
        rw [Submodule.subtype_apply, gradedProj_of_mem hw']
        exact w.2
      · rw [Submodule.subtype_apply, gradedProj_of_mem_ne hw' h, map_zero]
    · rw [map_zero, map_zero]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy, add_zero]
  have h1 := key _ (hsup hz)
  rwa [map_sub, gradedProj_of_mem hf, Algebra.algebraMap_eq_smul_one, map_smul,
    gradedProj_of_mem_ne (one_mem_weightSpace_zero b) (Ne.symm hχ), smul_zero, sub_zero] at h1

end Group

end Langlands.GroupScheme.TorusUnipotence
