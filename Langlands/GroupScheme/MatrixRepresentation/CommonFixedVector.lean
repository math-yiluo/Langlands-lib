import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Common fixed vectors for two unipotent factors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A finite-dimensional subspace has split coordinates with the stated image. -/
theorem exists_subspace_coordinates (W : Submodule k (n → k)) :
    ∃ (B : Matrix n (Fin (Module.finrank k W)) k)
      (C : Matrix (Fin (Module.finrank k W)) n k),
      C * B = 1 ∧
      (∀ w, B *ᵥ w ∈ W) ∧
      (∀ v, v ∈ W → (B * C) *ᵥ v = v) := by
  let b := Module.finBasis k W
  obtain ⟨p, hp⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let L : (Fin (Module.finrank k W) → k) →ₗ[k] (n → k) :=
    W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  let K : (n → k) →ₗ[k] (Fin (Module.finrank k W) → k) :=
    b.equivFun.toLinearMap ∘ₗ p
  have hKL : K.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext i
    change b.equivFun (p (W.subtype (b.equivFun.symm x))) i = x i
    have hpx := LinearMap.congr_fun hp (b.equivFun.symm x)
    change p (W.subtype (b.equivFun.symm x)) = b.equivFun.symm x at hpx
    rw [hpx, b.equivFun.apply_symm_apply]
  refine ⟨LinearMap.toMatrix' L, LinearMap.toMatrix' K, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hKL, LinearMap.toMatrix'_id]
  · intro w
    rw [LinearMap.toMatrix'_mulVec]
    exact (b.equivFun.symm w).property
  · intro v hv
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
      LinearMap.toMatrix'_mulVec]
    change W.subtype (b.equivFun.symm (b.equivFun (p v))) = v
    rw [b.equivFun.symm_apply_apply]
    have hpv := LinearMap.congr_fun hp (⟨v, hv⟩ : W)
    exact congrArg Subtype.val hpv

variable {G H J : GroupScheme (Spec (CommRingCat.of k))}

/-- A nonzero coordinate vector fixed by the restrictions to both factors. -/
def HasCommonFixedVector (ρ : MatrixRepresentation G n) (i : H ⟶ G) (j : J ⟶ G) : Prop :=
  ∃ v : n → k, v ≠ 0 ∧ (ρ.restrict i).IsFixedVector v ∧
    (ρ.restrict j).IsFixedVector v

/-- Two unipotent factors have a common nonzero fixed vector when the first is normal.
The supplied affine models retain all-test fixedness over an arbitrary field. -/
theorem exists_common_fixedVector_of_affine_models
    (ρ : MatrixRepresentation G n) [Nonempty n]
    (i : H ⟶ G) (j : J ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    {D E : CommAlgCat.{u} (CommRingCat.of k)}
    (a : (algSpec (CommRingCat.of k)).obj (op D) ≅ H.X)
    (b : (algSpec (CommRingCat.of k)).obj (op E) ≅ J.X)
    (hH : IsUnipotent H) (hJ : IsUnipotent J) :
    ρ.HasCommonFixedVector i j := by
  let W := (ρ.restrict i).fixedSubmodule
  obtain ⟨v, hv, hfix⟩ := hH n (ρ.restrict i)
  have hdim : 0 < Module.finrank k W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hfix⟩, fun h => hv (congrArg Subtype.val h)⟩
  let : Nonempty (Fin (Module.finrank k W)) := ⟨⟨0, hdim⟩⟩
  obtain ⟨B, C, hCB, hmem, hproj⟩ := exists_subspace_coordinates W
  have hcols (s : Fin (Module.finrank k W)) :
      (ρ.restrict i).IsFixedVector (fun r => B r s) := by
    have hs := hmem (Pi.single s 1)
    have hcol : B *ᵥ Pi.single s 1 = fun r => B r s := by
      funext r
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hcol] at hs
    exact hs
  have hstable : (ρ.restrict j).IsStableCoordinates B C := by
    apply isStableCoordinates_of_affine_model (ρ.restrict j) b B C
    rw [affineMatrix_restrict]
    exact normal_fixed_coordinates_affine ρ i hN a B C hcols hproj E
      (b.hom ≫ j.hom.hom)
  let σ := restrictCoordinates (ρ.restrict j) B C hCB hstable
  obtain ⟨w, hw, hσ⟩ := hJ (Fin (Module.finrank k W)) σ
  refine ⟨B *ᵥ w, ?_, hmem w, ?_⟩
  · intro hzero
    apply hw
    apply coordinateInclusion_injective B C hCB
    simpa only [Matrix.mulVec_zero] using hzero
  · exact isFixedVector_mulVec_restrictCoordinates (ρ.restrict j) B C hCB hstable hσ

/-- The affine version needs no chosen coordinate-algebra presentation. -/
theorem exists_common_fixedVector
    (ρ : MatrixRepresentation G n) [Nonempty n]
    (i : H ⟶ G) (j : J ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (hAffH : IsAffine H.X.left) (hAffJ : IsAffine J.X.left)
    (hH : IsUnipotent H) (hJ : IsUnipotent J) :
    ρ.HasCommonFixedVector i j := by
  obtain ⟨⟨D⟩, ⟨a⟩⟩ := (essImage_algSpec (G := H.X)).mpr hAffH
  obtain ⟨⟨E⟩, ⟨b⟩⟩ := (essImage_algSpec (G := J.X)).mpr hAffJ
  exact exists_common_fixedVector_of_affine_models ρ i j hN a b hH hJ

end Langlands.GroupScheme.MatrixRepresentation
