import Langlands.LinearAlgebra.GaloisPiDescent
import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation

/-! # Scalar extension and descent of actual stable subspaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [Fintype n] [DecidableEq n] in
/-- Extending a matrix range is the range of the extended matrix. -/
theorem scalarExtension_range (B : Matrix n m k) :
    scalarExtension (K := K) (LinearMap.range B.mulVecLin) =
      LinearMap.range (B.map (algebraMap k K)).mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v, ⟨w, rfl⟩, rfl⟩
    refine ⟨extend w, ?_⟩
    ext i
    exact ((algebraMap k K).map_mulVec B w i).symm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact Submodule.subset_span ⟨fun i => B i j,
      ⟨Pi.single j 1, Matrix.mulVec_single_one B j⟩, rfl⟩

omit [Fintype n] [DecidableEq n] in
/-- Every original-field coefficient of a vector in an extended subspace
belongs to the original subspace. -/
theorem linearFunctional_mem_scalarExtension {V : Submodule k (n → k)}
    {x : n → K} (hx : x ∈ scalarExtension (K := K) V) (φ : K →ₗ[k] k) :
    (fun i => φ (x i)) ∈ V := by
  suffices ∀ φ : K →ₗ[k] k, (fun i => φ (x i)) ∈ V from this φ
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      intro φ
      have h (a : k) : φ (algebraMap k K a) = a * φ 1 := by
        have hh := φ.map_smul a (1 : K)
        simpa only [Algebra.smul_def, mul_one, smul_eq_mul, Algebra.algebraMap_self_apply] using hh
      simpa only [extend_apply, h, mul_comm, Pi.smul_def, smul_eq_mul] using
        V.smul_mem (φ 1) hv
  | zero =>
      intro φ
      simpa only [Pi.zero_def, map_zero] using V.zero_mem
  | add x y hx hy ihx ihy =>
      intro φ
      simpa only [Pi.add_def, map_add] using V.add_mem (ihx φ) (ihy φ)
  | smul a x hx ih =>
      intro φ
      let ψ : K →ₗ[k] k := φ.comp (Algebra.lmul k K a)
      exact ih ψ

end Langlands.LinearAlgebra.GaloisPiDescent

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

section Descent

/-- Extending a linear functional to the first tensor factor, with values in K. -/
def scalarExtensionFunctional {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : A →ₗ[k] k) : K ⊗[k] A →ₗ[K] K :=
  (Algebra.TensorProduct.rid k K K).toLinearMap.comp (ℓ.baseChange K)

@[simp] theorem scalarExtensionFunctional_tmul
    {A : Type u} [CommRing A] [Algebra k A]
    (ℓ : A →ₗ[k] k) (c : K) (a : A) :
    scalarExtensionFunctional (K := K) ℓ (c ⊗ₜ[k] a) = c * algebraMap k K (ℓ a) := by
  simp [scalarExtensionFunctional, LinearMap.baseChange_tmul,
    Algebra.smul_def, mul_comm]

/-- Original vectors in an extension-field stable subspace form an original stable
subspace. No Galois stability or separability hypothesis is needed. -/
theorem IsStableSubspace.descend {ρ : MatrixRepresentation G n}
    {W : Submodule K (n → K)}
    (hW : (ρ.baseChange (algebraBaseMap k K)).IsStableSubspace W) :
    ρ.IsStableSubspace (descend (k := k) W) := by
  intro A x v hv ℓ
  let S := K ⊗[k] A
  let A₁ := CommAlgCat.of (CommRingCat.of K) S
  let A₀ := CommAlgCat.of (CommRingCat.of k) S
  let incR : A ⟶ A₀ := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let y : G.affinePoints A₀ := (algSpec (CommRingCat.of k)).map incR.op ≫ x
  have hs (a : k) : algebraMap K S (algebraMap k K a) =
      incR.hom (algebraMap k A a) := by
    rw [← IsScalarTower.algebraMap_apply k K S a, incR.hom.commutes]
  have hmat := affineMatrix_scalarExtensionPoint (K := K) S ρ y
  rw [affineMatrix_naturality] at hmat
  have h := hW A₁ (scalarExtensionPoint S y) (extend v) hv
    (scalarExtensionFunctional ℓ)
  rw [hmat] at h
  have hvec :
      (Matrix.GeneralLinearGroup.map incR.hom.toRingHom (ρ.affineMatrix A x) :
        Matrix n n S) *ᵥ (fun j => algebraMap K S (extend (K := K) v j)) =
      fun i => incR.hom (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (v j))) i) := by
    change ((ρ.affineMatrix A x : Matrix n n A).map incR.hom.toRingHom *ᵥ
      (fun j => algebraMap K S (algebraMap k K (v j)))) = _
    simp only [hs]
    funext i
    exact (incR.hom.toRingHom.map_mulVec _ _ i).symm
  change (fun i => scalarExtensionFunctional (K := K) ℓ
    (((Matrix.GeneralLinearGroup.map incR.hom.toRingHom (ρ.affineMatrix A x) :
      Matrix n n S) *ᵥ (fun j => algebraMap K S (extend (K := K) v j))) i)) ∈ W at h
  rw [hvec] at h
  change (fun i => algebraMap k K (ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
    (fun j => algebraMap k A (v j))) i))) ∈ W
  change (fun i => scalarExtensionFunctional (K := K) ℓ
    (1 ⊗ₜ[k] (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
      (fun j => algebraMap k A (v j))) i))) ∈ W at h
  simpa only [scalarExtensionFunctional_tmul, one_mul] using h

end Descent

section Extension

variable [IsAffineHom G.X.hom]

/-- Every actual stable subspace remains stable after scalar extension. -/
theorem IsStableSubspace.scalarExtension {ρ : MatrixRepresentation G n}
    {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V) :
    (ρ.baseChange (algebraBaseMap k K)).IsStableSubspace (scalarExtension (K := K) V) := by
  obtain ⟨r, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hcoords := hV.isStableCoordinates B C hcols hproj
  let τ := restrictCoordinates ρ B C hCB hcoords
  have hB : τ.Intertwines ρ B := intertwines_restrictCoordinates ρ B C hCB hcoords
  have hrange := range_coordinateInclusion_eq V B C hcols hproj
  have hBK := hB.baseChange (K := K)
  have hstable := hBK.isStableSubspace_range
  rwa [← scalarExtension_range B, hrange] at hstable

/-- Stability is preserved and reflected by every field extension. -/
theorem isStableSubspace_scalarExtension_iff (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k)) :
    (ρ.baseChange (algebraBaseMap k K)).IsStableSubspace (scalarExtension (K := K) V) ↔
      ρ.IsStableSubspace V := by
  constructor
  · intro h
    have hh := h.descend (k := k)
    rwa [descend_scalarExtension] at hh
  · exact fun h => h.scalarExtension

end Extension

end Langlands.GroupScheme.MatrixRepresentation
