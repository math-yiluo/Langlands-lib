import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.GroupScheme.MatrixRepresentation.DirectSum
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Mathlib.LinearAlgebra.Pi

/-! # Simple subspaces and semisimplicity of actual direct sums -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section DirectSum

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  (ρ : ∀ i, MatrixRepresentation G (n i))

/-- The affine-test matrix of an actual direct sum is block diagonal. -/
theorem directSum_affineMatrix_val (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ G.X) :
    ((directSum ρ).affineMatrix A x : Matrix (Σ i, n i) (Σ i, n i) A) =
      Matrix.blockDiagonal' fun i =>
        ((ρ i).affineMatrix A x : Matrix (n i) (n i) A) := by
  have h := directSum_pointMatrix_val ρ ((algSpec R).obj (op A)) x
  let e := Corepresented.affineSectionsAlgEquiv A
  have hh := congrArg (fun M : Matrix (Σ i, n i) (Σ i, n i)
    Γ(((algSpec R).obj (op A)).left, ⊤) => M.map e.toRingHom) h
  have he {a : Type} [Fintype a] [DecidableEq a] (τ : MatrixRepresentation G a) :
      (τ.pointMatrix ((algSpec R).obj (op A)) x :
        Matrix a a Γ(((algSpec R).obj (op A)).left, ⊤)).map e.toRingHom =
          (τ.affineMatrix A x : Matrix a a A) := by
    rw [pointMatrix_eq_affineMatrix]
    ext i j
    exact e.apply_symm_apply _
  rw [he] at hh
  erw [Matrix.blockDiagonal'_map _ _ (map_zero _)] at hh
  apply hh.trans
  congr 1
  funext i
  exact he (ρ i)

/-- The matrix of the canonical inclusion of one coordinate summand. -/
def directSumInclusion (i : I) : Matrix (Σ j, n j) (n i) R :=
  LinearMap.toMatrix' <|
    (LinearEquiv.piCurry R (fun i (_ : n i) => R)).symm.toLinearMap.comp
      (LinearMap.single R (fun i => n i → R) i)

omit [Fintype I] in
/-- The inclusion matrix acts by extension by zero to the other summands. -/
theorem directSumInclusion_mulVec (i : I) (v : n i → R) :
    directSumInclusion (n := n) (R := R) i *ᵥ v =
      Sigma.uncurry (Pi.single (M := fun j => n j → R) i v) := by
  rw [directSumInclusion, LinearMap.toMatrix'_mulVec]
  rfl

omit [Fintype I] in
/-- Each canonical coordinate-summand inclusion is injective. -/
theorem directSumInclusion_injective (i : I) :
    Function.Injective (directSumInclusion (n := n) (R := R) i).mulVecLin := by
  intro v w h
  have h' := congrArg (fun f => fun a => f ⟨i, a⟩) h
  simpa only [Matrix.mulVecLin_apply, directSumInclusion_mulVec,
    Sigma.uncurry, Pi.single_eq_same] using h'

omit [Fintype I] in
/-- Scalar extension preserves a canonical coordinate-summand inclusion. -/
theorem directSumInclusion_map {A : CommRingCat.{u}} (f : R →+* A) (i : I) :
    (directSumInclusion (n := n) (R := R) i).map f =
      directSumInclusion (n := n) (R := A) i := by
  ext ⟨j, a⟩ b
  by_cases h : j = i
  · subst j
    simp [directSumInclusion, LinearMap.comp_apply, Sigma.uncurry,
      LinearMap.single_apply, Pi.single_apply]
  · simp [directSumInclusion, LinearMap.comp_apply, Sigma.uncurry,
      LinearMap.single_apply, Pi.single_eq_of_ne h]

omit [∀ i, DecidableEq (n i)] in
/-- A block diagonal matrix acts separately in each coordinate summand. -/
theorem blockDiagonal_mulVec_apply {A : Type*} [CommSemiring A]
    (M : ∀ i, Matrix (n i) (n i) A)
    (v : (Σ i, n i) → A) (i : I) (a : n i) :
    (Matrix.blockDiagonal' M *ᵥ v) ⟨i, a⟩ =
      (M i *ᵥ (fun b => v ⟨i, b⟩)) a := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j hj
    apply Finset.sum_eq_zero
    intro b hb
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hj.symm, zero_mul]

/-- Every vector is the sum of its coordinate-summand components. -/
theorem sum_directSumInclusion_mulVec (v : (Σ i, n i) → R) :
    ∑ i, directSumInclusion (n := n) (R := R) i *ᵥ (fun a => v ⟨i, a⟩) = v := by
  simp_rw [directSumInclusion_mulVec]
  have h := LinearMap.sum_single_apply (fun i => n i → R) (fun i a => v ⟨i, a⟩)
  funext ⟨j, a⟩
  simpa only [Finset.sum_apply, Sigma.uncurry] using
    congrArg (fun f => f j a) h

/-- Extending a vector by zero commutes with the corresponding diagonal block. -/
theorem blockDiagonal_mulVec_directSumInclusion
    (M : ∀ i, Matrix (n i) (n i) R) (i : I) (v : n i → R) :
    Matrix.blockDiagonal' M *ᵥ (directSumInclusion (R := R) i *ᵥ v) =
      directSumInclusion (R := R) i *ᵥ (M i *ᵥ v) := by
  funext ⟨j, a⟩
  rw [blockDiagonal_mulVec_apply]
  simp_rw [directSumInclusion_mulVec]
  by_cases h : j = i
  · subst j
    simp only [Sigma.uncurry, Pi.single_eq_same]
  · simp only [Sigma.uncurry, Pi.single_eq_of_ne h, Pi.zero_apply]
    change (M j *ᵥ 0) a = 0
    rw [Matrix.mulVec_zero, Pi.zero_apply]

/-- Canonical inclusions intertwine each matrix with its block diagonal family. -/
theorem directSumInclusion_mul
    (M : ∀ i, Matrix (n i) (n i) R) (i : I) :
    directSumInclusion (R := R) i * M i =
      Matrix.blockDiagonal' M * directSumInclusion (R := R) i := by
  apply Matrix.ext_of_mulVec_single
  intro a
  have h := (blockDiagonal_mulVec_directSumInclusion M i (Pi.single a 1)).symm
  erw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
  exact h

end DirectSum

section Simple

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A nonzero stable subspace with no proper nonzero stable subspace. -/
def IsSimpleStableSubspace (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k)) : Prop :=
  ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W

/-- An injective intertwiner sends every simple stable subspace to a simple one. -/
theorem IsSimpleStableSubspace.map
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {V : Submodule k (n → k)} (hV : ρ.IsSimpleStableSubspace V)
    {C : Matrix m n k} (hC : ρ.Intertwines σ C)
    (hi : Function.Injective C.mulVecLin) :
    σ.IsSimpleStableSubspace (V.map C.mulVecLin) := by
  refine ⟨hV.1.map hC, ?_, ?_⟩
  · intro hbot
    apply hV.2.1
    apply Submodule.map_injective_of_injective hi
    simpa only [Submodule.map_bot] using hbot
  · intro U hU hle
    have hpre : U.comap C.mulVecLin ≤ V := by
      have h := Submodule.comap_mono (f := C.mulVecLin) hle
      rwa [Submodule.comap_map_eq_of_injective hi] at h
    rcases hV.2.2 _ (hU.comap hC) hpre with h | h
    · left
      apply le_antisymm ?_ bot_le
      intro w hw
      obtain ⟨v, hv, rfl⟩ := hle hw
      have hv0 : v = 0 := by
        have hvU : v ∈ U.comap C.mulVecLin := hw
        simpa only [h, Submodule.mem_bot] using hvU
      simp only [hv0, map_zero, Submodule.zero_mem]
    · right
      apply le_antisymm hle
      rintro w ⟨v, hv, rfl⟩
      show v ∈ U.comap C.mulVecLin
      rwa [h]

/-- A bijective actual intertwiner transports semisimplicity. -/
theorem IsSemisimple.of_bijective_intertwiner
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    (hρ : ρ.IsSemisimple) {C : Matrix m n k}
    (hC : ρ.Intertwines σ C) (hbij : Function.Bijective C.mulVecLin) :
    σ.IsSemisimple := by
  have hle : (sSup {V : Submodule k (n → k) | ρ.IsSimpleStableSubspace V}).map
      C.mulVecLin ≤ sSup {W : Submodule k (m → k) | σ.IsSimpleStableSubspace W} := by
    rw [Submodule.map_le_iff_le_comap]
    apply sSup_le
    intro V hV
    apply Submodule.map_le_iff_le_comap.mp
    exact le_sSup (hV.map hC hbij.1)
  change sSup {V : Submodule k (n → k) | ρ.IsSimpleStableSubspace V} = ⊤ at hρ
  rw [hρ, Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2] at hle
  exact eq_top_iff.mpr hle

/-- The injective equivariant image of a simple representation is a simple subspace. -/
theorem IsIrreducible.isSimpleStableSubspace_range
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    (hρ : ρ.IsIrreducible) {C : Matrix m n k}
    (hC : ρ.Intertwines σ C) (hi : Function.Injective C.mulVecLin) :
    σ.IsSimpleStableSubspace (LinearMap.range C.mulVecLin) := by
  let := hρ.1
  refine ⟨hC.isStableSubspace_range, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : n → k)
    intro hbot
    have hCv : C.mulVecLin v ≠ 0 := by
      intro h
      apply hv
      exact hi (h.trans (map_zero _).symm)
    apply hCv
    have hmem : C.mulVecLin v ∈ LinearMap.range C.mulVecLin := ⟨v, rfl⟩
    simpa only [hbot, Submodule.mem_bot] using hmem
  · intro U hU hle
    rcases hρ.2 (U.comap C.mulVecLin) (hU.comap hC) with h | h
    · left
      apply le_antisymm ?_ bot_le
      intro w hw
      obtain ⟨v, rfl⟩ := hle hw
      have hv : v ∈ U.comap C.mulVecLin := hw
      have hv0 : v = 0 := by simpa only [h, Submodule.mem_bot] using hv
      simp only [hv0, map_zero, Submodule.zero_mem]
    · right
      apply le_antisymm hle
      rintro w ⟨v, rfl⟩
      exact (show v ∈ U.comap C.mulVecLin by rw [h]; trivial)

end Simple

section SemisimpleDirectSum

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  (ρ : ∀ i, MatrixRepresentation G (n i))

/-- Each canonical summand inclusion intertwines the actual representations. -/
theorem intertwines_directSumInclusion (i : I) :
    (ρ i).Intertwines (directSum ρ)
      (directSumInclusion (n := n) (R := CommRingCat.of k) i) := by
  intro A x
  rw [directSum_affineMatrix_val]
  rw [directSumInclusion_map (R := CommRingCat.of k)
    (A := CommRingCat.of A) (algebraMap k A)]
  exact directSumInclusion_mul (R := CommRingCat.of A)
    (fun i => ((ρ i).affineMatrix A x : Matrix (n i) (n i) A)) i

/-- A finite direct sum of simple actual representations is semisimple. -/
theorem isSemisimple_directSum (hρ : ∀ i, (ρ i).IsIrreducible) :
    (directSum ρ).IsSemisimple := by
  unfold IsSemisimple
  apply eq_top_iff.mpr
  intro v hv
  rw [← sum_directSumInclusion_mulVec (R := CommRingCat.of k) (n := n) v]
  apply Submodule.sum_mem
  intro i hi
  have hS : LinearMap.range
      (directSumInclusion (n := n) (R := CommRingCat.of k) i).mulVecLin ≤
      sSup {W | (directSum ρ).IsSimpleStableSubspace W} :=
    le_sSup ((hρ i).isSimpleStableSubspace_range
      (intertwines_directSumInclusion ρ i) (directSumInclusion_injective i))
  exact hS ⟨_, rfl⟩

end SemisimpleDirectSum

end Langlands.GroupScheme.MatrixRepresentation
