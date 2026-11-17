import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation

/-! # Scalar endomorphisms of highest-weight representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An actual intertwiner preserves each all-algebra character space. -/
theorem Intertwines.mulVec_mem_characterSpace
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C)
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ) :
    C *ᵥ v ∈ σ.characterSpace χ := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  have hmap : C.map (algebraMap k A) *ᵥ (fun i => algebraMap k A (v i)) =
      (fun i => algebraMap k A ((C *ᵥ v) i)) := by
    funext i
    exact ((algebraMap k A).map_mulVec C v i).symm
  rw [← hmap, Matrix.mulVec_mulVec, ← hC A x, ← Matrix.mulVec_mulVec,
    characterSpace_affine hv A x, Matrix.mulVec_smul]

/-- The linear map induced by an actual intertwiner on a specified character space. -/
def Intertwines.characterSpaceLinearMap
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C) (χ : rationalCharacters G) :
    ρ.characterSpace χ →ₗ[k] σ.characterSpace χ where
  toFun v := ⟨C *ᵥ v, hC.mulVec_mem_characterSpace v.property⟩
  map_add' v w := Subtype.ext (C.mulVecLin.map_add v w)
  map_smul' c v := Subtype.ext (C.mulVecLin.map_smul c v)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : Type} [Fintype n] [DecidableEq n]

/-- Every endomorphism of a highest-weight representation is a scalar matrix. -/
theorem IsHighestWeight.intertwiner_eq_scalar
    {ρ : MatrixRepresentation G n} {lam : characterLattice p.torus}
    (hρ : p.IsHighestWeight ρ lam) (C : Matrix n n k) (hC : ρ.Intertwines ρ C) :
    ∃ c : k, C = Matrix.scalar n c := by
  let := p.isSplitTorus.isAffineHom
  let W := p.representationWeightSpace ρ lam
  have hCt : (ρ.restrict p.inclusion).Intertwines (ρ.restrict p.inclusion) C := by
    intro A x
    exact hC A (x ≫ p.inclusion.hom.hom)
  let L : W →ₗ[k] W := hCt.characterSpaceLinearMap
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hρ.2.2.1 L
  have hW0 : W ≠ ⊥ := by
    intro h
    have hd : Module.finrank k W = 1 := hρ.2.2.1
    rw [h, finrank_bot] at hd
    exact Nat.zero_ne_one hd
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hW0
  have hcv : C *ᵥ v = c • v := by
    exact congrArg Subtype.val (LinearMap.congr_fun hc ⟨v, hv⟩)
  let D := C - Matrix.scalar n c
  have hD : ρ.Intertwines ρ D := by
    intro A x
    have hmap : D.map (algebraMap k A) =
        C.map (algebraMap k A) - Matrix.scalar n (algebraMap k A c) := by
      ext i j
      by_cases hij : i = j <;>
        simp [D, Matrix.map_apply, Matrix.scalar_apply, hij]
    rw [hmap, Matrix.sub_mul, Matrix.mul_sub, hC A x]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hker : ρ.IsStableSubspace (LinearMap.ker D.mulVecLin) :=
    (MatrixRepresentation.isStableSubspace_bot ρ).comap hD
  have hvker : v ∈ LinearMap.ker D.mulVecLin := by
    change (C - Matrix.scalar n c) *ᵥ v = 0
    simp only [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
    simpa only [Pi.smul_apply, smul_eq_mul] using sub_eq_zero.mpr hcv
  have hkertop : LinearMap.ker D.mulVecLin = ⊤ := by
    rcases hρ.1.2 _ hker with h | h
    · exact False.elim (hv0 (by simpa only [h, Submodule.mem_bot] using hvker))
    · exact h
  refine ⟨c, sub_eq_zero.mp ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  have h := (show Pi.single j 1 ∈ LinearMap.ker D.mulVecLin by rw [hkertop]; trivial)
  simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.zero_mulVec] using h

end Langlands.GroupScheme.SplitPinning
