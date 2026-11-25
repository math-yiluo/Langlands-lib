import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates
import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability

/-! # Actual intertwiners detected by character spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Every actual intertwiner maps each actual character space into the same
character space of the target. -/
theorem Intertwines.mem_characterSpace {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C)
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ) :
    C *ᵥ v ∈ τ.characterSpace χ := by
  rw [mem_characterSpace_iff] at hv ⊢
  let A := CharacterUnits.Coord G
  have hvec : (fun i => algebraMap k A ((C *ᵥ v) i)) =
      C.map (algebraMap k A) *ᵥ (fun i => algebraMap k A (v i)) := by
    ext i
    exact (algebraMap k A).map_mulVec C v i
  have hCU := (intertwines_iff_universalCharacterMatrix ρ τ C).mp hC
  rw [hvec, Matrix.mulVec_mulVec,
    ← hCU, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-- A coefficient endomorphism acts by the character coefficient on an actual
character vector, for arbitrary affine algebra tests. -/
theorem affineCoefficientEndomorphism_of_mem_characterSpace
    (ρ : MatrixRepresentation G n) {χ : rationalCharacters G}
    {v : n → k} (hv : v ∈ ρ.characterSpace χ)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A)
    (ℓ : A →ₗ[k] k) :
    ρ.affineCoefficientEndomorphism A x ℓ v =
      ℓ (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) • v := by
  rw [affineCoefficientEndomorphism_apply, characterSpace_affine hv A x]
  ext i
  change ℓ ((Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) *
    algebraMap k A (v i)) = ℓ _ * v i
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- When source character spaces span, preserving every character space is
equivalent to actual equivariance on all affine algebra tests. -/
theorem intertwines_iff_maps_characterSpaces (ρ : MatrixRepresentation G n)
    (τ : MatrixRepresentation G m) (C : Matrix m n k)
    (hspan : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤) :
    ρ.Intertwines τ C ↔ ∀ χ v, v ∈ ρ.characterSpace χ → C *ᵥ v ∈ τ.characterSpace χ := by
  constructor
  · exact fun h χ v hv => h.mem_characterSpace hv
  · intro h
    apply (intertwines_iff_linearFunctional_mulVec ρ τ C).mpr
    intro A x v ℓ
    let D := C.mulVecLin.comp (ρ.affineCoefficientEndomorphism A x ℓ) -
      (τ.affineCoefficientEndomorphism A x ℓ).comp C.mulVecLin
    have hker : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) ≤ LinearMap.ker D := by
      apply iSup_le
      intro χ w hw
      change C *ᵥ (ρ.affineCoefficientEndomorphism A x ℓ w) -
        τ.affineCoefficientEndomorphism A x ℓ (C *ᵥ w) = 0
      rw [affineCoefficientEndomorphism_of_mem_characterSpace ρ hw,
        affineCoefficientEndomorphism_of_mem_characterSpace τ (h χ w hw),
        Matrix.mulVec_smul, sub_self]
    have hv : v ∈ LinearMap.ker D := hker (by rw [hspan]; trivial)
    rw [← affineCoefficientEndomorphism_apply, ← affineCoefficientEndomorphism_apply]
    exact sub_eq_zero.mp hv

/-- A shared nonzero actual weight supplies a nonzero actual intertwiner when
the source character spaces span. -/
theorem exists_nonzero_intertwiner_of_common_character
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m)
    (hspan : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤)
    (χ : rationalCharacters G) (hρ : ρ.characterSpace χ ≠ ⊥)
    (hτ : τ.characterSpace χ ≠ ⊥) :
    ∃ C : Matrix m n k, ρ.Intertwines τ C ∧ C ≠ 0 := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hρ
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hτ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
  let F : (n → k) →ₗ[k] (m → k) := (φ.comp (ρ.characterProjector χ)).smulRight w
  let C := LinearMap.toMatrix' F
  refine ⟨C, ?_, ?_⟩
  · apply (intertwines_iff_maps_characterSpaces ρ τ C hspan).mpr
    intro ψ z hz
    change (LinearMap.toMatrix' F) *ᵥ z ∈ τ.characterSpace ψ
    rw [LinearMap.toMatrix'_mulVec]
    change φ (ρ.characterProjector χ z) • w ∈ τ.characterSpace ψ
    rw [characterProjector_of_mem ρ χ ψ hz]
    by_cases hψ : ψ = χ
    · subst ψ
      exact (τ.characterSpace χ).smul_mem _ hw
    · simp only [ite_eq_right hψ, map_zero, zero_smul]
      exact (τ.characterSpace ψ).zero_mem
  · intro hC
    apply hw0
    have heval : C *ᵥ v = w := by
      change (LinearMap.toMatrix' F) *ᵥ v = w
      rw [LinearMap.toMatrix'_mulVec]
      change φ (ρ.characterProjector χ v) • w = w
      rw [characterProjector_of_mem ρ χ χ hv, ite_eq_left rfl, hφ, one_smul]
    rw [hC, Matrix.zero_mulVec] at heval
    exact heval.symm

omit [IsAffineHom G.X.hom] in
/-- A nonzero actual intertwiner between irreducible representations is an
isomorphism on coordinate vector spaces. -/
theorem Intertwines.bijective_of_irreducible {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C)
    (hρ : ρ.IsIrreducible) (hτ : τ.IsIrreducible) (hne : C ≠ 0) :
    Function.Bijective C.mulVecLin := by
  have hlin : C.mulVecLin ≠ 0 := by
    intro hh
    apply hne
    apply Matrix.toLin'.injective
    simpa only [map_zero, Matrix.toLin'_apply'] using hh
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rcases hρ.2 (LinearMap.ker C.mulVecLin) hC.isStableSubspace_ker with h | h
    · exact h
    · exact False.elim (hlin (LinearMap.ker_eq_top.mp h))
  · apply LinearMap.range_eq_top.mp
    rcases hτ.2 (LinearMap.range C.mulVecLin) hC.isStableSubspace_range with h | h
    · exact False.elim (hlin (LinearMap.range_eq_bot.mp h))
    · exact h

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- A nonzero actual intertwiner after any field extension has a nonzero
original-field coefficient which is an original actual intertwiner. -/
theorem exists_nonzero_intertwiner_of_baseChange
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m)
    (C : Matrix m n K)
    (hC : (ρ.baseChange (algebraBaseMap k K)).Intertwines
      (τ.baseChange (algebraBaseMap k K)) C) (hne : C ≠ 0) :
    ∃ D : Matrix m n k, ρ.Intertwines τ D ∧ D ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    apply hne
    ext i j
    exact not_not.mp (fun hh => h ⟨i, j, hh⟩)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hij
  refine ⟨C.map φ, hC.linearFunctional_descent φ, ?_⟩
  intro hz
  have hh := congrFun (congrFun hz i) j
  change φ (C i j) = 0 at hh
  rw [hφ] at hh
  exact one_ne_zero hh

end Langlands.GroupScheme.MatrixRepresentation
