import Langlands.GroupScheme.MatrixRepresentation.CharacterIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.IrreducibleWeightOrbit

/-! # Isomorphism classification of actual simple multiplicative-type representations -/

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

/-- An injective actual intertwiner preserves nonzero character spaces. -/
theorem Intertwines.characterSpace_ne_bot {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C)
    (hinj : Function.Injective C.mulVecLin) (χ : rationalCharacters G)
    (hχ : ρ.characterSpace χ ≠ ⊥) : τ.characterSpace χ ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
  refine (Submodule.ne_bot_iff _).mpr ⟨C *ᵥ v, hC.mem_characterSpace hv, ?_⟩
  intro hz
  apply hv0
  apply hinj
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_zero] using hz

omit [IsAffineHom G.X.hom] in
/-- The inverse of an actual bijective intertwiner is another actual bijective
intertwiner in the opposite direction. -/
theorem Intertwines.exists_inverse_matrix {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C)
    (hbij : Function.Bijective C.mulVecLin) :
    ∃ D : Matrix n m k, τ.Intertwines ρ D ∧ Function.Bijective D.mulVecLin := by
  let e := LinearEquiv.ofBijective C.mulVecLin hbij
  let D := LinearMap.toMatrix' e.symm.toLinearMap
  have hDvec (v : m → k) : D *ᵥ v = e.symm v := LinearMap.toMatrix'_mulVec _ v
  have hCD : C * D = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    apply LinearMap.ext
    intro v
    change C *ᵥ (D *ᵥ v) = v
    rw [hDvec]
    exact e.apply_symm_apply v
  have hD : τ.Intertwines ρ D := by
    apply hC.of_comp_injective hbij.1
    rw [hCD]
    intro A x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  refine ⟨D, hD, ?_⟩
  have hlin : D.mulVecLin = e.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply]
    exact hDvec v
  rw [hlin]
  exact e.symm.bijective

/-- Actual isomorphisms preserve the full set of nonzero character spaces. -/
theorem Intertwines.weights_eq_of_bijective {ρ : MatrixRepresentation G n}
    {τ : MatrixRepresentation G m} {C : Matrix m n k} (hC : ρ.Intertwines τ C)
    (hbij : Function.Bijective C.mulVecLin) :
    {χ | ρ.characterSpace χ ≠ ⊥} = {χ | τ.characterSpace χ ≠ ⊥} := by
  obtain ⟨D, hD, hDij⟩ := hC.exists_inverse_matrix hbij
  ext χ
  exact ⟨hC.characterSpace_ne_bot hbij.1 χ, hD.characterSpace_ne_bot hDij.1 χ⟩

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- The exact isomorphism/weight-set equivalence for irreducible representations
of a multiplicative-type group, over any separable closure. -/
theorem isomorphic_iff_weights_eq_of_isMultiplicativeType [IsSepClosure k K]
    (ρ : MatrixRepresentation G n) (τ : MatrixRepresentation G m)
    (hG : IsMultiplicativeType G) (hρ : ρ.IsIrreducible) (hτ : τ.IsIrreducible) :
    (∃ C : Matrix m n k, ρ.Intertwines τ C ∧ Function.Bijective C.mulVecLin) ↔
      {χ | (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥} =
        {χ | (τ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥} := by
  constructor
  · rintro ⟨C, hC, hbij⟩
    exact (hC.baseChange (K := K)).weights_eq_of_bijective
      ⟨Lie.mulVecLin_map_injective C hbij.1, Lie.mulVecLin_map_surjective C hbij.2⟩
  · intro hweights
    obtain ⟨χ, horbit⟩ := exists_weights_eq_galoisOrbit_of_isMultiplicativeType
      (K := K) ρ hG hρ
    have hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
      have hm : χ ∈ Set.range (fun σ : K ≃ₐ[k] K =>
          rationalCharacters.galoisRepresentation k K G σ χ) :=
        ⟨1, by simp only [map_one, Module.End.one_apply]⟩
      rwa [← horbit] at hm
    have hχ' : (τ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
      have hm : χ ∈ {ψ | (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥} := hχ
      rwa [hweights] at hm
    let : IsSepClosed K := IsSepClosure.sep_closed k
    have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
      k K G hG
    obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
      MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
    let := hΛ
    let := hfg
    have hspan := iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e
      (ρ.baseChange (algebraBaseMap k K))
    obtain ⟨C, hC, hne⟩ := exists_nonzero_intertwiner_of_common_character
      (ρ.baseChange (algebraBaseMap k K)) (τ.baseChange (algebraBaseMap k K)) hspan χ hχ hχ'
    obtain ⟨D, hD, hD0⟩ := exists_nonzero_intertwiner_of_baseChange ρ τ C hC hne
    exact ⟨D, hD, hD.bijective_of_irreducible hρ hτ hD0⟩

end Langlands.GroupScheme.MatrixRepresentation
