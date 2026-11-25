import Langlands.GroupScheme.MatrixRepresentation.CharacterIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.IrreducibleWeightOrbit
import Langlands.GroupScheme.MatrixRepresentation.BaseChangedWeightExistence

/-! # Irreducible realization of actual geometric character orbits -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An injective actual intertwiner reflects actual character-vector membership. -/
theorem Intertwines.mem_characterSpace_iff_of_injective
    {ρ : MatrixRepresentation G n} {τ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : ρ.Intertwines τ C) (hinj : Function.Injective C.mulVecLin)
    (χ : rationalCharacters G) (v : n → k) :
    C *ᵥ v ∈ τ.characterSpace χ ↔ v ∈ ρ.characterSpace χ := by
  constructor
  · intro hv
    rw [mem_characterSpace_iff] at hv ⊢
    let A := CharacterUnits.Coord G
    have hvec : (fun i => algebraMap k A ((C *ᵥ v) i)) =
        C.map (algebraMap k A) *ᵥ (fun i => algebraMap k A (v i)) := by
      ext i
      exact (algebraMap k A).map_mulVec C v i
    have hCU := (intertwines_iff_universalCharacterMatrix ρ τ C).mp hC
    rw [hvec, Matrix.mulVec_mulVec, ← hCU, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_smul] at hv
    have hi := Lie.mulVecLin_map_injective C hinj (A := A)
    apply hi
    simpa only [Matrix.mulVecLin_apply] using hv
  · exact hC.mem_characterSpace

/-- A supplied nonzero simple stable subspace has actual irreducible split
coordinates whose inclusion has exactly that image. -/
theorem exists_irreducible_subrepresentation_with_range (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k)) (hV : ρ.IsStableSubspace V) (hV0 : V ≠ ⊥)
    (hmin : ∀ W : Submodule k (n → k), ρ.IsStableSubspace W → W ≤ V → W = ⊥ ∨ W = V) :
    ∃ (d : ℕ) (τ : MatrixRepresentation G (Fin d)) (B : Matrix n (Fin d) k),
      τ.IsIrreducible ∧ τ.Intertwines ρ B ∧ Function.Injective B.mulVecLin ∧
        LinearMap.range B.mulVecLin = V := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B C hcols hproj
  let τ := restrictCoordinates ρ B C hCB hstable
  have hB : τ.Intertwines ρ B := intertwines_restrictCoordinates ρ B C hCB hstable
  have hi : Function.Injective B.mulVecLin :=
    coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
  have hrange := range_coordinateInclusion_eq V B C hcols hproj
  have hn : Nontrivial (Fin d → k) := by
    by_contra h
    have : Subsingleton (Fin d → k) := not_nontrivial_iff_subsingleton.mp h
    apply hV0
    rw [← hrange]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv, map_zero, LinearMap.zero_apply]
  refine ⟨d, τ, B, ⟨hn, ?_⟩, hB, hi, hrange⟩
  intro W hW
  have hW' := hW.map hB
  have hle : W.map B.mulVecLin ≤ V := by
    rw [← hrange]
    exact LinearMap.map_le_range
  have hmapinj := Submodule.map_injective_of_injective hi
  rcases hmin _ hW' hle with h | h
  · left
    apply hmapinj
    simpa only [Submodule.map_bot] using h
  · right
    apply hmapinj
    simpa only [Submodule.map_top, hrange] using h

/-- The actual character coefficient projector preserves every actual stable subspace. -/
theorem IsStableSubspace.characterProjector_mem {ρ : MatrixRepresentation G n}
    {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (χ : rationalCharacters G) {v : n → k} (hv : v ∈ V) :
    ρ.characterProjector χ v ∈ V :=
  hV (CharacterUnits.Coord G) (CharacterUnits.universalPoint G) v hv (characterCoefficient χ)

/-- When character spaces span, the coefficient projector has image in its
actual character space. -/
theorem characterProjector_mem_characterSpace_of_span (ρ : MatrixRepresentation G n)
    (hspan : (⨆ ψ : rationalCharacters G, ρ.characterSpace ψ) = ⊤)
    (χ : rationalCharacters G) (v : n → k) :
    ρ.characterProjector χ v ∈ ρ.characterSpace χ := by
  classical
  let V := (ρ.characterSpace χ).comap (ρ.characterProjector χ)
  have hle : (⨆ ψ : rationalCharacters G, ρ.characterSpace ψ) ≤ V := by
    apply iSup_le
    intro ψ w hw
    change ρ.characterProjector χ w ∈ ρ.characterSpace χ
    rw [characterProjector_of_mem ρ χ ψ hw]
    by_cases hψ : ψ = χ
    · subst ψ
      simpa only [ite_true] using hw
    · simp only [ite_eq_right hψ]
      exact (ρ.characterSpace χ).zero_mem
  exact hle (by rw [hspan]; trivial)

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- A specified nonzero geometric character of a semisimple original representation
is retained in an actual simple subrepresentation whenever geometric character spaces span. -/
theorem exists_irreducible_subrepresentation_with_geometric_weight
    (ρ : MatrixRepresentation G n) (hss : ρ.IsSemisimple)
    (hspan : (⨆ ψ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G),
      (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ) = ⊤)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥) :
    ∃ (d : ℕ) (τ : MatrixRepresentation G (Fin d)) (B : Matrix n (Fin d) k),
      τ.IsIrreducible ∧ τ.Intertwines ρ B ∧ Function.Injective B.mulVecLin ∧
        (τ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
  classical
  let S := {V : Submodule k (n → k) | ρ.IsStableSubspace V ∧ V ≠ ⊥ ∧
    ∀ W : Submodule k (n → k), ρ.IsStableSubspace W → W ≤ V → W = ⊥ ∨ W = V}
  let P := (ρ.baseChange (algebraBaseMap k K)).characterProjector χ
  have hsum : sSup S = ⊤ := hss
  have hex : ∃ V ∈ S, ∃ x ∈ scalarExtension (K := K) V, P x ≠ 0 := by
    by_contra h
    push Not at h
    let F : (n → k) →ₗ[k] (n → K) := (P.restrictScalars k).comp
      (Langlands.LinearAlgebra.GaloisPiDescent.extend : (n → k) →ₗ[k] (n → K))
    have hker : sSup S ≤ LinearMap.ker F := by
      apply sSup_le
      intro V hV v hv
      exact h V hV (extend v) (Submodule.subset_span ⟨v, hv, rfl⟩)
    have hground (v : n → k) : P (extend v) = 0 :=
      hker (by rw [hsum]; trivial)
    have hkerK : scalarExtension (K := K) (⊤ : Submodule k (n → k)) ≤ LinearMap.ker P := by
      apply Submodule.span_le.mpr
      rintro x ⟨v, hv, rfl⟩
      exact hground v
    rw [scalarExtension_top] at hkerK
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
    have hzero : P v = 0 := hkerK (by trivial)
    have hpv : P v = v := by
      simpa only [ite_true] using characterProjector_of_mem _ χ χ hv
    exact hv0 (hpv.symm.trans hzero)
  obtain ⟨V, hV, x, hx, hpx⟩ := hex
  obtain ⟨d, τ, B, hτ, hB, hi, hrange⟩ :=
    exists_irreducible_subrepresentation_with_range ρ V hV.1 hV.2.1 hV.2.2
  have hBK := hB.baseChange (K := K)
  have hiK := Lie.mulVecLin_map_injective B hi (A := K)
  have hmem : P x ∈ scalarExtension (K := K) V :=
    hV.1.scalarExtension.characterProjector_mem χ hx
  rw [← hrange, scalarExtension_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hzχ : z ∈ (τ.baseChange (algebraBaseMap k K)).characterSpace χ := by
    apply (hBK.mem_characterSpace_iff_of_injective hiK χ z).mp
    rw [← Matrix.mulVecLin_apply, hz]
    exact characterProjector_mem_characterSpace_of_span _ hspan χ x
  have hz0 : z ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hz
    exact hpx hz.symm
  exact ⟨d, τ, B, hτ, hB, hi, (Submodule.ne_bot_iff _).mpr ⟨z, hzχ, hz0⟩⟩

omit [IsAffineHom G.X.hom] in
/-- Shifting the chosen center of an actual Galois orbit within that orbit
leaves its range unchanged. -/
theorem galoisOrbit_range_eq_of_mem
    (χ ψ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hχ : χ ∈ Set.range (fun σ : K ≃ₐ[k] K =>
      rationalCharacters.galoisRepresentation k K G σ ψ)) :
    Set.range (fun σ : K ≃ₐ[k] K => rationalCharacters.galoisRepresentation k K G σ χ) =
      Set.range (fun σ : K ≃ₐ[k] K => rationalCharacters.galoisRepresentation k K G σ ψ) := by
  obtain ⟨σ, rfl⟩ := hχ
  apply Set.Subset.antisymm
  · rintro ξ ⟨τ, rfl⟩
    refine ⟨τ * σ, ?_⟩
    dsimp only
    rw [map_mul, Module.End.mul_apply]
  · rintro ξ ⟨τ, rfl⟩
    refine ⟨τ * σ⁻¹, ?_⟩
    dsimp only
    rw [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

/-- Every actual Galois orbit of a geometric character is the weight set of an
actual irreducible original finite representation of a multiplicative-type group. -/
theorem exists_irreducible_weights_eq_galoisOrbit_of_isMultiplicativeType
    [IsSepClosure k K] (hG : IsMultiplicativeType G)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    ∃ (d : ℕ) (τ : MatrixRepresentation G (Fin d)), τ.IsIrreducible ∧
      {ψ | (τ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥} =
        Set.range (fun σ : K ≃ₐ[k] K => rationalCharacters.galoisRepresentation k K G σ χ) := by
  obtain ⟨N, ρ, hχ⟩ := exists_weight_baseChange_of_isMultiplicativeType hG χ
  let : IsSepClosed K := IsSepClosure.sep_closed k
  have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
    k K G hG
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
  let := hΛ
  let := hfg
  have hspan := iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e
    (ρ.baseChange (algebraBaseMap k K))
  obtain ⟨d, τ, B, hτ, hB, hi, hτχ⟩ :=
    exists_irreducible_subrepresentation_with_geometric_weight ρ
      (isSemisimple_of_isMultiplicativeType ρ hG) hspan χ hχ
  obtain ⟨ψ, horbit⟩ := exists_weights_eq_galoisOrbit_of_isMultiplicativeType (K := K) τ hG hτ
  have hmem : χ ∈ Set.range (fun σ : K ≃ₐ[k] K =>
      rationalCharacters.galoisRepresentation k K G σ ψ) := by
    rw [← horbit]
    exact hτχ
  refine ⟨d, τ, hτ, horbit.trans ?_⟩
  exact (galoisOrbit_range_eq_of_mem χ ψ hmem).symm

end Langlands.GroupScheme.MatrixRepresentation
