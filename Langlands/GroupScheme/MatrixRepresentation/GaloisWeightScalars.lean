import Langlands.GroupScheme.MatrixRepresentation.CharacterIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.GaloisCharacterSpaces
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Galois.Infinite

/-! # Descent of equivariant scalar operators on actual weight spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section ScalarOperator

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Prescribing a scalar on each actual character space gives a linear operator.
No spanning hypothesis is needed for this existence lemma. -/
theorem exists_characterScalarOperator (ρ : MatrixRepresentation G n)
    (f : rationalCharacters G → k) :
    ∃ F : Module.End k (n → k), ∀ χ v, v ∈ ρ.characterSpace χ → F v = f χ • v := by
  classical
  let Ω := {χ : rationalCharacters G // ρ.characterSpace χ ≠ ⊥}
  let : Fintype Ω := ρ.characterSpace_iSupIndep.fintypeNeBotOfFiniteDimensional
  let F : Module.End k (n → k) := ∑ χ : Ω, f χ.val • ρ.characterProjector χ.val
  refine ⟨F, ?_⟩
  intro ψ v hv
  by_cases hψ : ρ.characterSpace ψ = ⊥
  · have hv0 : v = 0 := by rwa [hψ] at hv
    rw [hv0, map_zero, smul_zero]
  let ψ₀ : Ω := ⟨ψ, hψ⟩
  change (∑ χ : Ω, f χ.val • ρ.characterProjector χ.val) v = f ψ • v
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single ψ₀]
  · rw [characterProjector_of_mem ρ ψ ψ hv]
    simp only [ψ₀, ite_true]
  · intro χ hχ hne
    have hneq : ψ ≠ χ.val := by
      intro heq
      apply hne
      exact Subtype.ext heq.symm
    rw [characterProjector_of_mem ρ χ.val ψ hv, ite_eq_right hneq, smul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ ψ₀))

end ScalarOperator

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- A Galois-equivariant scalar on every occurring geometric character is realized
by one actual original-field intertwining matrix. -/
theorem exists_intertwiner_with_weight_scalars (ρ : MatrixRepresentation G n)
    (hspan : (⨆ χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G),
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) = ⊤)
    (f : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) → K)
    (hf : ∀ (σ : K ≃ₐ[k] K)
      (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)),
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ →
        f (rationalCharacters.galoisRepresentation k K G σ χ) = σ (f χ)) :
    ∃ D : Matrix n n k, ρ.Intertwines ρ D ∧
      ∀ χ v, v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ →
        D.map (algebraMap k K) *ᵥ v = f χ • v := by
  classical
  obtain ⟨F, hF⟩ := exists_characterScalarOperator (ρ.baseChange (algebraBaseMap k K)) f
  let C := LinearMap.toMatrix' F
  have hC : (ρ.baseChange (algebraBaseMap k K)).Intertwines
      (ρ.baseChange (algebraBaseMap k K)) C := by
    apply (intertwines_iff_maps_characterSpaces _ _ C hspan).mpr
    intro χ v hv
    change (LinearMap.toMatrix' F) *ᵥ v ∈ _
    rw [LinearMap.toMatrix'_mulVec, hF χ v hv]
    exact ((ρ.baseChange (algebraBaseMap k K)).characterSpace χ).smul_mem _ hv
  have hcomm (σ : K ≃ₐ[k] K) (v : n → K) :
      F (fun i => σ (v i)) = fun i => σ (F v i) := by
    let g : (n → K) → (n → K) := fun w i => σ (w i)
    have hg0 : g 0 = 0 := by ext i; exact map_zero σ
    have hgadd (v w : n → K) : g (v + w) = g v + g w := by
      ext i
      exact map_add σ (v i) (w i)
    have hgsmul (a : K) (v : n → K) : g (a • v) = σ a • g v := by
      ext i
      exact map_mul σ a (v i)
    let W : Submodule K (n → K) :=
      { carrier := {v | F (g v) = g (F v)}
        zero_mem' := by
          change F (g 0) = g (F 0)
          rw [hg0, map_zero, hg0]
        add_mem' := by
          intro v w hv hw
          change F (g (v + w)) = g (F (v + w))
          rw [hgadd, map_add, map_add, hgadd, hv, hw]
        smul_mem' := by
          intro a v hv
          change F (g (a • v)) = g (F (a • v))
          rw [hgsmul, map_smul, map_smul, hgsmul, hv] }
    have hle : (⨆ χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G),
        (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) ≤ W := by
      apply iSup_le
      intro χ w hw
      by_cases hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ = ⊥
      · have hw0 : w = 0 := by rwa [hχ] at hw
        rw [hw0]
        exact W.zero_mem
      change F (g w) = g (F w)
      have hgw := conjugate_mem_characterSpace_baseChange ρ σ χ hw
      rw [hF _ _ hgw, hF χ w hw, hf σ χ hχ]
      exact (hgsmul (f χ) w).symm
    exact hle (by rw [hspan]; trivial)
  have hfixed (σ : K ≃ₐ[k] K) (i j : n) : σ (C i j) = C i j := by
    have hh := hcomm σ (Pi.single j 1)
    have hsingle : (fun a => σ ((Pi.single j 1 : n → K) a)) = Pi.single j 1 := by
      ext a
      by_cases ha : a = j <;> simp [ha]
    rw [hsingle] at hh
    exact (congrFun hh i).symm
  have hground (i j : n) : ∃ a : k, algebraMap k K a = C i j :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (C i j)).mpr (fun σ => hfixed σ i j)
  choose D hD using hground
  have hmap : Matrix.map (D : Matrix n n k) (algebraMap k K) = C := by
    ext i j
    exact hD i j
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero (α := K))
  have hφmap : (Matrix.map (D : Matrix n n k) (algebraMap k K)).map φ = D := by
    ext i j
    change φ (algebraMap k K (D i j)) = D i j
    have hh := φ.map_smul (D i j) (1 : K)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one, hφ] using hh
  have hDint := hC.linearFunctional_descent φ
  rw [← hmap, hφmap] at hDint
  refine ⟨D, hDint, ?_⟩
  intro χ v hv
  rw [hmap, LinearMap.toMatrix'_mulVec]
  exact hF χ v hv

end Galois

end Langlands.GroupScheme.MatrixRepresentation
