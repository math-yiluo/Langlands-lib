import Langlands.GroupScheme.MatrixRepresentation.GaloisCharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionStableSubspaces
import Langlands.GroupScheme.MatrixRepresentation.MultiplicativeTypeSemisimplicity
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability

/-! # Galois orbits of weights of actual irreducible representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem scalarExtension_bot :
    scalarExtension (K := K) (⊥ : Submodule k (n → k)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨v, hv, rfl⟩
  have hv0 : v = 0 := hv
  rw [hv0, map_zero]
  exact Submodule.zero_mem _

@[simp] theorem scalarExtension_top :
    scalarExtension (K := K) (⊤ : Submodule k (n → k)) = ⊤ := by
  have h := scalarExtension_range (K := K) (1 : Matrix n n k)
  simpa only [Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mulVecLin_one, LinearMap.range_id] using h

end Langlands.LinearAlgebra.GaloisPiDescent

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

local notation "G₁" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "Γ" => K ≃ₐ[k] K

/-- Every Galois conjugate of an actual nonzero weight space is nonzero. -/
theorem characterSpace_galois_ne_bot (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G₁) (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥)
    (σ : Γ) :
    (ρ.baseChange (algebraBaseMap k K)).characterSpace
      (rationalCharacters.galoisRepresentation k K G σ χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
  refine (Submodule.ne_bot_iff _).mpr ⟨fun i => σ (v i),
    conjugate_mem_characterSpace_baseChange ρ σ χ hv, ?_⟩
  intro hz
  apply hv0
  ext i
  apply σ.injective
  simpa only [map_zero, Pi.zero_apply] using congrFun hz i

/-- Sum of all actual weight spaces in one Galois orbit. -/
def galoisOrbitSubspace (ρ : MatrixRepresentation G n) (χ : rationalCharacters G₁) :
    Submodule K (n → K) :=
  ⨆ σ : Γ, (ρ.baseChange (algebraBaseMap k K)).characterSpace
    (rationalCharacters.galoisRepresentation k K G σ χ)

/-- Orbit sums are stable on every affine test algebra. -/
theorem isStableSubspace_galoisOrbitSubspace (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G₁) :
    (ρ.baseChange (algebraBaseMap k K)).IsStableSubspace (galoisOrbitSubspace ρ χ) := by
  apply IsStableSubspace.iSup
  intro σ
  exact isStableSubspace_of_le_characterSpace _ _ _ le_rfl

/-- Orbit sums are also invariant under coefficientwise Galois conjugation. -/
theorem isGaloisStable_galoisOrbitSubspace (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G₁) :
    IsGaloisStable (k := k) (galoisOrbitSubspace ρ χ) := by
  intro σ v hv
  refine Submodule.iSup_induction _ (motive := fun w =>
    (fun i => σ (w i)) ∈ galoisOrbitSubspace ρ χ) hv ?_ ?_ ?_
  · intro τ w hw
    have hh := conjugate_mem_characterSpace_baseChange ρ σ
      (rationalCharacters.galoisRepresentation k K G τ χ) hw
    have heq : rationalCharacters.galoisRepresentation k K G σ
        (rationalCharacters.galoisRepresentation k K G τ χ) =
      rationalCharacters.galoisRepresentation k K G (σ * τ) χ := by
        rw [map_mul, Module.End.mul_apply]
    rw [heq] at hh
    exact Submodule.mem_iSup_of_mem (σ * τ) hh
  · simpa only [Pi.zero_def, map_zero] using (galoisOrbitSubspace ρ χ).zero_mem
  · intro v w hv hw
    simpa only [Pi.add_def, map_add] using (galoisOrbitSubspace ρ χ).add_mem hv hw

section Galois

variable [IsGalois k K]

/-- In an original irreducible representation, the orbit sum of any nonzero
weight space is the whole extended coordinate space. -/
theorem galoisOrbitSubspace_eq_top_of_irreducible (ρ : MatrixRepresentation G n)
    (hρ : ρ.IsIrreducible) (χ : rationalCharacters G₁)
    (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥) :
    galoisOrbitSubspace ρ χ = ⊤ := by
  let W := galoisOrbitSubspace ρ χ
  have hW := isStableSubspace_galoisOrbitSubspace ρ χ
  have hWG := isGaloisStable_galoisOrbitSubspace ρ χ
  have hrec : scalarExtension (descend (k := k) W) = W := scalarExtension_descend W hWG
  have hχW : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≤ W := by
    have hh := le_iSup (fun σ : Γ => (ρ.baseChange (algebraBaseMap k K)).characterSpace
      (rationalCharacters.galoisRepresentation k K G σ χ)) (1 : Γ)
    change (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≤
      ⨆ σ : Γ, (ρ.baseChange (algebraBaseMap k K)).characterSpace
        (rationalCharacters.galoisRepresentation k K G σ χ)
    simpa only [map_one, Module.End.one_apply] using hh
  rcases hρ.2 (descend (k := k) W) hW.descend with hzero | htop
  · rw [hzero, scalarExtension_bot] at hrec
    exact False.elim (hχ (le_bot_iff.mp (hχW.trans hrec.symm.le)))
  · rw [htop, scalarExtension_top] at hrec
    exact hrec.symm

/-- Whenever actual character spaces span after a Galois field extension, the
weights of an original irreducible representation form exactly one Galois orbit. -/
theorem exists_weights_eq_galoisOrbit_of_irreducible (ρ : MatrixRepresentation G n)
    (hρ : ρ.IsIrreducible)
    (hspan : (⨆ χ : rationalCharacters G₁,
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) = ⊤) :
    ∃ χ : rationalCharacters G₁,
      {ψ | (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥} =
        Set.range (fun σ : Γ => rationalCharacters.galoisRepresentation k K G σ χ) := by
  have hex : ∃ χ : rationalCharacters G₁,
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule K (n → K)) = ⊥ := by
      rw [← hspan]
      simp only [h, iSup_bot]
    let := hρ.1
    obtain ⟨v, hv⟩ := exists_ne (0 : n → k)
    have hz : extend (K := K) v = 0 := by
      have hm : extend (K := K) v ∈ (⊤ : Submodule K (n → K)) := by trivial
      rwa [htop] at hm
    apply hv
    ext i
    apply (algebraMap k K).injective
    simpa only [extend_apply, Pi.zero_apply, map_zero] using congrFun hz i
  obtain ⟨χ, hχ⟩ := hex
  refine ⟨χ, ?_⟩
  ext ψ
  constructor
  · intro hψ
    by_contra hout
    have hdiff (σ : Γ) : rationalCharacters.galoisRepresentation k K G σ χ ≠ ψ := by
      intro hh
      exact hout ⟨σ, hh⟩
    have hle : galoisOrbitSubspace ρ χ ≤
        ⨆ (ξ : rationalCharacters G₁) (_ : ξ ≠ ψ),
          (ρ.baseChange (algebraBaseMap k K)).characterSpace ξ := by
      apply iSup_le
      intro σ
      exact le_iSup_of_le _ (le_iSup_of_le (hdiff σ) le_rfl)
    have hd := (iSupIndep_def.mp
      ((ρ.baseChange (algebraBaseMap k K)).characterSpace_iSupIndep) ψ).mono_right hle
    rw [galoisOrbitSubspace_eq_top_of_irreducible ρ hρ χ hχ, disjoint_top] at hd
    exact hψ hd
  · rintro ⟨σ, rfl⟩
    exact characterSpace_galois_ne_bot ρ χ hχ σ

end Galois

/-- The exact single-orbit weight conclusion for irreducible representations
of any affine group of multiplicative type over any separable closure. -/
theorem exists_weights_eq_galoisOrbit_of_isMultiplicativeType
    [IsSepClosure k K] (ρ : MatrixRepresentation G n) (hG : IsMultiplicativeType G)
    (hρ : ρ.IsIrreducible) :
    ∃ χ : rationalCharacters G₁,
      {ψ | (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥} =
        Set.range (fun σ : Γ => rationalCharacters.galoisRepresentation k K G σ χ) := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
    k K G hG
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
  let := hΛ
  let := hfg
  apply exists_weights_eq_galoisOrbit_of_irreducible ρ hρ
  exact iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e _

end Langlands.GroupScheme.MatrixRepresentation
