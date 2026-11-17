import Langlands.GroupScheme.MatrixRepresentation.IrreducibleWeightOrbit
import Langlands.LinearAlgebra.SubgroupFixedVectors

/-! # Stabilizer-fixed character lines in original irreducible representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The sum of all coefficientwise conjugates of a vector's line. -/
def orbitLineSubspace (v : n → K) : Submodule K (n → K) :=
  ⨆ σ : K ≃ₐ[k] K, Submodule.span K ({fun i => σ (v i)} : Set (n → K))

omit [Fintype n] [DecidableEq n] in
/-- The sum of conjugate lines is invariant under coefficientwise Galois action. -/
theorem isGaloisStable_orbitLineSubspace (v : n → K) :
    IsGaloisStable (k := k) (orbitLineSubspace (k := k) v) := by
  intro σ z hz
  refine Submodule.iSup_induction _ (motive := fun w =>
    (fun i => σ (w i)) ∈ orbitLineSubspace (k := k) v) hz ?_ ?_ ?_
  · intro τ w hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ha]
    have he : (fun i => σ ((a • (fun i => τ (v i))) i)) =
        σ a • (fun i => (σ * τ) (v i)) := by
      funext i
      exact map_mul σ a (τ (v i))
    rw [he]
    exact Submodule.mem_iSup_of_mem (σ * τ)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · simpa only [Pi.zero_def, map_zero] using
      (orbitLineSubspace (k := k) v).zero_mem
  · intro x y hx hy
    simpa only [Pi.add_def, map_add] using
      (orbitLineSubspace (k := k) v).add_mem hx hy

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

local notation "G₁" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "Γ" => K ≃ₐ[k] K

/-- A character vector's conjugate lines form an actual stable subspace. -/
theorem isStableSubspace_orbitLineSubspace (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G₁) {v : n → K}
    (hv : v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) :
    (ρ.baseChange (algebraBaseMap k K)).IsStableSubspace
      (orbitLineSubspace (k := k) v) := by
  apply IsStableSubspace.iSup
  intro σ
  apply isStableSubspace_of_le_characterSpace _
    (rationalCharacters.galoisRepresentation k K G σ χ)
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr
    (conjugate_mem_characterSpace_baseChange ρ σ χ hv)

variable [IsGalois k K]

/-- In an original irreducible representation, the conjugate lines of any
nonzero geometric character vector span the entire scalar extension. -/
theorem orbitLineSubspace_eq_top_of_irreducible (ρ : MatrixRepresentation G n)
    (hρ : ρ.IsIrreducible) (χ : rationalCharacters G₁) {v : n → K}
    (hv : v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) (hv0 : v ≠ 0) :
    orbitLineSubspace (k := k) v = ⊤ := by
  let W := orbitLineSubspace (k := k) v
  have hW := isStableSubspace_orbitLineSubspace ρ χ hv
  have hWG := isGaloisStable_orbitLineSubspace (k := k) v
  have hrec : scalarExtension (descend (k := k) W) = W := scalarExtension_descend W hWG
  have hvW : v ∈ W := by
    change v ∈ ⨆ σ : Γ, Submodule.span K ({fun i => σ (v i)} : Set (n → K))
    apply Submodule.mem_iSup_of_mem (1 : Γ)
    change v ∈ Submodule.span K ({v} : Set (n → K))
    exact Submodule.mem_span_singleton_self v
  rcases hρ.2 (descend (k := k) W) hW.descend with hzero | htop
  · rw [hzero, scalarExtension_bot] at hrec
    exact False.elim (hv0 (by simpa only [← hrec, Submodule.mem_bot] using hvW))
  · rw [htop, scalarExtension_top] at hrec
    exact hrec.symm

/-- A nonzero weight space of an original irreducible representation is a
stabilizer-fixed line, with a chosen coordinate normalized to one. -/
theorem exists_normalized_galois_characterLine (ρ : MatrixRepresentation G n)
    (hρ : ρ.IsIrreducible) (χ : rationalCharacters G₁)
    (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥)
    (H : Subgroup Γ)
    (hH : ∀ σ : Γ, σ ∈ H ↔ rationalCharacters.galoisRepresentation k K G σ χ = χ) :
    ∃ (v : n → K) (j : n), v j = 1 ∧
      (∀ σ ∈ H, (fun i => σ (v i)) = v) ∧
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ =
        Submodule.span K ({v} : Set (n → K)) ∧
      orbitLineSubspace (k := k) v = ⊤ := by
  have hstable : ∀ σ ∈ H,
      ∀ z ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ,
        (fun i => σ (z i)) ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ := by
    intro σ hσ z hz
    have h := conjugate_mem_characterSpace_baseChange ρ σ χ hz
    rwa [(hH σ).mp hσ] at h
  obtain ⟨v, j, hv, hvj, hfixed⟩ :=
    Langlands.LinearAlgebra.SubgroupFixedVectors.exists_fixed_pi H
      ((ρ.baseChange (algebraBaseMap k K)).characterSpace χ) hstable hχ
  have hv0 : v ≠ 0 := by
    intro hz
    have h := congrFun hz j
    rw [hvj] at h
    exact one_ne_zero h
  have htop := orbitLineSubspace_eq_top_of_irreducible ρ hρ χ hv hv0
  refine ⟨v, j, hvj, hfixed, ?_, htop⟩
  apply le_antisymm
  · have hproj : orbitLineSubspace (k := k) v ≤
        (Submodule.span K ({v} : Set (n → K))).comap
          ((ρ.baseChange (algebraBaseMap k K)).characterProjector χ) := by
      apply iSup_le
      intro σ
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      change (ρ.baseChange (algebraBaseMap k K)).characterProjector χ
        (fun i => σ (v i)) ∈ Submodule.span K ({v} : Set (n → K))
      rw [characterProjector_of_mem _ χ
        (rationalCharacters.galoisRepresentation k K G σ χ)
        (conjugate_mem_characterSpace_baseChange ρ σ χ hv)]
      by_cases heq : rationalCharacters.galoisRepresentation k K G σ χ = χ
      · rw [ite_eq_left heq, hfixed σ ((hH σ).mpr heq)]
        exact Submodule.mem_span_singleton_self v
      · rw [ite_eq_right heq]
        exact Submodule.zero_mem _
    intro z hz
    have hh : (ρ.baseChange (algebraBaseMap k K)).characterProjector χ z ∈
        Submodule.span K ({v} : Set (n → K)) := hproj (by rw [htop]; trivial)
    simpa only [characterProjector_of_mem _ χ χ hz, ite_true] using hh
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv

end Langlands.GroupScheme.MatrixRepresentation
