import Langlands.GroupScheme.SimplyConnected.TypeD4CenterCharacters
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField

/-! # Actual centre characters summed over full star orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

local instance : DecidableEq d.Vertex := Classical.decEq _

/-- The finite orbit of a simple vertex under the full absolute star action. -/
def starOrbitVertices (a : d.Vertex) : Finset d.Vertex := by
  classical
  letI := Fintype.ofFinite d.Vertex
  exact Finset.univ.filter (fun b =>
    ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = b)

@[simp] theorem mem_starOrbitVertices (a b : d.Vertex) :
    b ∈ d.starOrbitVertices a ↔
      ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = b := by
  classical
  simp [starOrbitVertices]

@[simp] theorem self_mem_starOrbitVertices (a : d.Vertex) :
    a ∈ d.starOrbitVertices a :=
  (d.mem_starOrbitVertices a a).mpr ⟨1, d.star_one a⟩

/-- Every element of the absolute Galois group permutes the same full orbit. -/
theorem star_mem_starOrbitVertices_iff
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a b : d.Vertex) :
    d.star σ b ∈ d.starOrbitVertices a ↔ b ∈ d.starOrbitVertices a := by
  simp only [mem_starOrbitVertices]
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨σ⁻¹ * τ, ?_⟩
    calc
      d.star (σ⁻¹ * τ) a = d.star σ⁻¹ (d.star σ b) := by
        rw [d.star_mul, hτ]
      _ = b := by rw [← d.star_mul, inv_mul_cancel, d.star_one]
  · rintro ⟨τ, hτ⟩
    exact ⟨σ * τ, by rw [d.star_mul, hτ]⟩

/-- Sum of the actual fundamental characters of the full geometric centre
over one full star orbit, counting each vertex once. -/
def centerOrbitCharacter (hsc : IsSimplyConnected G) (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.toralCenter.group) :=
  ∑ b ∈ d.starOrbitVertices a, d.centerFundamentalCharacter hsc b

/-- Orbit sums are fixed by the ordinary action of every absolute Galois
automorphism on the full geometric centre's actual character group. -/
theorem centerOrbitCharacter_galois
    (hsc : IsSimplyConnected G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    characterLattice.galoisRepresentation K (SeparableClosure K)
        d.toralCenter.group σ (d.centerOrbitCharacter hsc a) =
      d.centerOrbitCharacter hsc a := by
  classical
  unfold centerOrbitCharacter
  simp only [map_sum, d.centerFundamentalCharacter_galois]
  refine Finset.sum_bij (fun b _ => d.star σ b) ?_ ?_ ?_ ?_
  · intro b hb
    exact (d.star_mem_starOrbitVertices_iff σ a b).mpr hb
  · intro b hb c hc hbc
    exact (d.starPermutation σ).injective hbc
  · intro b hb
    refine ⟨d.star σ⁻¹ b, ?_, ?_⟩
    · exact (d.star_mem_starOrbitVertices_iff σ⁻¹ a b).mpr hb
    · rw [← d.star_mul, mul_inv_cancel, d.star_one]
  · intro b hb
    rfl

/-- The original fundamental centre character is fixed by every automorphism
fixing its vertex field pointwise. No character descent is asserted here. -/
theorem centerFundamentalCharacter_fixedBy_vertexField
    (hsc : IsSimplyConnected G) (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hσ : ∀ x ∈ d.starVertexField a, σ x = x) :
    characterLattice.galoisRepresentation K (SeparableClosure K)
        d.toralCenter.group σ (d.centerFundamentalCharacter hsc a) =
      d.centerFundamentalCharacter hsc a := by
  rw [d.centerFundamentalCharacter_galois,
    (d.fixes_starVertexField_iff a σ).mp hσ]

/-- A globally fixed vertex has a singleton orbit. -/
theorem starOrbitVertices_eq_singleton_of_fixed (a : d.Vertex)
    (ha : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) :
    d.starOrbitVertices a = {a} := by
  classical
  ext b
  simp only [mem_starOrbitVertices, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, hσ⟩
    exact hσ.symm.trans (ha σ)
  · intro hba
    exact ⟨1, (d.star_one a).trans hba.symm⟩

theorem centerOrbitCharacter_eq_of_fixed (hsc : IsSimplyConnected G) (a : d.Vertex)
    (ha : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) :
    d.centerOrbitCharacter hsc a = d.centerFundamentalCharacter hsc a := by
  classical
  simp [centerOrbitCharacter, d.starOrbitVertices_eq_singleton_of_fixed a ha]

/-- In the trialitarian D4 case the orbit of every leaf is exactly the three
leaves, expressed using the complete actual Cartan numbering. -/
theorem starOrbitVertices_eq_D4_leaves_of_no_fixed_leaf
    (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    d.starOrbitVertices a = {e.symm 0, e.symm 2, e.symm 3} := by
  classical
  have hleaf (b : d.Vertex) :
      b ∈ d.starOrbitVertices a ↔ e b ≠ 1 := by
    rw [d.mem_starOrbitVertices]
    constructor
    · rintro ⟨σ, rfl⟩ hb
      have hc : d.star σ (e.symm 1) = e.symm 1 :=
        d.star_fixes_center_of_D (by decide) e hD σ _ (by simp)
      have heq : d.star σ a = d.star σ (e.symm 1) := by
        rw [hc]
        exact e.injective (hb.trans (e.apply_symm_apply 1).symm)
      exact ha (by simpa using congrArg e ((d.starPermutation σ).injective heq))
    · intro hb
      exact d.star_transitive_on_D4_leaves_of_no_fixed_leaf e hD hno a b ha hb
  ext b
  rw [hleaf]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hb
    have hcases : e b = 0 ∨ e b = 2 ∨ e b = 3 := by
      have hlt := (e b).isLt
      omega
    simpa only [← Equiv.eq_symm_apply] using hcases
  · rintro (rfl | rfl | rfl) <;> simp

/-- The actual centre character summed over a trialitarian D4 leaf orbit is
zero. This uses no Tits-algebra or Brauer comparison. -/
theorem centerOrbitCharacter_D4_eq_zero_of_no_fixed_leaf
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    d.centerOrbitCharacter hsc a = 0 := by
  classical
  rw [centerOrbitCharacter,
    d.starOrbitVertices_eq_D4_leaves_of_no_fixed_leaf e hD hno a ha]
  simpa [add_assoc, e.injective.eq_iff] using
    d.centerFundamentalCharacter_D4_leaf_sum_eq_zero hsc e hD

end Langlands.GroupScheme.TitsIndexData
