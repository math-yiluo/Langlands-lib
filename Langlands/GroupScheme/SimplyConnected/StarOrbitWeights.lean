import Langlands.GroupScheme.SimplyConnected.CenterOrbitCharacters

/-! # Integral fundamental weights summed over full star orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

/-- The full star action carries each actual integral fundamental weight by
the corresponding simple-vertex permutation. -/
theorem absoluteFundamentalCharacter_star
    (hsc : IsSimplyConnected G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    (d.pinning.starAction σ).val.weightEquiv
        (d.absoluteFundamentalCharacter hsc a) =
      d.absoluteFundamentalCharacter hsc (d.star σ a) := by
  exact Langlands.RootDatum.fundamentalWeightBasis_aut
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc)
    (d.pinning.starAction σ).val (d.pinning.starAction σ).property a

/-- The sum of the actual integral fundamental weights over a full star
orbit, with each vertex counted once. -/
def absoluteOrbitWeight (hsc : IsSimplyConnected G) (a : d.Vertex) :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.pinning.torus) :=
  ∑ b ∈ d.starOrbitVertices a, d.absoluteFundamentalCharacter hsc b

/-- An orbit weight is fixed by the full star action on the actual integral
weight lattice. -/
theorem absoluteOrbitWeight_star
    (hsc : IsSimplyConnected G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    (d.pinning.starAction σ).val.weightEquiv (d.absoluteOrbitWeight hsc a) =
      d.absoluteOrbitWeight hsc a := by
  classical
  unfold absoluteOrbitWeight
  have hmap := map_sum (ι := d.Vertex) (d.pinning.starAction σ).val.weightEquiv.toLinearMap
  rw [LinearEquiv.coe_coe] at hmap
  simp only [hmap, d.absoluteFundamentalCharacter_star]
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

/-- Pointwise fixers of the actual vertex field fix the fundamental weight
for the star action in the original separable closure. -/
theorem absoluteFundamentalCharacter_star_fixedBy_vertexField
    (hsc : IsSimplyConnected G) (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hσ : ∀ x ∈ d.starVertexField a, σ x = x) :
    (d.pinning.starAction σ).val.weightEquiv
        (d.absoluteFundamentalCharacter hsc a) =
      d.absoluteFundamentalCharacter hsc a := by
  rw [d.absoluteFundamentalCharacter_star,
    (d.fixes_starVertexField_iff a σ).mp hσ]

/-- Restricting an orbit weight to the actual full geometric centre gives
the corresponding orbit character. -/
theorem absoluteOrbitWeight_comp_center
    (hsc : IsSimplyConnected G) (a : d.Vertex) :
    (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        d.toralCenter.torusMap ≫ d.absoluteOrbitWeight hsc a =
      d.centerOrbitCharacter hsc a := by
  classical
  unfold absoluteOrbitWeight centerOrbitCharacter
  simp only [Preadditive.comp_sum, centerFundamentalCharacter,
    centralFundamentalCharacter]

/-- At a globally fixed vertex the orbit weight is its fundamental weight. -/
theorem absoluteOrbitWeight_eq_of_fixed
    (hsc : IsSimplyConnected G) (a : d.Vertex)
    (ha : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) :
    d.absoluteOrbitWeight hsc a = d.absoluteFundamentalCharacter hsc a := by
  classical
  simp [absoluteOrbitWeight, d.starOrbitVertices_eq_singleton_of_fixed a ha]

/-- In the trialitarian D4 case a leaf-orbit weight is the actual integral
sum of the three fundamental leaf weights. -/
theorem absoluteOrbitWeight_D4_eq_leafWeightSum_of_no_fixed_leaf
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    d.absoluteOrbitWeight hsc a =
      Langlands.RootDatum.d4LeafWeightSum d.pinning.rootDatum d.pinning.base
        (d.pinning_corootSpan_eq_top hsc) e := by
  classical
  rw [absoluteOrbitWeight,
    d.starOrbitVertices_eq_D4_leaves_of_no_fixed_leaf e hD hno a ha]
  simp [Langlands.RootDatum.d4LeafWeightSum, absoluteFundamentalCharacter, add_assoc]

/-- Every leaf-orbit weight in the trialitarian D4 case lies in the actual
integral root lattice, without a Brauer obstruction premise. -/
theorem absoluteOrbitWeight_D4_mem_rootSpan_of_no_fixed_leaf
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a : d.Vertex) (ha : e a ≠ 1) :
    d.absoluteOrbitWeight hsc a ∈ d.pinning.rootDatum.rootSpan ℤ := by
  rw [d.absoluteOrbitWeight_D4_eq_leafWeightSum_of_no_fixed_leaf hsc e hD hno a ha]
  exact Langlands.RootDatum.d4LeafWeightSum_mem_rootSpan
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) e hD

end Langlands.GroupScheme.TitsIndexData
