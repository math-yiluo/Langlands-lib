import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Langlands.GroupScheme.SimplyConnected.StarFixedWeights
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField
import Langlands.GroupScheme.SimplyConnected.TypeD4CentralCharacters

/-! # The coset sum of a fundamental weight over its simple-vertex field -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The full star action on simple vertices, as an action. -/
abbrev vertexStarAction : MulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K) d.Vertex where
  smul := d.star
  one_smul := d.star_one
  mul_smul := d.star_mul

/-- A vertex stabilizer has finite index, the size of the vertex orbit. -/
theorem starVertexStabilizer_finiteIndex (a : d.Vertex) :
    (d.starVertexStabilizer a).FiniteIndex := by
  let _ := d.vertexStarAction
  have hstab : d.starVertexStabilizer a =
      MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) a := rfl
  rw [Subgroup.finiteIndex_iff, hstab, MulAction.index_stabilizer]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, MulAction.mem_orbit_self a⟩ |>.ne'

/-- The actual simple-vertex field is a finite extension. -/
instance finiteDimensional_starVertexField (a : d.Vertex) :
    FiniteDimensional K (d.starVertexField a) := by
  have := d.starVertexStabilizer_finiteIndex a
  refine Module.finite_of_finrank_pos ?_
  rw [d.finrank_starVertexField]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

variable (hsc : IsSimplyConnected G)

/-- The star action permutes the actual fundamental weights as it permutes the simple
vertices. -/
theorem starAction_absoluteFundamentalCharacter
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    (d.pinning.starAction σ).val.weightEquiv (d.absoluteFundamentalCharacter hsc a) =
      d.absoluteFundamentalCharacter hsc (d.star σ a) :=
  d.absoluteFundamentalCharacter_star hsc σ a

/-- Distinct simple vertices have distinct fundamental weights. -/
theorem absoluteFundamentalCharacter_injective :
    Function.Injective (d.absoluteFundamentalCharacter hsc) :=
  (Langlands.RootDatum.fundamentalWeightBasis d.pinning.rootDatum d.pinning.base
    (d.pinning_corootSpan_eq_top hsc)).injective

/-- Stabilizer comparison: an automorphism fixes the fundamental weight of a vertex under
the star action exactly when it fixes the vertex. -/
theorem starAction_absoluteFundamentalCharacter_eq_iff
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) :
    (d.pinning.starAction σ).val.weightEquiv (d.absoluteFundamentalCharacter hsc a) =
        d.absoluteFundamentalCharacter hsc a ↔ d.star σ a = a := by
  rw [d.starAction_absoluteFundamentalCharacter hsc,
    (d.absoluteFundamentalCharacter_injective hsc).eq_iff]

/-- Stabilizer comparison: the star stabilizer of the fundamental weight of a vertex is the
star stabilizer of the vertex. -/
theorem equivStabilizer_absoluteFundamentalCharacter (a : d.Vertex) :
    equivStabilizer d.pinning.starWeightHom (d.absoluteFundamentalCharacter hsc a) =
      d.starVertexStabilizer a := by
  ext σ
  exact d.starAction_absoluteFundamentalCharacter_eq_iff hsc σ a

/-- The subgroup fixing the simple-vertex field of `a` is the star stabilizer of the
fundamental weight of `a`. -/
theorem starVertexField_fixingSubgroup_eq_equivStabilizer (a : d.Vertex) :
    (d.starVertexField a).fixingSubgroup =
      equivStabilizer d.pinning.starWeightHom (d.absoluteFundamentalCharacter hsc a) := by
  rw [d.equivStabilizer_absoluteFundamentalCharacter hsc, d.starVertexField_fixingSubgroup]

/-- The fundamental weight of a vertex is fixed by the subgroup fixing its vertex field. -/
theorem absoluteFundamentalCharacter_mem_fixedWeights (a : d.Vertex) :
    d.absoluteFundamentalCharacter hsc a ∈
      d.pinning.fixedWeights (d.starVertexField a).fixingSubgroup := by
  intro σ hσ
  rw [d.starVertexField_fixingSubgroup] at hσ
  exact (d.starAction_absoluteFundamentalCharacter_eq_iff hsc σ a).mpr hσ

/-- The star orbit of the fundamental weight of `a` is the image of the vertex orbit
of `a`. -/
theorem range_starAction_absoluteFundamentalCharacter (a : d.Vertex) :
    Set.range (fun σ : SeparableClosure K ≃ₐ[K] SeparableClosure K =>
        (d.pinning.starAction σ).val.weightEquiv (d.absoluteFundamentalCharacter hsc a)) =
      d.absoluteFundamentalCharacter hsc ''
        {b : d.Vertex | ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = b} := by
  ext mu
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨d.star σ a, ⟨σ, rfl⟩, (d.starAction_absoluteFundamentalCharacter hsc σ a).symm⟩
  · rintro ⟨b, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, d.starAction_absoluteFundamentalCharacter hsc σ a⟩

/-- Vertex-field specialization: the coset sum of the fundamental weight of a vertex, for the
actual simple-vertex field of that vertex, is the sum of the actual fundamental weights over
the full star orbit of the vertex, each vertex counted once. -/
theorem cosetSum_starVertexField (a : d.Vertex) :
    d.pinning.cosetSum (d.starVertexField a) (d.absoluteFundamentalCharacter hsc a) =
      ∑ᶠ b ∈ {b : d.Vertex | ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
        d.star σ a = b}, d.absoluteFundamentalCharacter hsc b := by
  rw [GaloisPinningData.cosetSum_eq_finsum_orbit
      (d.starVertexField_fixingSubgroup_eq_equivStabilizer hsc a),
    d.range_starAction_absoluteFundamentalCharacter hsc a]
  exact finsum_mem_image (f := fun mu : characterLattice d.pinning.toSplitPinning.torus => mu)
    (d.absoluteFundamentalCharacter_injective hsc).injOn

end TitsIndexData

end Langlands.GroupScheme
