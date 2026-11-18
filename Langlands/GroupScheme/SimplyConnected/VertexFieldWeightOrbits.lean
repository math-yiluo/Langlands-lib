import Langlands.GroupScheme.SimplyConnected.StarVertexFieldWeights
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Actual vertex fields and fundamental-weight orbit sums -/

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

/-- Equality of transported actual fundamental weights is exactly equality
of their star vertices. -/
theorem absoluteFundamentalCharacter_star_eq_iff
    (hsc : IsSimplyConnected G)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a b : d.Vertex) :
    (d.pinning.starAction σ).val.weightEquiv
        (d.absoluteFundamentalCharacter hsc a) =
        d.absoluteFundamentalCharacter hsc b ↔
      d.star σ a = b := by
  rw [d.absoluteFundamentalCharacter_star]
  exact (d.absoluteFundamentalCharacter_injective hsc).eq_iff

/-- The actual vertex field is also the field of definition of its integral
fundamental weight for the full star action in the original closure. -/
theorem absoluteFundamentalCharacter_star_fixed_iff_fixes_vertexField
    (hsc : IsSimplyConnected G) (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (d.pinning.starAction σ).val.weightEquiv
        (d.absoluteFundamentalCharacter hsc a) =
        d.absoluteFundamentalCharacter hsc a ↔
      ∀ x ∈ d.starVertexField a, σ x = x := by
  rw [d.absoluteFundamentalCharacter_star_eq_iff hsc σ a a,
    d.fixes_starVertexField_iff a σ]

/-- Left cosets of the actual vertex stabilizer are exactly the vertices
in its full star orbit. No normality of the stabilizer is required. -/
def starVertexCosetOrbitEquiv (a : d.Vertex) :
    ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ d.starVertexStabilizer a) ≃
      ↥(d.starOrbitVertices a) := by
  classical
  let Γ := SeparableClosure K ≃ₐ[K] SeparableClosure K
  letI : MulAction Γ d.Vertex := {
    smul := d.star
    one_smul := d.star_one
    mul_smul := d.star_mul }
  change (Γ ⧸ MulAction.stabilizer Γ a) ≃ ↥(d.starOrbitVertices a)
  refine (MulAction.orbitEquivQuotientStabilizer Γ a).symm.trans
    (Equiv.subtypeEquivRight fun b => ?_)
  rw [MulAction.mem_orbit_iff, d.mem_starOrbitVertices]
  rfl

@[simp] theorem starVertexCosetOrbitEquiv_mk (a : d.Vertex)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (d.starVertexCosetOrbitEquiv a (QuotientGroup.mk σ)).val = d.star σ a := by
  rfl

/-- The quotient by an actual vertex stabilizer is finite, even though the
absolute Galois group itself need not be finite. -/
instance finite_starVertexQuotient (a : d.Vertex) :
    Finite ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸
      d.starVertexStabilizer a) :=
  Finite.of_equiv ↥(d.starOrbitVertices a) (d.starVertexCosetOrbitEquiv a).symm

/-- The degree of any actual vertex field equals the number of vertices
in its full star orbit. -/
theorem finrank_starVertexField_eq_card_starOrbitVertices (a : d.Vertex) :
    Module.finrank K (d.starVertexField a) = (d.starOrbitVertices a).card := by
  rw [d.finrank_starVertexField]
  change Nat.card ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸
    d.starVertexStabilizer a) = _
  rw [Nat.card_congr (d.starVertexCosetOrbitEquiv a)]
  exact Nat.card_eq_finsetCard _

/-- Summing actual fundamental weights over vertex-stabilizer cosets counts
each full-star-orbit weight exactly once. -/
theorem sum_starVertexCosets_eq_absoluteOrbitWeight
    (hsc : IsSimplyConnected G) (a : d.Vertex)
    [Fintype ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸
      d.starVertexStabilizer a)] :
    (∑ q : (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸
        d.starVertexStabilizer a,
      d.absoluteFundamentalCharacter hsc (d.starVertexCosetOrbitEquiv a q).val) =
      d.absoluteOrbitWeight hsc a := by
  classical
  calc
    _ = ∑ b : ↥(d.starOrbitVertices a), d.absoluteFundamentalCharacter hsc b.val :=
      Fintype.sum_equiv (d.starVertexCosetOrbitEquiv a) _ _ (fun _ => rfl)
    _ = d.absoluteOrbitWeight hsc a := by
      exact Finset.sum_coe_sort (d.starOrbitVertices a) (d.absoluteFundamentalCharacter hsc)

end Langlands.GroupScheme.TitsIndexData
