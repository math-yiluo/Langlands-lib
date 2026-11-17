import Langlands.GroupScheme.Composition.IsotropicCayleyAutomorphismRankStatement
import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualIndices
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound

/-! # Actual Cayley presentations of type-G2 groups and a conditional local exclusion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual simply connected absolutely almost-simple group with its
entire Cartan matrix numbered as G2 realizes the full algebra automorphism
functor of an actual Cayley datum. This general statement is unproved. -/
def TypeG2CayleyPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 2),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) →
      ∃ (c : CayleyDatum K)
        (iG : G ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)),
        c.IsAutomorphismRepresentation iG

section Local

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every eight-dimensional Cayley norm over a nonarchimedean local field
has an actual nonzero zero vector. This uses the proved quadratic
anisotropic dimension bound and no structural group premise. -/
theorem CayleyDatum.exists_nonzero_norm_eq_zero (c : CayleyDatum K) :
    ∃ x : CayleyVector K, x ≠ 0 ∧ c.norm x = 0 := by
  apply c.norm.not_anisotropic_iff_exists.mp
  intro hn
  have hdim :=
    Langlands.localQuadraticAnisotropicDimensionBound K (CayleyVector K) c.norm hn
  have hfin : Module.finrank K (CayleyVector K) = 8 := by
    simp [CayleyVector]
  rw [hfin] at hdim
  omega

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The two general Cayley premises imply split rank two for every actual
local type-G2 group in the presentation's scope. -/
theorem localTypeG2_splitRank_eq_two_of_cayleyStructure
    (hpresentation : TypeG2CayleyPresentationStatement.{u})
    (hautomorphismRank : IsotropicCayleyAutomorphismRankStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 2)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hG2 : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) :
    splitRank G = 2 := by
  obtain ⟨c, iG, hc⟩ := hpresentation K G d e hsc has hG2
  exact hautomorphismRank K c G iG hc c.exists_nonzero_norm_eq_zero

/-- The two unproved general Cayley premises conditionally exclude local
split rank one in actual type G2. -/
theorem localRankOneTypeG2_false_of_cayleyStructure
    (hpresentation : TypeG2CayleyPresentationStatement.{u})
    (hautomorphismRank : IsotropicCayleyAutomorphismRankStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 2)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hG2 : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b))
    (hrank : splitRank G = 1) : False := by
  have htwo := localTypeG2_splitRank_eq_two_of_cayleyStructure
    hpresentation hautomorphismRank d e hsc has hG2
  rw [hrank] at htwo
  norm_num at htwo

/-- The exact rank-one G2 residual predicate is excluded under the two
general Cayley premises, with no alteration to its markings or star action. -/
theorem localRankOne_not_hasG2Index_of_cayleyStructure
    (hpresentation : TypeG2CayleyPresentationStatement.{u})
    (hautomorphismRank : IsotropicCayleyAutomorphismRankStatement.{u})
    (d : TitsIndexData G) (hsc : IsSimplyConnected G)
    (has : IsAbsolutelyAlmostSimple G) (hrank : splitRank G = 1) :
    ¬ d.HasRankOneG2Index := by
  rintro ⟨⟨e, hnumbering⟩, _⟩
  exact localRankOneTypeG2_false_of_cayleyStructure
    hpresentation hautomorphismRank d e hsc has hnumbering.1 hrank

end Local

end Langlands.GroupScheme
