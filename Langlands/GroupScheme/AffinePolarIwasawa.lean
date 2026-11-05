import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.Dynamic.ConjugatedParabolicPolarCover

/-! # A single polar compact subgroup covers all actual dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ComplexOrder

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false

variable {k S : Type u} [Field k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left] {d : ℕ}
  (ρ : MatrixRepresentation G (Fin d))

local instance affinePolarIwasawaPointTopology : TopologicalSpace (G.affinePoints (CommAlgCat.of k S)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k S)

/-- The constructed polar maximal compact subgroup covers every actual dynamic
parabolic, using the original evaluation topology. -/
theorem parabolic_mul_affineMaximalCompact_eq_univ
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ((Dynamic.parabolic χ).carrier (Dynamic.affineTest k S) :
      Set (G.affinePoints (CommAlgCat.of k S))) *
      ((ρ.affineMaximalCompact hρ hstar).val :
        Set (G.affinePoints (CommAlgCat.of k S))) = Set.univ := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  apply Dynamic.parabolic_mul_compact_eq_univ_of_star_hermitian ρ hstar χ
    (ρ.affineMaximalCompact hρ hstar).val (ρ.affineMaximalCompact hρ hstar).property.1
  intro x
  obtain ⟨z, hz, hpos⟩ := ρ.exists_affineUnitary_right_quotient_posDef hρ hstar x
  exact ⟨z, hz, hpos.isHermitian⟩

/-- Every actual representative has the same literal range-times-compact
covering, for the same constructed maximal compact subgroup. -/
theorem range_mul_affineMaximalCompact_eq_univ
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p) :
    Set.range (P.affinePointsTarget p (CommAlgCat.of k S)) *
      ((ρ.affineMaximalCompact hρ hstar).val :
        Set (G.affinePoints (CommAlgCat.of k S))) = Set.univ := by
  change ((SubgroupFunctor.range p).carrier (Dynamic.affineTest k S) :
    Set (G.affinePoints (CommAlgCat.of k S))) * _ = _
  rw [hP.2]
  exact ρ.parabolic_mul_affineMaximalCompact_eq_univ hρ hstar χ

/-- Construct one compact subgroup, maximal among all compact overgroups,
that covers every actual representative of every dynamic parabolic. -/
def affineDynamicIwasawa
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    {K : Subgroup (G.affinePoints (CommAlgCat.of k S)) //
      IsCompact (K : Set (G.affinePoints (CommAlgCat.of k S))) ∧
      (∀ L : Subgroup (G.affinePoints (CommAlgCat.of k S)),
        IsCompact (L : Set (G.affinePoints (CommAlgCat.of k S))) → K ≤ L → L = K) ∧
      ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
        (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        (Dynamic.parabolic χ).IsRepresentedBy p →
        Set.range (P.affinePointsTarget p (CommAlgCat.of k S)) *
          (K : Set (G.affinePoints (CommAlgCat.of k S))) = Set.univ} :=
  ⟨(ρ.affineMaximalCompact hρ hstar).val,
    (ρ.affineMaximalCompact hρ hstar).property.1,
    (ρ.affineMaximalCompact hρ hstar).property.2,
    fun χ _ p hP => ρ.range_mul_affineMaximalCompact_eq_univ hρ hstar χ p hP⟩

@[simp] theorem affineDynamicIwasawa_val
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    (ρ.affineDynamicIwasawa hρ hstar).val = ρ.affineUnitarySubgroup (S := S) := rfl

end Langlands.GroupScheme.MatrixRepresentation
