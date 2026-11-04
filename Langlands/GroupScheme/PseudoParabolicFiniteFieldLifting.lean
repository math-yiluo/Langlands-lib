import Langlands.GroupScheme.HomogeneousQuotientRationalPoints
import Langlands.GroupScheme.FiniteFieldTorsorPointProof
import Langlands.GroupScheme.PseudoParabolicStructureProof

/-! # Rational lifting for supplied pseudo-parabolic quotients over finite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

variable (k : Type u) [Field k] [Finite k]
variable (G P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G)
variable [IsAffineHom G.X.hom]
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]

/-- Every rational point of the supplied exact pseudo-parabolic quotient over
 a finite field lifts under the original projection. -/
theorem rational_lifts_pseudo_finiteField
    (hi : IsPseudoParabolicSubgroup i)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    ∀ p : RationalPoint k Q, ∃ g : RationalPoint k G.X, g ≫ q = p := by
  exact rational_lifts_pseudo_of_finite_torsor_and_connected k G P i q hi
    hi.source_connectedSpace hfib finiteFieldTorsorPointStatement

/-- A chosen actual rational lift under the supplied finite-field quotient. -/
def rationalLiftPseudoFiniteField
    (hi : IsPseudoParabolicSubgroup i)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (p : RationalPoint k Q) : RationalPoint k G.X :=
  Classical.choose (rational_lifts_pseudo_finiteField k G P i q hi hfib p)

@[reassoc]
theorem rationalLiftPseudoFiniteField_comp
    (hi : IsPseudoParabolicSubgroup i)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (p : RationalPoint k Q) :
    rationalLiftPseudoFiniteField k G P i q hi hfib p ≫ q = p :=
  Classical.choose_spec (rational_lifts_pseudo_finiteField k G P i q hi hfib p)

end Langlands.GroupScheme.HomogeneousQuotient
