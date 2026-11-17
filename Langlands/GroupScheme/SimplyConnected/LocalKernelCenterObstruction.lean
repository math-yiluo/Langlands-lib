import Langlands.GroupScheme.SimplyConnected.TypeEKernelCenterMovementStatement
import Langlands.GroupScheme.NormOneCenterAutomorphismOppositeStatement
import Langlands.Algebra.LocalDivisionOppositeDegree

/-! # Conditional full-centre obstructions for local anisotropic kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual automorphism fixes the full scheme-theoretic centre
pointwise over every test scheme. -/
def AllAutomorphismsFixCenter {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  ∀ f : G ≅ G, AutomorphismFixesCenter f

/-- Full-centre rigidity is equivalent to absence of a centre-moving
automorphism. -/
theorem allAutomorphismsFixCenter_iff_not_hasCenterMovingAutomorphism
    {S : Scheme.{u}} (G : GroupScheme S) :
    AllAutomorphismsFixCenter G ↔ ¬ HasCenterMovingAutomorphism G := by
  classical
  simp only [AllAutomorphismsFixCenter, HasCenterMovingAutomorphism,
    not_exists, not_not]

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Given the norm-one automorphism classification prerequisite, every
automorphism of a local division norm-one model of degree greater than two
fixes its full scheme-theoretic centre. -/
theorem HasCentralDivisionNormOnePresentation.automorphismFixesCenter
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of K))} {degree : ℕ}
    (hmodel : HasCentralDivisionNormOnePresentation G degree)
    (hdegree : 2 < degree) (f : G ≅ G) : AutomorphismFixesCenter f := by
  obtain ⟨D, hD, hKD, hfd, hcentral, hdeg, ⟨e⟩⟩ := hmodel
  apply (AutomorphismFixesCenter.conjugate_iff e f).mp
  by_contra hf
  exact Langlands.not_hasAlgebraAntiEquivalence_of_two_lt
    (by simpa only [hdeg] using hdegree) (hclass K D ((e.symm.trans f).trans e) hf)

/-- Conditional full-centre rigidity for a local division norm-one
presentation of degree greater than two. -/
theorem HasCentralDivisionNormOnePresentation.allAutomorphismsFixCenter
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of K))} {degree : ℕ}
    (hmodel : HasCentralDivisionNormOnePresentation G degree)
    (hdegree : 2 < degree) : AllAutomorphismsFixCenter G :=
  fun f => hmodel.automorphismFixesCenter hclass hdegree f

/-- Under the same explicit prerequisite, a local division norm-one
presentation of degree greater than two has no centre-moving automorphism. -/
theorem HasCentralDivisionNormOnePresentation.not_hasCenterMovingAutomorphism
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of K))} {degree : ℕ}
    (hmodel : HasCentralDivisionNormOnePresentation G degree)
    (hdegree : 2 < degree) : ¬ HasCenterMovingAutomorphism G :=
  (allAutomorphismsFixCenter_iff_not_hasCenterMovingAutomorphism G).mp
    (hmodel.allAutomorphismsFixCenter hclass hdegree)

namespace TitsIndexData

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The degree-six actual E6 kernel model is incompatible with the two
explicit structural prerequisites over a local field. -/
theorem not_E6_branch_mark_of_centerMovement
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) (hstar : d.StarIsTrivial)
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) : False :=
  HasCentralDivisionNormOnePresentation.not_hasCenterMovingAutomorphism hclass
    (d.anisotropicKernel_divisionModel_of_E6_branch_mark e hsc h hstar) (by decide)
    (hmove K G d hsc has hrank hstar (Or.inl ⟨e, h⟩))

/-- The degree-seven actual E7 kernel model is incompatible with the two
explicit structural prerequisites over a local field. -/
theorem not_E7_branch_mark_of_centerMovement
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) (hstar : d.StarIsTrivial)
    (e : d.Vertex ≃ Fin 7)
    (h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e) : False :=
  HasCentralDivisionNormOnePresentation.not_hasCenterMovingAutomorphism hclass
    (d.anisotropicKernel_divisionModel_of_E7_branch_mark e hsc h hstar) (by decide)
    (hmove K G d hsc has hrank hstar (Or.inr ⟨e, h⟩))

end TitsIndexData

end Langlands.GroupScheme
