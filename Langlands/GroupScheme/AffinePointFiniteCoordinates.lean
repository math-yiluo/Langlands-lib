import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Mathlib.Topology.Bases

/-! # Finite coordinates on actual affine group-scheme points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]
variable (A : CommAlgCat.{u} R)

/-- The existing affine scheme/algebra comparison evaluates each global function
at the actual group-scheme point. -/
theorem affineSchemePointEquiv_evaluation (x : G.affinePoints A)
    (a : AffineCoordinateRing R G.X) :
    affineSchemePointEquiv R G.X A x a = G.affinePointEvaluation A x a := by
  have h : CommRingCat.ofHom
      (affineSchemePointEquiv R G.X A x).toAlgHom.toRingHom =
        x.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    apply Spec.map_injective
    rw [affineSchemePointEquiv_spec R A x, Spec.map_comp, ← Scheme.isoSpec_Spec_hom,
      ← Scheme.isoSpec_hom_naturality]
    rfl
  exact congrArg (fun f => f.hom a) h

variable [TopologicalSpace A]

/-- The actual group-scheme point space is the existing global-section
algebra-point space, with its evaluation topology. -/
def affinePointsAlgebraHomeomorph :
    G.affinePoints A ≃ₜ AlgPoint R (AffineCoordinateRing R G.X) A where
  toEquiv := affineSchemePointEquiv R G.X A
  continuous_toFun := by
    apply (AlgPoint.continuous_iff _).mpr
    intro a
    change Continuous (fun x : G.affinePoints A => affineSchemePointEquiv R G.X A x a)
    simp_rw [G.affineSchemePointEquiv_evaluation A]
    exact G.continuous_affinePointEvaluation A a
  continuous_invFun := by
    apply (G.continuous_affinePoints_iff A _).mpr
    intro a
    have h (p : AlgPoint R (AffineCoordinateRing R G.X) A) :
        G.affinePointEvaluation A ((affineSchemePointEquiv R G.X A).symm p) a = p a := by
      rw [← affineSchemePointEquiv_evaluation, Equiv.apply_symm_apply]
    change Continuous (fun p : AlgPoint R (AffineCoordinateRing R G.X) A =>
      G.affinePointEvaluation A ((affineSchemePointEquiv R G.X A).symm p) a)
    simp_rw [h]
    exact AlgPoint.continuous_eval (R := R) (A := AffineCoordinateRing R G.X) (S := A) a

@[simp] theorem affinePointsAlgebraHomeomorph_apply
    (x : G.affinePoints A) (a : AffineCoordinateRing R G.X) :
    G.affinePointsAlgebraHomeomorph A x a = G.affinePointEvaluation A x a :=
  G.affineSchemePointEquiv_evaluation A x a

variable [IsTopologicalRing A]

/-- Any finite algebra-generating family induces the canonical point topology. -/
theorem isEmbedding_affinePointFiniteEvaluation (n : ℕ)
    (a : Fin n → AffineCoordinateRing R G.X)
    (ha : Algebra.adjoin R (Set.range a) = ⊤) :
    IsEmbedding (fun (x : G.affinePoints A) (i : Fin n) =>
      G.affinePointEvaluation A x (a i)) := by
  have h := (finiteCoordinateEmbedding_proof R (AffineCoordinateRing R G.X) A n a ha).comp
    (G.affinePointsAlgebraHomeomorph A).isEmbedding
  simpa only [Function.comp_def, affinePointsAlgebraHomeomorph_apply] using h

/-- Over Hausdorff coefficients the finite-coordinate image is closed. -/
theorem isClosedEmbedding_affinePointFiniteEvaluation [T2Space A] (n : ℕ)
    (a : Fin n → AffineCoordinateRing R G.X)
    (ha : Algebra.adjoin R (Set.range a) = ⊤) :
    IsClosedEmbedding (fun (x : G.affinePoints A) (i : Fin n) =>
      G.affinePointEvaluation A x (a i)) := by
  have h := (finiteCoordinateClosedEmbedding_proof R (AffineCoordinateRing R G.X) A n a ha).comp
    (G.affinePointsAlgebraHomeomorph A).isClosedEmbedding
  simpa only [Function.comp_def, affinePointsAlgebraHomeomorph_apply] using h

/-- Finite-type affine group-scheme points over locally compact Hausdorff
coefficients are locally compact. -/
instance affinePointsLocallyCompactSpace [LocallyOfFiniteType G.X.hom]
    [T2Space A] [LocallyCompactSpace A] : LocallyCompactSpace (G.affinePoints A) := by
  have : LocallyCompactSpace (AlgPoint R (AffineCoordinateRing R G.X) A) :=
    affineLocalCompactness_proof R (AffineCoordinateRing R G.X) A inferInstance
  exact (G.affinePointsAlgebraHomeomorph A).isClosedEmbedding.locallyCompactSpace

/-- Finite-type affine group-scheme points over second-countable coefficients
are second countable. Hausdorffness is not needed. -/
instance affinePointsSecondCountableTopology [LocallyOfFiniteType G.X.hom]
    [SecondCountableTopology A] : SecondCountableTopology (G.affinePoints A) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R (AffineCoordinateRing R G.X))
  have h := (AlgPoint.polynomialPointHomeomorph (R := R) (S := A) (Fin n)).isEmbedding.comp
    (AlgPoint.isEmbedding_precomp_of_surjective f hf)
  exact (h.comp (G.affinePointsAlgebraHomeomorph A).isEmbedding).secondCountableTopology

end Langlands.GroupScheme
