import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.AdicCompletion

/-! # Lifting actual affine smooth scheme points over adically complete rings -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

/-- Smoothness of the actual structure map makes the canonical coordinate algebra smooth. -/
theorem smooth_affineCoordinateRing [Smooth X.hom] :
    Algebra.Smooth R (AffineCoordinateRing R X) := by
  have h : Smooth (Spec.algebraMap R (AffineCoordinateRing R X)) := by
    rw [affineCoordinateSpecMap]
    let : IsIso X.left.isoSpec.inv := inferInstance
    exact smooth_comp X.left.isoSpec.inv X.hom
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

/-- Every point modulo an ideal of an adically complete coefficient algebra lifts to an
actual point of an affine smooth scheme, with the specified reduction unchanged. -/
theorem surjective_changeRing_of_isAdicComplete [Smooth X.hom]
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [IsAdicComplete I S] :
    Function.Surjective (fun p : RingPoint R X S =>
      p.changeRing (Ideal.Quotient.mkₐ R I)) := by
  let := smooth_affineCoordinateRing R X
  intro p₀
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (affineSchemePointEquiv R X (S ⧸ I) p₀).toAlgHom
  refine ⟨(affineSchemePointEquiv R X S).symm (AlgPoint.ofAlgHom g), ?_⟩
  apply (affineSchemePointEquiv R X (S ⧸ I)).injective
  apply AlgPoint.ext
  intro a
  have h := affineSchemePointEquiv_changeRing R X S (S ⧸ I) (Ideal.Quotient.mkₐ R I)
    ((affineSchemePointEquiv R X S).symm (AlgPoint.ofAlgHom g))
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun f : AffineCoordinateRing R X →ₐ[R] S ⧸ I => f a) (h.trans hg)

/-- A chosen actual point lifting the specified quotient-valued point. -/
def adicPointLift [Smooth X.hom]
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [IsAdicComplete I S]
    (p₀ : RingPoint R X (S ⧸ I)) : RingPoint R X S :=
  (surjective_changeRing_of_isAdicComplete R X S I p₀).choose

/-- The chosen actual lift reduces to the originally specified point. -/
@[simp] theorem adicPointLift_changeRing [Smooth X.hom]
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [IsAdicComplete I S]
    (p₀ : RingPoint R X (S ⧸ I)) :
    (adicPointLift R X S I p₀).changeRing (Ideal.Quotient.mkₐ R I) = p₀ :=
  (surjective_changeRing_of_isAdicComplete R X S I p₀).choose_spec

/-- A residue-valued point suffices for a section over an adically complete base. -/
theorem nonempty_ringPoint_of_quotient [Smooth X.hom]
    (I : Ideal R) [IsAdicComplete I R] (h : Nonempty (RingPoint R X (R ⧸ I))) :
    Nonempty (RingPoint R X R) := by
  obtain ⟨p₀⟩ := h
  obtain ⟨p, -⟩ := surjective_changeRing_of_isAdicComplete R X R I p₀
  exact ⟨p⟩

end Langlands.AlgebraicGeometry.PointTopology
