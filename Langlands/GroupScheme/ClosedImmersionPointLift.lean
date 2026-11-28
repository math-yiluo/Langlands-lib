import Langlands.GroupScheme.AffinePointTopology
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Points that factor through a closed immersion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine H.X.left] [IsAffine G.X.left]

/-- A point of an affine group scheme `G` at which every regular function vanishing on a closed
subgroup scheme `j : H ⟶ G` vanishes is the image of a point of `H`. -/
theorem exists_comp_eq_of_evaluation_eq_zero (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (B : Type u) [CommRing B] [Algebra k B] (x : G.affinePoints (CommAlgCat.of k B))
    (hx : ∀ a : Γ(G.X.left, ⊤), j.hom.hom.left.appTop a = 0 →
      G.affinePointEvaluation (CommAlgCat.of k B) x a = 0) :
    ∃ y : H.affinePoints (CommAlgCat.of k B), y ≫ j.hom.hom = x := by
  let π := affineCoordinatePullback k j.hom.hom
  have hπ : Function.Surjective π :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine j.hom.hom.left).2
  let φ := (affineSchemePointEquiv k G.X B x).toAlgHom
  have hφ (a : AffineCoordinateRing k G.X) :
      φ a = G.affinePointEvaluation (CommAlgCat.of k B) x a :=
    affineSchemePointEquiv_evaluation G (CommAlgCat.of k B) x a
  have hker : ∀ a ∈ RingHom.ker π, φ a = 0 := by
    intro a ha
    rw [hφ]
    exact hx a ha
  let ψ : AffineCoordinateRing k H.X →ₐ[k] B :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) φ hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hψ (a : AffineCoordinateRing k G.X) : ψ (π a) = φ a := by
    have he : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a) =
        Ideal.Quotient.mk (RingHom.ker π) a :=
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm_apply_eq.mpr rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker π) φ hker)
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a)) = φ a
    rw [he]
    rfl
  let y : H.affinePoints (CommAlgCat.of k B) :=
    (affineSchemePointEquiv k H.X (CommAlgCat.of k B)).symm (AlgPoint.ofAlgHom ψ)
  refine ⟨y, ?_⟩
  apply G.affinePointEvaluation_injective (CommAlgCat.of k B)
  funext a
  change G.affinePointEvaluation (CommAlgCat.of k B) (y ≫ j.hom.hom) a =
    G.affinePointEvaluation (CommAlgCat.of k B) x a
  rw [affinePointEvaluation_postcomp]
  calc H.affinePointEvaluation (CommAlgCat.of k B) y (j.hom.hom.left.appTop a)
      = affineSchemePointEquiv k H.X (CommAlgCat.of k B) y (π a) :=
        (affineSchemePointEquiv_evaluation H (CommAlgCat.of k B) y (π a)).symm
    _ = ψ (π a) := by
        simp only [y, Equiv.apply_symm_apply]
        rfl
    _ = φ a := hψ a
    _ = G.affinePointEvaluation (CommAlgCat.of k B) x a := hφ a

end Langlands.GroupScheme
