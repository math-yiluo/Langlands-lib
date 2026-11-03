import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyComparisons
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# The actual origin of the affine line
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- The origin is the actual relative spectrum morphism induced by evaluation
of the one coordinate at zero. -/
def affineLineOrigin :
    ringTest R R ⟶ ringTest R (MvPolynomial Unit R) :=
  ringTestMap R (MvPolynomial.aeval (fun _ : Unit => (0 : R)))

instance affineLineOrigin_isClosedImmersion :
    IsClosedImmersion (affineLineOrigin R).left := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  exact ⟨MvPolynomial.C r, MvPolynomial.aeval_C _ r⟩

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Evaluation of the coordinate identifies actual relative affine-line points
with the value algebra. The inverse is the actual polynomial evaluation point. -/
def affineLinePointEquiv :
    RingPoint R (ringTest R (MvPolynomial Unit R)) S ≃ S where
  toFun p := spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) p (MvPolynomial.X ())
  invFun s := (spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)).symm
    (AlgPoint.ofAlgHom (MvPolynomial.aeval (fun _ : Unit => s)))
  left_inv p := by
    apply (spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)).injective
    rw [Equiv.apply_symm_apply]
    apply AlgPoint.algHomEquiv.injective
    apply MvPolynomial.algHom_ext
    intro i
    cases i
    exact MvPolynomial.aeval_X _ _
  right_inv s := by
    change spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)
      ((spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)).symm
        (AlgPoint.ofAlgHom (MvPolynomial.aeval (fun _ : Unit => s))))
          (MvPolynomial.X ()) = s
    rw [Equiv.apply_symm_apply]
    exact MvPolynomial.aeval_X _ _

@[simp] theorem affineLinePointEquiv_apply
    (p : RingPoint R (ringTest R (MvPolynomial Unit R)) S) :
    affineLinePointEquiv R S p =
      spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) p (MvPolynomial.X ()) := rfl

/-- The actual zero section sends every relative base point to coordinate zero. -/
@[simp] theorem affineLinePointEquiv_origin
    (p : RingPoint R (ringTest R R) S) :
    affineLinePointEquiv R S (p ≫ affineLineOrigin R) = 0 := by
  change spectrumAlgebraPointEquiv R S (MvPolynomial Unit R)
    (p ≫ ringTestMap R (MvPolynomial.aeval (fun _ : Unit => (0 : R))))
      (MvPolynomial.X ()) = 0
  rw [spectrumAlgebraPointEquiv_natural]
  change spectrumAlgebraPointEquiv R S R p
    (MvPolynomial.aeval (fun _ : Unit => (0 : R)) (MvPolynomial.X ())) = 0
  rw [MvPolynomial.aeval_X]
  exact map_zero (spectrumAlgebraPointEquiv R S R p).toAlgHom

/-- The point image of the actual origin is exactly the zero-coordinate locus,
without any topology, nontriviality or faithfulness assumption. -/
theorem range_affineLineOrigin_points :
    Set.range (fun p : RingPoint R (ringTest R R) S => p ≫ affineLineOrigin R) =
      affineLinePointEquiv R S ⁻¹' ({0} : Set S) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact affineLinePointEquiv_origin R S p
  · intro hq
    refine ⟨ringTestMap R (Algebra.ofId R S), ?_⟩
    apply (affineLinePointEquiv R S).injective
    exact (affineLinePointEquiv_origin R S _).trans hq.symm

/-- The independently defined global-section evaluation topology makes the
coordinate equivalence a homeomorphism onto the given value-ring topology. -/
def affineLinePointHomeomorph [TopologicalSpace S] [IsTopologicalRing S] :
    RingPoint R (ringTest R (MvPolynomial Unit R)) S ≃ₜ S :=
  ((spectrumAlgebraPointHomeomorph R S (MvPolynomial Unit R)).trans
    (AlgPoint.polynomialPointHomeomorph (R := R) (S := S) Unit)).trans
      (Homeomorph.funUnique Unit S)

@[simp] theorem affineLinePointHomeomorph_apply
    [TopologicalSpace S] [IsTopologicalRing S]
    (p : RingPoint R (ringTest R (MvPolynomial Unit R)) S) :
    affineLinePointHomeomorph R S p = affineLinePointEquiv R S p := rfl

end Langlands.AlgebraicGeometry.PointTopology
