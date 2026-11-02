import Langlands.GroupScheme.GeneralLinear
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# General linear point topology comparisons
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

namespace GeneralLinear

open Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n]
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

local instance : IsAffine (groupScheme n (CommRingCat.of R)).X.left :=
  isAffine_groupScheme n (CommRingCat.of R)

theorem continuous_point :
    Continuous (X := AlgPoint R (CoordinateRing n R) S)
      (Y := GL n S) (fun f => point f.toAlgHom) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_pi fun i => continuous_pi fun j =>
      AlgPoint.continuous_eval (quotient n R (MvPolynomial.X (.entry i j)))
  · exact continuous_pi fun i => continuous_pi fun j =>
      AlgPoint.continuous_eval (quotient n R (MvPolynomial.X (.inverseEntry i j)))

theorem continuous_classify [IsTopologicalRing S] :
    Continuous (X := GL n S) (Y := AlgPoint R (CoordinateRing n R) S)
      (fun g => AlgPoint.ofAlgHom (classify g)) := by
  apply (AlgPoint.continuous_iff _).mpr
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Continuous (fun g : GL n S => MvPolynomial.aeval (values g) p)
  have hv : Continuous (fun g : GL n S => values g) := by
    apply continuous_pi
    intro v
    cases v with
    | entry i j =>
        exact (continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i)
    | inverseEntry i j =>
        exact (continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_inv i)
  have hp : Continuous (fun x : Coordinate n → S =>
      MvPolynomial.aeval (R := R) x p) := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] using
      (MvPolynomial.continuous_eval (p.map (algebraMap R S)))
  exact hp.comp hv

/-- Evaluation points of the general linear coordinate algebra are matrices
with the existing matrix-unit topology. -/
def algPointHomeomorph [IsTopologicalRing S] :
    AlgPoint R (CoordinateRing n R) S ≃ₜ GL n S where
  toEquiv := AlgPoint.algHomEquiv.trans homEquiv
  continuous_toFun := continuous_point n R S
  continuous_invFun := continuous_classify n R S

/-- The existing topology on actual general linear scheme points agrees
with the existing topology on matrix units. -/
def schemePointHomeomorph [IsTopologicalRing S] :
    RingPoint R (groupScheme n (CommRingCat.of R)).X S ≃ₜ GL n S :=
  ((spectrumRingPointHomeomorph R S (CoordinateRing n R)).trans
    (specPointHomeomorph R (CoordinateRing n R) S)).trans
      (algPointHomeomorph n R S)

theorem schemePointHomeomorph_eq_point [IsTopologicalRing S]
    (p : RingPoint R (groupScheme n (CommRingCat.of R)).X S) :
    schemePointHomeomorph n R S p =
      point (affineRingPointEquiv R (CoordinateRing n R) S p) := by
  apply congrArg point
  change Spec.homEquivAlgHom _ =
    Spec.homEquivAlgHom ((ringPointEquiv R (ringTest R (CoordinateRing n R)) S) p)
  apply congrArg Spec.homEquivAlgHom
  apply Subtype.ext
  exact spectrumRingPointHomeomorph_apply R S (CoordinateRing n R) p

@[simp] theorem schemePointHomeomorph_apply [IsTopologicalRing S]
    (p : RingPoint R (groupScheme n (CommRingCat.of R)).X S) :
    schemePointHomeomorph n R S p =
      affinePointsEquiv n (CommRingCat.of R) (CommAlgCat.of R S) p := by
  refine (schemePointHomeomorph_eq_point n R S p).trans ?_
  obtain ⟨f, rfl⟩ :=
    (affineRingPointEquiv R (CoordinateRing n R) S).symm.surjective p
  rw [Equiv.apply_symm_apply]
  change point f =
    affinePointsEquiv n (CommRingCat.of R) (CommAlgCat.of R S)
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)
  exact (affinePointsEquiv_map (n := n) (R := CommRingCat.of R) (CommAlgCat.of R S)
    (CommAlgCat.ofHom f)).symm

end GeneralLinear

end Langlands.AlgebraicGeometry.PointTopology
