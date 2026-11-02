import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Topology families and the polynomial coproduct of affine lines
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Topologies on the actual algebra-map points of every finite-type coordinate algebra. -/
def AffinePointTopologyFamily :=
  (A : CommAlgCat.{u} R) → [Algebra.FiniteType R A] →
    TopologicalSpace (AlgPoint R A S)

/-- The actual evaluation topologies form such a family. -/
def evaluationAffineTopologyFamily [TopologicalSpace S] : AffinePointTopologyFamily R S :=
  fun _ _ => inferInstance

variable {S}

/-- The multivariate polynomial algebra is the coproduct of one-variable
polynomial algebras, with the actual variable inclusions. -/
def polynomialLineCofan (ι : Type u) :
    Cofan (fun _ : ι => CommAlgCat.of R (MvPolynomial Unit R)) :=
  Cofan.mk (CommAlgCat.of R (MvPolynomial ι R))
    (fun i => CommAlgCat.ofHom (MvPolynomial.rename (fun _ : Unit => i)))

/-- The universal map evaluates the variable indexed by `i` at the image of
the variable of the `i`th one-variable polynomial algebra. -/
def polynomialLineCofanIsColimit (ι : Type u) :
    IsColimit (polynomialLineCofan R ι) := by
  refine Cofan.IsColimit.mk _
    (fun s => CommAlgCat.ofHom
      (MvPolynomial.aeval (fun i => (s.inj i).hom (MvPolynomial.X ())))) ?_ ?_
  · intro s i
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro j
    cases j
    simp [polynomialLineCofan]
  · intro s m hm
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have h := congrArg (fun f => f.hom (MvPolynomial.X ())) (hm i)
    change m.hom ((MvPolynomial.rename (fun _ : Unit => i)) (MvPolynomial.X ())) =
      (s.inj i).hom (MvPolynomial.X ()) at h
    change m.hom (MvPolynomial.X i) =
      (MvPolynomial.aeval (fun j => (s.inj j).hom (MvPolynomial.X ()))) (MvPolynomial.X i)
    simpa using h

end Langlands.AlgebraicGeometry.PointTopology
