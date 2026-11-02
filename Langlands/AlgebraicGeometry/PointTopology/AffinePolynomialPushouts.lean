import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# Adjoining a polynomial variable as an actual algebra pushout
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Adjoining one variable is the pushout of a polynomial algebra and a
polynomial line over the initial `R`-algebra. -/
def polynomialOptionPushout (ι : Type u) :
    PushoutCocone
      (CommAlgCat.ofHom (Algebra.ofId R (MvPolynomial ι R)))
      (CommAlgCat.ofHom (Algebra.ofId R (MvPolynomial Unit R))) :=
  PushoutCocone.mk
    (CommAlgCat.ofHom (MvPolynomial.rename (Option.some : ι → Option ι)))
    (CommAlgCat.ofHom (MvPolynomial.rename (fun _ : Unit => (none : Option ι))))
    (by
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _)

/-- The universal map evaluates the old variables in the first factor and
the new variable in the polynomial-line factor. -/
def polynomialOptionPushoutIsColimit (ι : Type u) :
    IsColimit (polynomialOptionPushout R ι) := by
  refine PushoutCocone.IsColimit.mk _
    (fun s => CommAlgCat.ofHom (MvPolynomial.aeval
      (fun i => Option.elim i (s.inr.hom (MvPolynomial.X ()))
        (fun j => s.inl.hom (MvPolynomial.X j))))) ?_ ?_ ?_
  · intro s
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp
  · intro s
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro i
    cases i
    simp
  · intro s m hl hr
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
        have h := congrArg (fun f => f.hom (MvPolynomial.X ())) hr
        simpa using h
    | some i =>
        have h := congrArg (fun f => f.hom (MvPolynomial.X i)) hl
        simpa using h

end Langlands.AlgebraicGeometry.PointTopology
