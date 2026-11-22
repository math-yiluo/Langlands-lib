import Langlands.Geometry.FormalGroup.NilpotentAlgebras
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # The affine formal spectrum on affine Nilp tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.FormalGroup

variable {R : Type u} [CommRing R] (π : R)

/-- An affine adic algebra over the base with the distinguished parameter
in its ideal of definition. -/
structure AdicAffineChart where
  algebra : CommAlgCat.{u} R
  ideal : Ideal algebra
  parameter_mem : algebraMap R algebra π ∈ ideal
  complete : IsAdicComplete ideal algebra

namespace AdicAffineChart

variable {π} (C : AdicAffineChart π)

/-- The quotient by the `(n+1)`-st power of the ideal of definition, as a Nilp test. -/
def quotientTest (n : ℕ) : Nilp.{u, u} R π :=
  Nilp.of R π (C.algebra ⧸ C.ideal ^ (n + 1)) (by
    refine ⟨n + 1, ?_⟩
    change (Ideal.Quotient.mk (C.ideal ^ (n + 1)) (algebraMap R C.algebra π)) ^ (n + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow C.parameter_mem (n + 1))

/-- The actual algebra reduction from a thicker to a thinner quotient. -/
def quotientReduction {m n : ℕ} (i : m ⟶ n) : C.quotientTest n ⟶ C.quotientTest m :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom i)))))

@[simp] theorem quotientReduction_id (n : ℕ) :
    C.quotientReduction (𝟙 n) = 𝟙 (C.quotientTest n) := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  exact Ideal.Quotient.factorₐ_refl _

@[simp] theorem quotientReduction_comp {l m n : ℕ} (i : l ⟶ m) (j : m ⟶ n) :
    C.quotientReduction (i ≫ j) = C.quotientReduction j ≫ C.quotientReduction i := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  exact (Ideal.Quotient.factorₐ_comp R _ _).symm

/-- The covariant point functors of the actual quotient algebras, with
transition maps induced by ordinary scheme closed immersions. -/
def quotientPointDiagram : ℕ ⥤ Nilp.{u, u} R π ⥤ Type u where
  obj n := coyoneda.obj (op (C.quotientTest n))
  map i := coyoneda.map (C.quotientReduction i).op
  map_id n := by
    rw [quotientReduction_id, op_id]
    exact coyoneda.map_id _
  map_comp i j := by
    rw [quotientReduction_comp, op_comp, Functor.map_comp]

/-- The affine formal spectrum is the colimit of the point functors of
its actual ordinary quotient schemes. -/
def nilpPointsFunctor : Nilp.{u, u} R π ⥤ Type u :=
  colimit C.quotientPointDiagram

/-- The point map from each actual quotient into the affine formal spectrum. -/
def quotientPointInclusion (n : ℕ) :
    coyoneda.obj (op (C.quotientTest n)) ⟶ C.nilpPointsFunctor :=
  colimit.ι C.quotientPointDiagram n

@[reassoc] theorem quotientPointInclusion_compatible {m n : ℕ} (i : m ⟶ n) :
    coyoneda.map (C.quotientReduction i).op ≫ C.quotientPointInclusion n =
      C.quotientPointInclusion m :=
  colimit.w C.quotientPointDiagram i

end AdicAffineChart
end Langlands.FormalGroup
