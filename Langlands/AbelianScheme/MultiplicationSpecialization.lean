import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.MultiplicationIsogenyStatement

/-! # Integer multiplication on bundled abelian schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}}

/-- Integer multiplication in the actual additive group of endomorphisms. -/
def multiplication (A : AbelianScheme S) (n : ℤ) : A ⟶ A :=
  n • 𝟙 A

/-- Forgetting additive notation gives the published group-scheme multiplication. -/
@[simp] theorem groupHom_multiplication (A : AbelianScheme S) (n : ℤ) :
    groupHom (multiplication A n) = GroupScheme.multiplication A.toGrp n := rfl

/-- The underlying scheme map is the published multiplication map. -/
@[simp] theorem hom_multiplication (A : AbelianScheme S) (n : ℤ) :
    hom (multiplication A n) = (GroupScheme.multiplication A.toGrp n).hom.hom.left := rfl

/-- The action on sections is integer multiplication in their pointwise group. -/
theorem points_multiplication (A : AbelianScheme S) (n : ℤ)
    (U : Over S) (x : U ⟶ A.X) :
    x ≫ (groupHom (multiplication A n)).hom.hom = x ^ n :=
  GroupScheme.points_multiplication A.toGrp n U x

/-- Bundled multiplication commutes with arbitrary base change. -/
theorem multiplication_baseChange (f : T ⟶ S) (A : AbelianScheme S) (n : ℤ) :
    (baseChange f).map (multiplication A n) =
      multiplication ((baseChange f).obj A) n := by
  change Additive.ofMul ((Over.pullback f).mapGrp.map
    (GroupScheme.multiplication A.toGrp n)) =
      Additive.ofMul (GroupScheme.multiplication ((Over.pullback f).mapGrp.obj A.toGrp) n)
  exact congrArg Additive.ofMul (GroupScheme.multiplication_baseChange f A.toGrp n)

/-- Specialization of the generic geometric target, conditional on its proof.
This lemma does not assert that the target has been proved. -/
theorem isIsogeny_multiplication_of_statement
    (h : GroupScheme.MultiplicationIsogenyStatement.{u})
    (A : AbelianScheme S) (n : ℤ) (hn : n ≠ 0) :
    GroupScheme.IsIsogeny (groupHom (multiplication A n)) :=
  h S A.toGrp A.smooth A.proper A.geometricallyConnected n hn

end Langlands.AbelianScheme
