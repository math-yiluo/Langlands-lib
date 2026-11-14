import Langlands.GroupScheme.Derived.BaseChangeElementary
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.RelativeCommutativity

/-! # Commutators in the kernel of a relative-torus quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

variable {S S' : Scheme.{u}} {G D Q : GroupScheme S}

/-- The specified full kernel of a quotient with commutative target contains
every commutator on every test scheme. -/
theorem containsCommutators_of_isCommMonObj
    {F : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient F q) [IsCommMonObj Q.X] :
    F.ContainsCommutators := by
  rw [← hq.2.2.2]
  exact SubgroupFunctor.containsCommutators_range_kernelι q

/-- If a supplied subgroup has a relative-torus quotient, its actual
base-changed inclusion contains all commutators after any change of base. -/
theorem containsCommutators_range_baseChange_of_isTorus
    {d : D ⟶ G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hQ : RelativeTorus.IsTorus Q) (b : S' ⟶ S) :
    (SubgroupFunctor.range ((GroupScheme.baseChange b).map d)).ContainsCommutators := by
  let : IsCommMonObj Q.X := hQ.isCommMonObj
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hq.containsCommutators_of_isCommMonObj.baseChange b

end RelativeRoot.IsFppfQuotient

/-- A relative-torus quotient forces commutator containment in the actual
subgroup range after every base change, over any base scheme. -/
def TorusQuotientCommutatorsStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (G D Q : GroupScheme S) (d : D ⟶ G) (q : G ⟶ Q),
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
      RelativeTorus.IsTorus Q → ∀ b : S' ⟶ S,
        (SubgroupFunctor.range ((GroupScheme.baseChange b).map d)).ContainsCommutators

theorem torusQuotientCommutators : TorusQuotientCommutatorsStatement.{u} :=
  fun _ _ _ _ _ _ _ hq hQ b =>
    hq.containsCommutators_range_baseChange_of_isTorus hQ b

end Langlands.GroupScheme
